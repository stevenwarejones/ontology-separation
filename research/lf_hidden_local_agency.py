#!/usr/bin/env python3
"""Exploratory LPs for unread friend records and relaxed Local Agency.

This file is intentionally *not* in the trusted Lean proof path.  It reproduces
the numerical observations documented in PR #46:

  observed early outcomes:
      zero-TV score ceiling = 6
      min TV at score 8     = 1/4

  unread reversible friend records + exact readout:
      zero-TV score ceiling = 22/3
      min TV at score 8     = 1/8

For the full LF table it also evaluates the record-revealed TV relaxation at
specified quantum measurement angles.  The repository's rational angles give
63/625, while a simple pi/8-grid choice reaches

    (sqrt(2) - 1) / 2 ~= 0.2071067812.

The latter is a certified *target angle value only if/when a Lean certificate is
added*.  This script does not prove that no other angles do better.

Requirements: numpy, scipy.
"""

from __future__ import annotations

import argparse
import math
from typing import Iterable

import numpy as np
from scipy.optimize import differential_evolution, linprog


def response(table: int, setting: int) -> int:
    return (table >> setting) & 1


def signbit(n: int) -> int:
    return 1 if n % 2 == 0 else -1


ATOMS = []
for j in range(256):
    ATOMS.append((
        j // 128,
        (j // 64) % 2,
        (j // 32) % 2,
        (j // 16) % 2,
        (j // 4) % 4,
        j % 4,
    ))


def score_coeff(j: int) -> int:
    x, w, a, d, bt, ct = ATOMS[j]
    if x == 0 and w == 1:
        return (
            signbit(a + response(bt, 0))
            + signbit(a + response(bt, 1))
            + 2 * signbit(a + response(ct, 1) + d)
        )
    if x == 1 and w == 0:
        return (
            signbit(a + response(bt, 0) + d)
            - signbit(a + response(bt, 1) + d)
            + 2 * signbit(response(ct, 0) + d)
        )
    return 0


SCORE = np.array([score_coeff(j) for j in range(256)], dtype=float)
READOUT_CONSISTENT = {
    j for j, (_x, _w, a, d, bt, ct) in enumerate(ATOMS)
    if response(bt, 0) == a and response(ct, 0) == d
}


def _normalization_rows(n: int) -> tuple[list[np.ndarray], list[float]]:
    rows, rhs = [], []
    for x in (0, 1):
        for w in (0, 1):
            row = np.zeros(n)
            for j, (xx, ww, *_rest) in enumerate(ATOMS):
                if xx == x and ww == w:
                    row[j] = 1
            rows.append(row)
            rhs.append(1.0)
    return rows, rhs


def solve_score_lp(*, unread_records: bool, target_score: float | None = None,
                   delta_fixed: float | None = None):
    """Solve the score surrogate with either observed or unread early records."""
    cells = 4 if unread_records else 8
    nslack = 16 * cells
    delta = 256 + nslack
    n = delta + 1

    objective = np.zeros(n)
    if target_score is None:
        objective[:256] = -SCORE
    else:
        objective[delta] = 1.0

    aeq, beq = _normalization_rows(n)
    if target_score is not None:
        row = np.zeros(n)
        row[:256] = SCORE
        aeq.append(row)
        beq.append(float(target_score))

    aub, bub = [], []
    slack = 256

    def add_context(coeffs: Iterable[np.ndarray]) -> None:
        nonlocal slack
        used = []
        for coeff in coeffs:
            u = slack
            slack += 1
            used.append(u)
            for sgn in (1.0, -1.0):
                row = sgn * coeff.copy()
                row[u] -= 1
                aub.append(row)
                bub.append(0.0)
        row = np.zeros(n)
        for u in used:
            row[u] = 0.5
        row[delta] -= 1
        aub.append(row)
        bub.append(0.0)

    # x flip
    for w in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                coeffs = []
                if unread_records:
                    recipients = [(b, c) for b in (0, 1) for c in (0, 1)]
                    for b, c in recipients:
                        coeff = np.zeros(n)
                        for j, (xj, wj, _a, _d, bt, ct) in enumerate(ATOMS):
                            if wj == w and response(bt, y) == b and response(ct, z) == c:
                                coeff[j] += 1 if xj == 0 else -1
                        coeffs.append(coeff)
                else:
                    recipients = [(b, c, d) for b in (0, 1) for c in (0, 1) for d in (0, 1)]
                    for b, c, d in recipients:
                        coeff = np.zeros(n)
                        for j, (xj, wj, _a, dj, bt, ct) in enumerate(ATOMS):
                            if (wj == w and dj == d and response(bt, y) == b
                                    and response(ct, z) == c):
                                coeff[j] += 1 if xj == 0 else -1
                        coeffs.append(coeff)
                add_context(coeffs)

    # w flip
    for x in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                coeffs = []
                if unread_records:
                    recipients = [(b, c) for b in (0, 1) for c in (0, 1)]
                    for b, c in recipients:
                        coeff = np.zeros(n)
                        for j, (xj, wj, _a, _d, bt, ct) in enumerate(ATOMS):
                            if xj == x and response(bt, y) == b and response(ct, z) == c:
                                coeff[j] += 1 if wj == 0 else -1
                        coeffs.append(coeff)
                else:
                    recipients = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]
                    for a, b, c in recipients:
                        coeff = np.zeros(n)
                        for j, (xj, wj, aj, _d, bt, ct) in enumerate(ATOMS):
                            if (xj == x and aj == a and response(bt, y) == b
                                    and response(ct, z) == c):
                                coeff[j] += 1 if wj == 0 else -1
                        coeffs.append(coeff)
                add_context(coeffs)

    bounds = [(0.0, None)] * n
    if unread_records:
        for j in range(256):
            if j not in READOUT_CONSISTENT:
                bounds[j] = (0.0, 0.0)
    if delta_fixed is not None:
        bounds[delta] = (float(delta_fixed), float(delta_fixed))

    return linprog(
        objective,
        A_ub=np.asarray(aub), b_ub=np.asarray(bub),
        A_eq=np.asarray(aeq), b_eq=np.asarray(beq),
        bounds=bounds, method="highs",
    )


def singlet_probs(a_angles: list[float], b_angles: list[float]) -> np.ndarray:
    p = np.zeros((3, 3, 2, 2))
    for x, ta in enumerate(a_angles):
        va = [(math.cos(ta), math.sin(ta)), (-math.sin(ta), math.cos(ta))]
        for y, tb in enumerate(b_angles):
            vb = [(math.cos(tb), math.sin(tb)), (-math.sin(tb), math.cos(tb))]
            for a in (0, 1):
                for b in (0, 1):
                    det = va[a][0] * vb[b][1] - va[a][1] * vb[b][0]
                    p[x, y, a, b] = det * det / 2
    return p


def _qidx(x: int, y: int, r: int, a: int, b: int) -> int:
    return ((((x * 3 + y) * 4 + r) * 2 + a) * 2 + b)


ACOMPS = [(x, y, yp) for x in range(3) for y in range(3) for yp in range(y + 1, 3)]
BCOMPS = [(x, xp, y) for y in range(3) for x in range(3) for xp in range(x + 1, 3)]


def full_table_record_tv(a_angles: list[float], b_angles: list[float]) -> float:
    """Minimize the maximum record-revealed TV while matching all 36 public probabilities."""
    target = singlet_probs(a_angles, b_angles)
    nq = 3 * 3 * 4 * 2 * 2
    nslack = (len(ACOMPS) + len(BCOMPS)) * 8
    delta = nq + nslack
    n = delta + 1

    obj = np.zeros(n)
    obj[delta] = 1.0
    aeq, beq = [], []

    # exact public table
    for x in range(3):
        for y in range(3):
            for a in (0, 1):
                for b in (0, 1):
                    row = np.zeros(n)
                    for r in range(4):
                        row[_qidx(x, y, r, a, b)] = 1
                    aeq.append(row)
                    beq.append(target[x, y, a, b])

    # setting-independent friend-record distribution
    for x in range(3):
        for y in range(3):
            if x == 0 and y == 0:
                continue
            for r in range(4):
                row = np.zeros(n)
                for a in (0, 1):
                    for b in (0, 1):
                        row[_qidx(x, y, r, a, b)] += 1
                        row[_qidx(0, 0, r, a, b)] -= 1
                aeq.append(row)
                beq.append(0.0)

    aub, bub = [], []
    slack = nq

    def add_abs_context(differences: list[np.ndarray]) -> None:
        nonlocal slack
        used = []
        for diff in differences:
            u = slack
            slack += 1
            used.append(u)
            for sgn in (1.0, -1.0):
                row = sgn * diff.copy()
                row[u] -= 1
                aub.append(row)
                bub.append(0.0)
        row = np.zeros(n)
        for u in used:
            row[u] = 0.5
        row[delta] -= 1
        aub.append(row)
        bub.append(0.0)

    for x, y, yp in ACOMPS:
        differences = []
        for r in range(4):
            for a in (0, 1):
                row = np.zeros(n)
                for b in (0, 1):
                    row[_qidx(x, y, r, a, b)] += 1
                    row[_qidx(x, yp, r, a, b)] -= 1
                differences.append(row)
        add_abs_context(differences)

    for x, xp, y in BCOMPS:
        differences = []
        for r in range(4):
            for b in (0, 1):
                row = np.zeros(n)
                for a in (0, 1):
                    row[_qidx(x, y, r, a, b)] += 1
                    row[_qidx(xp, y, r, a, b)] -= 1
                differences.append(row)
        add_abs_context(differences)

    bounds = [(0.0, None)] * n

    # exact friend readout at x=0 / y=0
    for x in range(3):
        for y in range(3):
            for r in range(4):
                c, d = r // 2, r % 2
                for a in (0, 1):
                    for b in (0, 1):
                        if (x == 0 and a != c) or (y == 0 and b != d):
                            bounds[_qidx(x, y, r, a, b)] = (0.0, 0.0)

    result = linprog(
        obj,
        A_ub=np.asarray(aub), b_ub=np.asarray(bub),
        A_eq=np.asarray(aeq), b_eq=np.asarray(beq),
        bounds=bounds, method="highs",
    )
    if not result.success:
        raise RuntimeError(result.message)
    return float(result.fun)


def angle_search(seed: int = 1) -> tuple[float, np.ndarray]:
    """Numerical search only: no proof that this is the global angle optimum."""
    def objective(v: np.ndarray) -> float:
        try:
            return -full_table_record_tv([0.0, v[0], v[1]], [v[2], v[3], v[4]])
        except RuntimeError:
            return 1.0

    result = differential_evolution(
        objective,
        [(-math.pi / 2, math.pi / 2)] * 5,
        seed=seed, popsize=8, maxiter=40, polish=True,
    )
    return -float(result.fun), result.x


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--search", action="store_true",
                        help="run an additional numerical measurement-angle search")
    args = parser.parse_args()

    observed8 = solve_score_lp(unread_records=False, target_score=8)
    observed0 = solve_score_lp(unread_records=False, delta_fixed=0)
    unread8 = solve_score_lp(unread_records=True, target_score=8)
    unread0 = solve_score_lp(unread_records=True, delta_fixed=0)

    print("score surrogate")
    print(f"  observed: min TV at score 8 = {observed8.fun:.12g}")
    print(f"  observed: zero-TV score max = {-observed0.fun:.12g}")
    print(f"  unread+readout: min TV at score 8 = {unread8.fun:.12g}")
    print(f"  unread+readout: zero-TV score max = {-unread0.fun:.12g}")

    rational_a = [0.0, math.atan2(-4, 3), 0.0]
    rational_b = [math.atan2(-3, 4), 0.0, math.atan2(-8, 15)]
    rational = full_table_record_tv(rational_a, rational_b)

    # Simple exact-angle target:
    # A = [0, -pi/4, pi/4], B = [-3pi/8, pi/4, -pi/8].
    optimal_a = [0.0, -math.pi / 4, math.pi / 4]
    optimal_b = [-3 * math.pi / 8, math.pi / 4, -math.pi / 8]
    angle_target = full_table_record_tv(optimal_a, optimal_b)
    radical = (math.sqrt(2) - 1) / 2

    print("full LF table")
    print(f"  repository rational angles = {rational:.12g}  (63/625 = {63/625:.12g})")
    print(f"  pi/8-grid target angles    = {angle_target:.12g}")
    print(f"  (sqrt(2)-1)/2              = {radical:.12g}")
    print(f"  residual                   = {angle_target-radical:.3g}")

    if args.search:
        value, angles = angle_search()
        print("numerical angle search (not a proof of global optimality)")
        print(f"  best value = {value:.12g}")
        print(f"  [a1,a2,b0,b1,b2] = {angles}")


if __name__ == "__main__":
    main()
