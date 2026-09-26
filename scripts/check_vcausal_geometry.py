#!/usr/bin/env python3
"""Independent exact-rational geometry checks; no Lean evaluation or float inputs."""
from fractions import Fraction as Q
from itertools import product


def cone(p, q, v=Q(1), closed=False):
    dt, dx = q[0] - p[0], abs(q[1] - p[1])
    return dx <= dt if closed else dt > 0 and dx < v * dt


def lc4(layout, v):
    return (v > 1 and all(cone(layout[a], layout[b], v)
            for a in "AD" for b in "BC")
            and not cone(layout["B"], layout["C"], v)
            and not cone(layout["C"], layout["B"], v))


def apex(records):
    u, w = max(t + x for t, x in records), max(t - x for t, x in records)
    return (u + w) / 2, (u - w) / 2


def collectible(sender, records):
    q = apex(records)
    assert all(cone(r, q, closed=True) for r in records)
    return not cone(sender, q, closed=True)


def boost(p, beta):
    t, x = p
    return t - beta * x, x - beta * t


def frame_tests(beta, v, tau):
    edges = [(2*tau-1000*beta, 1000-2*tau*beta),
             (2*tau-11000*beta, 11000-2*tau*beta),
             (tau+11000*beta, -11000-tau*beta),
             (tau+1000*beta, -1000-tau*beta)]
    return v > 1 and all(dt > 0 and abs(dx) < v*dt for dt, dx in edges) and v*abs(beta) <= 1


def main():
    minimal = dict(zip("ADBC", [(Q(0), Q(-1)), (Q(11,20), Q(1)),
                               (Q(17,20), Q(-1,10)), (Q(17,20), Q(1,10))]))
    tau = Q(299792458, 10000000)
    restored = dict(zip("ADBC", [(Q(0), Q(-6000)), (tau, Q(6000)),
                                (2*tau, Q(-5000)), (2*tau, Q(5000))]))
    for layout, v in [(minimal, Q(4)), (restored, Q(10000))]:
        assert lc4(layout, v)
        for sender in "AD":
            assert collectible(layout[sender], [p for k, p in layout.items() if k != sender])
    margins = [minimal[s][0] + abs(x-minimal[s][1]) - Q(39,20)
               for s, x in [("A", Q(1)), ("D", Q(-1))]]
    assert margins == [Q(1,20), Q(3,5)]
    assert cone(minimal["B"], (Q(39,20), Q(1)), closed=True)
    assert Q(39,20)-minimal["B"][0] == abs(Q(1)-minimal["B"][1])
    for delays in product([Q(0), Q(1,100)], repeat=4):
        shifted = {p: (t+d, x) for (p, (t, x)), d in zip(minimal.items(), delays)}
        assert lc4(shifted, Q(4))
    threshold = Q(12000)/tau
    assert threshold == Q(60000000000,149896229)
    assert Q(400275,1000) < threshold < Q(400285,1000)
    assert not collectible((Q(0), Q(0)), [(Q(1), Q(-2)), (Q(1), Q(2))])
    assert cone((Q(0), Q(0)), (Q(1), Q(1)), closed=True)
    assert not cone((Q(0), Q(0)), (Q(1), Q(2)), Q(2))
    for beta, v in product([Q(-1,2), Q(-1,10000), Q(0), Q(1,10000), Q(1,2)],
                           [Q(2), Q(400), Q(401), Q(10000)]):
        mapped = {p: boost(event, beta) for p, event in restored.items()}
        assert lc4(mapped, v) == frame_tests(beta, v, tau)
        for s in "AD":
            assert collectible(mapped[s], [p for k,p in mapped.items() if k != s])
    print("Exact rational causal geometry: layouts, apexes, margins, boundaries, durations and frame tests passed")


if __name__ == "__main__":
    main()
