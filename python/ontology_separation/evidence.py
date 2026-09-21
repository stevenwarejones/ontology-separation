"""Shared rendering contract for proof-bearing claims. Parsing is not proof verification."""
from fractions import Fraction
import re

KINDS = {'exact', 'bound', 'realizedBound', 'witness', 'exclusion', 'theorem'}
NUMERIC = {'exact', 'bound', 'realizedBound', 'witness'}
LABELS = {'exact': 'Exact prediction', 'bound': 'Conditional bound · existence not certified',
          'realizedBound': 'Bound + satisfying model', 'witness': 'Realized witness',
          'exclusion': 'Mathematical exclusion', 'theorem': 'Theorem · see full assumptions'}


def validate_claim(claim: dict) -> None:
    if not isinstance(claim, dict) or claim.get('kind') not in KINDS:
        raise ValueError('Unknown proof-bearing claim kind')
    if not isinstance(claim.get('statement'), str) or not claim['statement'].strip():
        raise ValueError('A claim needs its actual Lean proposition')
    quantity = claim.get('quantity')
    if claim['kind'] not in NUMERIC:
        if quantity is not None:
            raise ValueError('A theorem or exclusion cannot acquire a numerical value without an equality proof')
        return
    if not isinstance(quantity, dict):
        raise ValueError('A numerical claim needs its proved rational quantity')
    n, d = quantity.get('numerator'), quantity.get('denominator')
    if (not isinstance(n, str) or not re.fullmatch(r'-?[0-9]+', n)
            or not isinstance(d, str) or not re.fullmatch(r'[0-9]+', d) or int(d) <= 0):
        raise ValueError('Claims require integer strings and a positive denominator')


def result_text(claim: dict) -> str:
    validate_claim(claim)
    if claim['kind'] in NUMERIC:
        q = claim['quantity']
        value = str(Fraction(int(q['numerator']), int(q['denominator'])))
        return ('≤ ' if claim['kind'] in {'bound', 'realizedBound'} else '') + value
    # A symbolic theorem's full proposition is the result, not independently maintained prose.
    return claim['statement']


def evidence_label(claim: dict | None) -> str:
    return LABELS[claim['kind']] if claim else 'No interpretation supplied'
