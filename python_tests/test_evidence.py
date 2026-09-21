from copy import deepcopy
import unittest
from ontology_separation import Report, load_report
from ontology_separation.evidence import validate_claim, result_text, evidence_label

class EvidenceTests(unittest.TestCase):
    def test_old_catalog_schema_is_rejected(self):
        data = deepcopy(load_report().data)
        data['schema_version'] = 2
        with self.assertRaisesRegex(ValueError, 'schema_version=3'):
            Report(data)

    def test_every_cell_uses_the_common_contract(self):
        cells = load_report().compare()
        self.assertEqual(len(cells), 98)
        self.assertEqual(sum(c['applicability'] == 'additional' for c in cells), 74)
        self.assertEqual(sum(c['status'] == 'realizedBound' for c in cells), 5)
        for cell in cells:
            validate_claim(cell['claim'])
            self.assertEqual(cell['status'], cell['claim']['kind'])
            self.assertEqual(cell['result'], result_text(cell['claim']))
        exclusions = [x for c in cells for x in c['supporting'] if x['kind'] == 'exclusion']
        self.assertGreaterEqual(len(exclusions), 2)

    def test_labels_or_values_cannot_drift_from_claim_metadata(self):
        for field, fake in [('result', '999'), ('status', 'exclusion')]:
            data = deepcopy(load_report().data)
            data['cells'][0][field] = fake
            with self.assertRaisesRegex(ValueError, 'does not match'):
                Report(data)

    def test_theorem_cannot_claim_a_numeric_value(self):
        claim = dict(kind='theorem', statement='True', quantity=dict(numerator='100', denominator='1'))
        with self.assertRaisesRegex(ValueError, 'without an equality proof'):
            validate_claim(claim)

    def test_bound_is_distinct_from_nonempty_class(self):
        claim = dict(kind='bound', statement='∀ x, P x → f x ≤ 2', quantity=dict(numerator='2', denominator='1'))
        self.assertIn('existence not certified', evidence_label(claim))
        self.assertEqual(result_text(claim), '≤ 2')
        realized = dict(claim, kind='realizedBound', statement='(∀ x, P x → f x ≤ 2) ∧ ∃ x, P x')
        self.assertEqual(evidence_label(realized), 'Bound + satisfying model')

    def test_missing_proposition_or_quantity_fails(self):
        for claim in [dict(kind='exact', statement='', quantity=dict(numerator='1', denominator='1')),
                      dict(kind='exact', statement='f x = 1', quantity=None)]:
            with self.assertRaises(ValueError): validate_claim(claim)
