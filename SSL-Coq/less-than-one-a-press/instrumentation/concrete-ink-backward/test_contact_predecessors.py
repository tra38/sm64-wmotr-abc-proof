import copy
import json
import math
from pathlib import Path
import tempfile
import unittest

from contact_predecessors import contact_templates
from search import previous_templates, DIALOG, number, Input
from reverse_scattershot import continuous, initial_aux, proposal, advance_aux, open_store
from test_compact_scattershot import FakeBackend, scatter_signature, scatter_row


class ContactTests(unittest.TestCase):
    def test_finite_unique_menu_contains_contact_horizontal_and_message_moves(self):
        target = copy.deepcopy(scatter_signature()['jobOrder'][0]['patch'])
        moves = list(contact_templates(target, previous_templates(target)))
        self.assertEqual(len({json.dumps(m.patch, sort_keys=True) for m in moves}), len(moves))
        self.assertTrue(any(m.patch['collision'] != target['collision'] for m in moves))
        self.assertTrue(any(m.name.startswith('horizontal') and
                            m.patch['movement'][::2] != target['movement'][::2] for m in moves))
        self.assertTrue(any(m.name.startswith('interaction') and m.patch['action'] == DIALOG and
                            m.patch['actionState'] == 23 for m in moves))
        for m in moves:
            for field in ('movement', 'collision', 'display'):
                self.assertTrue(all(math.isfinite(number(x)) and abs(number(x)) < 8192
                                    for x in m.patch[field]))

    def test_parent_mismatch_replays_actual_suffix_once_and_returns_actual_checkpoints(self):
        b = FakeBackend(); context = b.capture()
        b.f = 1; wrong = b.observe(); wrong['timer'] = 999
        b.f = 2; end = b.observe(); b.f = 0
        target = dict(movement=[0, 0, 0], collision=b.endpoint['collision'], display=b.endpoint['display'])
        report, earlier = continuous(b, context, {}, [Input(), Input()], [wrong],
                                     {'original': target}, {'original': end}, 'released', exact_parent=False)
        self.assertEqual(report['status'], 'accepted-projection')
        self.assertEqual(report['parentComparisons'][0]['differences']['timer']['expected'], 999)
        self.assertEqual(report['observations'][0]['timer'], 1)
        self.assertIsNotNone(earlier)
        self.assertEqual(b.ops, ['restore', 'patch'] + ['advance'] * 25)

    def test_saved_parent_cannot_supply_wrong_prefix_records(self):
        b = FakeBackend(); context = b.capture()
        b.f = 1; wrong = b.observe(); wrong['display'] = [99, 99, 99]
        b.f = 2; end = b.observe(); b.f = 0
        target = dict(movement=[0, 0, 0], collision=b.endpoint['collision'], display=wrong['display'])
        report, earlier = continuous(b, context, {}, [Input(), Input()], [wrong],
                                     {'original': target}, {'original': end}, 'released', exact_parent=False)
        self.assertEqual(report['status'], 'rejected-event')
        self.assertFalse(report['targets']['original']['conditionalPrefixMatches'])
        self.assertIsNone(earlier)

    def test_expanded_seeded_schedule_resumes_without_skipping_trials(self):
        sig = scatter_signature(); sig['predecessorMenu'] = 'contact-approach'
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / 'ledger'
            with open_store(root, sig, chunk_records=3) as s:
                for i in range(9): s.append(scatter_row(s.state['aux'], sig, i))
                s.commit(); expected = copy.deepcopy(s.state)
            with open_store(root, sig, True, chunk_records=3) as s:
                self.assertEqual(s.state, expected)
                for i in range(9, 18): s.append(scatter_row(s.state['aux'], sig, i))
                s.commit(); expected = copy.deepcopy(s.state)
            with open_store(root, sig, True, chunk_records=3) as s:
                self.assertEqual(s.state, expected)
                self.assertEqual([r['case'] for r in s.records()], list(range(18)))


if __name__ == '__main__': unittest.main()
