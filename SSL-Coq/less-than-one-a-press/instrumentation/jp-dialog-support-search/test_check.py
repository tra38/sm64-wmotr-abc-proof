"""Mutation tests for the boundaries that could turn a failed search into a claim."""
import copy
import unittest
from pathlib import Path
from check import check, records


class ReceiptChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = records(Path(__file__).with_name('example-trace.txt'))

    def changed(self, tag, field, value):
        rows = copy.deepcopy(self.receipt)
        next(r for name, r in rows if name == tag)[field] = value
        return rows

    def rejects(self, rows):
        with self.assertRaises(ValueError):
            check(rows)

    def test_recorded_trial(self):
        self.assertEqual(check(self.receipt)['updates'], '90')

    def test_no_supplied_gap(self):
        self.rejects(self.changed('START', 'display', '(-2200,1939,-1024)'))

    def test_initial_live_owner(self):
        self.rejects(self.changed('QUERY', 'owner', '00000000'))

    def test_dialog_must_finish(self):
        self.rejects(self.changed('LAST_DIALOG', 'state', '9'))

    def test_incomplete_depth(self):
        self.rejects([(t, r) for t, r in self.receipt if not (t == 'POLL' and r['step'] == '45')])

    def test_no_a(self):
        self.rejects(self.changed('INPUT', 'a', '1'))

    def test_policy_is_checked(self):
        self.rejects(self.changed('INPUT', 'x', '127'))

    def test_no_late_fixture(self):
        self.rejects(self.changed('RESULT', 'lateWrites', '1'))

    def test_sink_count(self):
        self.rejects(self.changed('RESULT', 'dialogSinks', '1'))

    def test_early_movement_is_real(self):
        start = next(r for t, r in self.receipt if t == 'RELEASE')
        self.rejects(self.changed('MOVED', 'pos', start['pos']))

    def test_early_movement_retains_display(self):
        self.rejects(self.changed('MOVED', 'display', '(0,0,0)'))

    def test_missing_query_not_counted_as_failure(self):
        self.rejects(self.changed('RESULT', 'missesBeforeReset', '1'))


if __name__ == '__main__':
    unittest.main()
