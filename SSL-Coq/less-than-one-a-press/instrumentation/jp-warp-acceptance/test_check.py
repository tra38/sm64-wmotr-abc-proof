import pathlib
import unittest
from check import validate

HERE = pathlib.Path(__file__).resolve().parent


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.receipt = (HERE / "expected-receipt.txt").read_text()
        self.route = (HERE / "expected-route.txt").read_text()

    def test_saved_receipt(self):
        sample = validate(self.receipt, self.route)[2]
        self.assertEqual(sample["state"], sample["collision"])
        self.assertEqual(sample["state"], sample["display"])

    def test_reject_wrong_checkpoint_and_bad_provenance(self):
        for old, new in (("arg=00040002", "arg=00040001"),
                         ("result=1,action", "result=0,action"),
                         ("area=1", "area=2"),
                         ("failures=0", "failures=1"),
                         ("originalTopSlot=803451f8", "originalTopSlot=8034bcd8"),
                         ("liveTopCount=0", "liveTopCount=1"),
                         ("display=", "omitted=")):
            with self.subTest(old=old), self.assertRaises((ValueError, KeyError)):
                validate(self.receipt.replace(old, new), self.route)
        for old, new in (("controllerAFrames=0", "controllerAFrames=1"),
                         ("inputPluginMemoryWrites=zero", "inputPluginMemoryWrites=setup"),
                         ("invariant=1", "invariant=0")):
            with self.subTest(old=old), self.assertRaises(ValueError):
                validate(self.receipt, self.route.replace(old, new))

    def test_missing_and_reordered_samples_fail(self):
        lines = self.receipt.splitlines()
        with self.assertRaises(ValueError):
            validate("\n".join(lines[1:]), self.route)
        lines[2], lines[3] = lines[3], lines[2]
        with self.assertRaises(ValueError):
            validate("\n".join(lines), self.route)

    def test_a_split_is_reported_not_filtered_out(self):
        changed = self.receipt.replace(
            "display=c4fe3c24:44400000:c481a1e0",
            "display=c4fe3c24:44f25bad:c481a1e0")
        sample = validate(changed, self.route)[2]
        self.assertNotEqual(sample["state"], sample["display"])


if __name__ == "__main__":
    unittest.main()
