"""Ensure the receipt checker rejects missing mechanical connections."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from check import check


class ReceiptCheck(unittest.TestCase):
    def setUp(self):
        self.trace = Path(__file__).with_name("expected-trace.txt").read_text()

    def validate(self, trace):
        with tempfile.TemporaryDirectory(prefix="sm64-vertical-receipt-") as directory:
            path = Path(directory) / "trace.txt"
            path.write_text(trace)
            with contextlib.redirect_stdout(io.StringIO()):
                check(path)

    def test_recorded_success(self):
        self.validate(self.trace)

    def test_rejects_a_missing_connection(self):
        alterations = [
            ("VERTICAL_QUERY,index=1", "floor=00000000", "floor=8019ba80"),
            ("VERTICAL_QUERY,index=2", "owner=803451f8", "owner=00000000"),
            ("VERTICAL_NODE,query=1,kind=dynamic,index=0", "next=8018b340", "next=00000000"),
            ("TRACE_A1,timer=500", "platform=803451f8", "platform=00000000"),
            ("FIRST_APPLY_RETURN", "marioBits=(43b6cbe0,45abe000,c48919af)",
             "marioBits=(00000000,45abe000,43800000)"),
            ("VERTICAL_INPUTS,timer=516", "pressed=0", "pressed=1"),
        ]
        for prefix, old, new in alterations:
            with self.subTest(connection=prefix):
                lines = self.trace.splitlines()
                matching = [i for i, line in enumerate(lines) if line.startswith(prefix + ",")]
                self.assertEqual(len(matching), 1)
                index = matching[0]
                self.assertIn(old, lines[index])
                lines[index] = lines[index].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    self.validate("\n".join(lines) + "\n")


if __name__ == "__main__":
    unittest.main()
