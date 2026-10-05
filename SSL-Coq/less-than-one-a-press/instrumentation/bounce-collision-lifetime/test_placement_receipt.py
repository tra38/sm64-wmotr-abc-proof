import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent))
from placement_receipt import summarize

class ReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder=Path(__file__).resolve().parent
        raw=gzip.decompress((folder/'expected-placement-report.json.gz').read_bytes())
        receipt=json.loads((folder/'expected-placement-receipt.json').read_text(encoding='utf8'))
        assert hashlib.sha256(raw).hexdigest()==receipt['reportSha256']
        cls.r=json.loads(raw)
    def test_actual_totals(self):
        s=summarize(self.r)
        self.assertEqual((s['trials'],s['updates'],s['bounces']),(24,72,7))
        self.assertEqual(s['maxDetectedEndUpdateCollisionGap'],0.)
        self.assertEqual(s['maxDetectedEndUpdateDisplayGap'],249.95330810546875)
        self.assertEqual(s['maxDetectedBounceEntryRise'],89.9998779296875)
    def test_initial_sync_checked(self):
        r=copy.deepcopy(self.r);r['trials'][0]['before']['collision'][1]+=1
        with self.assertRaisesRegex(ValueError,'Unsynchronized'):summarize(r)
    def test_missing_update_rejected(self):
        r=copy.deepcopy(self.r);r['trials'][0]['samples'][1]['after']['timer']+=1
        with self.assertRaisesRegex(ValueError,'Noncontinuous'):summarize(r)
    def test_a_rejected(self):
        r=copy.deepcopy(self.r);r['trials'][0]['samples'][1]['after']['buttonPressed']=0x8000
        with self.assertRaisesRegex(ValueError,'Unexpected A'):summarize(r)
    def test_death_is_not_ink_or_bounce_rejection(self):
        s=summarize(self.r)
        low=[o for o in s['outcomes'] if o['position'][1]==768.]
        self.assertEqual(len(low),16)
        self.assertTrue(all(o['firstFloorNull'] and o['firstWarpOperation']==18 for o in low))
        self.assertFalse(any(o['bounceAtFirstActionEntry'] for o in low))

if __name__=='__main__':unittest.main()
