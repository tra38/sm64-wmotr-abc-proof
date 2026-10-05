from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent))
from receipt import summarize

def sample():
    # Known float words 768,769; the validation should expose a surviving gap.
    before=dict(frame=1,timer=10,movement=[0,1145044992,0],collision=[0,1145044992,0],display=[0,1145044992,0])
    after=dict(before,frame=2,timer=11,buttonDown=0,buttonPressed=0,particleFlags=0)
    return dict(trials=[dict(before=before,actor=dict(species='test',slot=1),epsilon=1,
        bounceDetectedByActionEntry=True,updates=[dict(after=after)])],scope='conditional',observation='end only')

class ReceiptTests(unittest.TestCase):
    def test_equal(self):
        r=summarize(sample());self.assertEqual(r['unequalEndUpdateY'],0)
    def test_surviving_gap_is_counted(self):
        d=sample();d['trials'][0]['updates'][0]['after']['collision']=[0,1145061376,0]
        r=summarize(d);self.assertEqual(r['unequalEndUpdateY'],1);self.assertGreater(r['maxDetectedEndUpdateCollisionGap'],0)
    def test_unsynchronized_start_refused(self):
        d=sample();d['trials'][0]['before']['collision']=[0,0,0]
        with self.assertRaises(ValueError):summarize(d)
    def test_skipped_update_refused(self):
        d=sample();d['trials'][0]['updates'][0]['after']['frame']=3
        with self.assertRaises(ValueError):summarize(d)
    def test_a_press_refused(self):
        d=sample();d['trials'][0]['updates'][0]['after']['buttonPressed']=0x8000
        with self.assertRaises(ValueError):summarize(d)

if __name__=='__main__':unittest.main()
