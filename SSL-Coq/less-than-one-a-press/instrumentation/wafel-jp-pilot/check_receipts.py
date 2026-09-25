"""Connect the saved-state branch to emulator samples and reject bad receipts."""
import argparse
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
from replay import compare, load_capture, RUNTIME

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('baseline', type=Path)
p.add_argument('branch', type=Path)
args = p.parse_args()
baseline = load_capture(args.baseline)
branch = load_capture(args.branch)
report = json.loads((RUNTIME/'branches.json').read_text())
first, length = report['firstPoll'], report['updates']
assert branch[:first-1] == baseline[:first-1]
samples = json.loads((RUNTIME/'branch-samples.json').read_text())
assert len(branch) == first+length and len(samples) == length
for actual, emulated in zip(samples, branch[first:first+length]):
    assert actual['timer'] == emulated['timer']+1
    assert all(actual.get(k) == v for k, v in emulated.items()
               if k not in ('poll', 'timer', 'buttons', 'stick'))
schedule = ''.join('%d %d %d %d\n' % (r['poll'], r['buttons'], *r['stick']) for r in branch)
expected_hash = next(r['inputSha256'] for r in report['results'] if r['name'] == 'neutral-30')
assert hashlib.sha256(schedule.encode()).hexdigest() == expected_hash
assert branch[first-1]['stick'] != baseline[first-1]['stick']
assert all(not r['buttons'] & 0x8000 for r in branch)
# A shifted timer or one changed position bit must fail. These are temporary
# diagnostic records, never a gameplay state or published counterexample.
with tempfile.TemporaryDirectory(dir=RUNTIME) as tmp:
    with contextlib.redirect_stdout(io.StringIO()):
        for field in ('positions', 'timer'):
            bad = copy.deepcopy(baseline[:355])
            if field == 'positions':
                bad[350][field][0] ^= 1
            else:
                bad[350][field] += 1
            assert not compare(bad, Path(tmp)/(field+'.json'))
print('PASS: saved-state branch matches all 90 emulator checkpoints; exact input schedule and no A; position-bit and timer-offset perturbations rejected.')
