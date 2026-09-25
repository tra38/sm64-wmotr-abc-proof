"""Five finite controller choices at one reached late-approach checkpoint."""
import argparse
import hashlib
import json
import struct
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from replay import create_game, load_capture, Observer, set_input, RUNTIME

FIRST, LENGTH = 2700, 90

def floats(words):
    return [struct.unpack('>f', struct.pack('>I', word))[0] for word in words]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('capture')
    args = p.parse_args()
    rows = load_capture(Path(args.capture))
    g = create_game()
    o = Observer(g)
    prefix = rows[:FIRST-1]
    assert [r['poll'] for r in rows] == list(range(1, len(rows)+1))
    assert all(not r['buttons'] & 0x8000 for r in rows)
    # Reach the checkpoint through the validated controller prefix; no pose,
    # action, depth, enemy or RNG write, and no imported emulator savestate.
    for row in prefix:
        actual = o.snapshot()
        if 'positions' in row:
            assert actual['timer'] == row['timer']+1
            assert all(actual.get(k) == v for k, v in row.items()
                       if k not in ('poll', 'timer', 'buttons', 'stick'))
        set_input(g, row)
        g.advance()
    saved = g.save_state()
    initial = o.snapshot()
    results = []
    for name in ('baseline', 'neutral-30', 'hold-z', 'reverse-x', 'b-once'):
        g.load_state(saved)
        assert o.snapshot() == initial
        inputs, samples = [], []
        for i, row in enumerate(rows[FIRST-1:FIRST-1+LENGTH]):
            record = dict(row, stick=list(row['stick']))
            if name == 'neutral-30' and i < 30:
                record.update(buttons=0, stick=[0, 0])
            elif name == 'hold-z':
                record['buttons'] |= 0x2000
            elif name == 'reverse-x':
                record['stick'][0] = max(-128, min(127, -record['stick'][0]))
            elif name == 'b-once' and i == 0:
                record['buttons'] |= 0x4000
            assert not record['buttons'] & 0x8000
            inputs.append(record)
            set_input(g, record)
            g.advance()
            samples.append(o.snapshot())
        assert len(samples) == LENGTH and all('positions' in s for s in samples)
        dy = [floats(s['positions'])[7]-floats(s['positions'])[1] for s in samples]
        cy = [floats(s['positions'])[7]-floats(s['positions'])[4] for s in samples]
        summary = dict(name=name, updates=LENGTH, area1Samples=len(samples),
                       floorNullSamples=sum(s['floorNull'] for s in samples),
                       maxDisplayMinusStateY=max(dy), minDisplayMinusStateY=min(dy),
                       maxDisplayMinusCollisionY=max(cy),
                       anyPositionSplit=sum(s['positions'][:3] != s['positions'][3:6]
                           or s['positions'][:3] != s['positions'][6:] for s in samples),
                       finalPosition=floats(samples[-1]['positions'])[:3],
                       actions=sorted({s['action'] for s in samples}),
                       topActiveValues=sorted({s['topActive'] for s in samples}))
        results.append(summary)
        # Full controller prefix and this interval, plus one final input poll
        # at which the last resulting snapshot is observed by the emulator.
        schedule = prefix + inputs + [dict(rows[FIRST-1+LENGTH], buttons=0, stick=[0, 0])]
        text = ''.join('%d %d %d %d\n' % (r['poll'], r['buttons'], *r['stick']) for r in schedule)
        (RUNTIME/(name+'.inputs')).write_text(text, encoding='ascii')
        if name == 'neutral-30':
            (RUNTIME/'branch-samples.json').write_text(json.dumps(samples, indent=2)+'\n')
            summary['inputSha256'] = hashlib.sha256(text.encode('ascii')).hexdigest()
    report = dict(firstPoll=FIRST, updates=LENGTH, secondsAt30Hz=LENGTH/30,
                  aButtonFrames=0, initialPosition=floats(initial['positions'])[:3],
                  initialTopActive=initial['topActive'], initialTopTimer=initial['topTimer'],
                  initialTopAction=initial['topAction'], results=results,
                  scope='Finite after-update samples. The original top slot becomes inactive during these intervals. Adapter pilot, not an Ink search closure.')
    (RUNTIME/'branches.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
