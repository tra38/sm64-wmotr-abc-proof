"""Compare the captured JP controller replay with pinned Wafel 0.8.5.

The only non-controller write is the pre-entry level-select flag, matching
the project's already accepted startup. No gameplay pose/depth/RNG is set.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import wafel

ROOT = Path(__file__).resolve().parents[2]
RUNTIME = ROOT / 'build/wafel-pilot'

def bits(value):
    return struct.unpack('>I', struct.pack('>f', value))[0]

def set_input(game, record):
    # The released 0.8.5 Python API predates main's set_input convenience call.
    for field, value in [('button', record['buttons']), ('stick_x', record['stick'][0]), ('stick_y', record['stick'][1])]:
        game.write('gControllerPads[0].' + field, value)

def create_game():
    expected = '960fe979068b78e6733b3ddb87741833fbf4eb29b2a21a2bba871977427c2d0f'
    assert hashlib.sha256((RUNTIME / 'sm64_jp.dll').read_bytes()).hexdigest() == expected
    game = wafel.Game(str(RUNTIME / 'sm64_jp.dll'))
    game.write('gDebugLevelSelect', 1)
    return game

class Observer:
    def __init__(self, game):
        self.game = game
        self.slots = [game.address('gObjectPool[%d]' % i) for i in range(240)]

    def slot(self, address):
        if address is None or address.is_null():
            return -1
        try:
            return self.slots.index(address)
        except ValueError:
            return -2

    def snapshot(self):
        g = self.game
        read = g.read
        mario = read('gMarioObject')
        result = {'timer': read('gGlobalTimer'), 'area': read('gCurrAreaIndex')}
        if result['area'] == 1 and self.slot(mario) >= 0:
            xyz = read('gMarioState.pos')
            xyz += [read('gMarioObject.oPos' + axis) for axis in 'XYZ']
            xyz += read('gMarioObject.header.gfx.pos')
            result.update(action=read('gMarioState.action'), actionTimer=read('gMarioState.actionTimer'),
                          input=read('gMarioState.input'), positions=[bits(v) for v in xyz],
                          floorHeight=bits(read('gMarioState.floorHeight')),
                          floorNull=int(read('gMarioState.floor').is_null()),
                          floorOwner=self.slot(read('gMarioState.floor?.object')),
                          platform=self.slot(read('gMarioPlatform')), marioSlot=self.slot(mario))
            # The original stock actor's slot is checked by behavior at entry.
            result.update(topSlot=61, topTimer=read('gObjectPool[61].oTimer'),
                          topAction=read('gObjectPool[61].oAction'),
                          pillars=read('gObjectPool[61].oPyramidTopPillarsTouched'),
                          topActive=read('gObjectPool[61].activeFlags'))
        return result

def load_capture(path):
    # Raw logs are accepted while diagnosing, but final comparison uses the
    # capture.sh output produced only after the inherited observer checks pass.
    rows = []
    for line in path.read_text(encoding='utf-8', errors='replace').splitlines():
        if line.startswith('WAFEL_PILOT,'):
            rows.append(json.loads(line.split(',', 1)[1]))
        elif line.startswith('{'):
            rows.append(json.loads(line))
    return rows

def compare(rows, output):
    """Require exact sampled fields and the one established poll-boundary offset."""
    assert rows and [r['poll'] for r in rows] == list(range(1, len(rows)+1))
    assert all(not r['buttons'] & 0x8000 for r in rows)
    g = create_game()
    observer = Observer(g)
    mismatch = []
    counts = {}
    event_fields = {}
    checked = 0
    timer_offsets = set()
    for row in rows:
        actual = observer.snapshot()
        if 'positions' in row:
            checked += 1
            timer_offsets.add(actual['timer'] - row['timer'])
            if checked == 1:
                assert g.read('gObjectPool[61].behavior') == g.address('bhvPyramidTop')
            diffs = {key: [value, actual.get(key)] for key, value in row.items()
                     if key not in ('poll', 'timer', 'buttons', 'stick') and value != actual.get(key)}
            for key in diffs:
                counts[key] = counts.get(key, 0) + 1
            if diffs and len(mismatch) < 12:
                mismatch.append({'poll': row['poll'], 'timer': row['timer'], 'differences': diffs})
        set_input(g, row)
        g.advance()
        for event in g.frame_log():
            event_fields.setdefault(event['type'], set()).update(event.keys())
    result = {'inputRows': len(rows), 'checkedRows': checked, 'aButtonFrames': 0,
              'timerOffsets': sorted(timer_offsets), 'mismatchFieldCounts': counts,
              'firstMismatches': mismatch,
              'eventFields': {key: sorted(value) for key, value in event_fields.items()},
              'passed': bool(checked) and not counts and timer_offsets == {1}}
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
    return result['passed']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--output', type=Path, default=RUNTIME/'comparison.json')
    args = parser.parse_args()
    rows = load_capture(args.capture)
    if not compare(rows, args.output):
        raise SystemExit('Replay mismatch: do not use this run as a validated baseline.')

if __name__ == '__main__':
    main()
