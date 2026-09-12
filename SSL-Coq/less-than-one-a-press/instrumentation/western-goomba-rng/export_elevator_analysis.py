"""Check native US/JP receipts and export their presentation data.

No movement is simulated here. Distances/time comparisons are measurements
of the saved source diagnostic, not all-history reachability bounds.
"""
import csv
import hashlib
import json
import math
from pathlib import Path
import re
import struct

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'build/instrumentation/western-goomba-rng/elevator-analysis'


def fields(line):
    return {k: float(v) for k, v in (x.split('=') for x in line.split(',')[1:])}


def matching(stem, extension):
    us = (OUT / f'{stem}-us.{extension}').read_bytes()
    assert us == (OUT / f'{stem}-jp.{extension}').read_bytes(), stem
    return us


def f32(x):
    return struct.unpack('f', struct.pack('f', float(x)))[0]


def rows(data):
    result = []
    for row in csv.DictReader(data.decode().splitlines()):
        result.append({k: (int(v) if k in ('frame','yaw','action','timer','flags','active','turning')
                           else f32(v)) for k,v in row.items()})
    assert all(row['frame'] == i+1 for i,row in enumerate(result))
    return result


def search(stem):
    log = matching(stem, 'txt').decode().splitlines()
    trace = matching(stem, 'csv')
    states = rows(trace)
    coverage = fields(next(s for s in log if s.startswith('SEARCH_COVERAGE,')))
    choices = next(s for s in log if s.startswith('CHOICE_PATH,'))
    frame = int(re.search(r'frames=(\d+)', choices)[1])
    assert 0 < frame <= len(states) <= 900
    last_depth = fields([s for s in log if s.startswith('CHOICE_DEPTH,')][-1])
    best = states[frame-1]
    assert all(best[k] == f32(last_depth[k]) for k in ('x','y','z'))
    assert coverage['nearBaseSamples'] == 0
    assert all(abs(r['x']) < 8192 and abs(r['y']) < 8192 and abs(r['z']) < 8192 for r in states)
    return dict(config=fields(next(s for s in log if s.startswith('STOCK_SEARCH,'))),
                coverage=coverage, best=best, choices=choices.split(',')[2:], states=states,
                csvSha256=hashlib.sha256(trace).hexdigest(), targetDistance=last_depth['closest'])


scene = matching('scene', 'txt').decode().splitlines()
timeline = [{k: float(v) for k,v in r.items()} for r in
            csv.DictReader(matching('elevator', 'csv').decode().splitlines())]
assert len(timeline) == 901 and all(r['frame'] == i for i,r in enumerate(timeline))
timing = fields(next(s for s in scene if s.startswith('ELEVATOR,')))
assert timing == dict(gripY=4020,hitboxTopY=4120,belowGripFrame=104,
    belowHitboxFrame=94,below640Frame=442,bottomFrame=493,settledFrame=502)
inventory = [fields(s) for s in scene if s.startswith('ACTOR,')]
assert len(inventory) == 9
names = ['East raised 1','East low','Western','East raised 2','East raised 3','Southern',
         'Triplet child 0','Triplet child 1','Triplet child 2']
targets = [[512,768],[512,-255],[-511,768],[512,768],[512,-255],[-511,768]]
for i, actor in enumerate(inventory):
    actor['name'] = names[i]
    actor['relativeToSecondPole'] = 'below'
    assert actor['spawnY'] < timing['gripY'] and actor['homeY']+75 < timing['gripY']
    if i < 6:
        actor['search'] = search(f'actor-{i}')
        actor['targetXZ'] = targets[i]
        actor['firstLowLanding'] = next((r for r in actor['search']['states']
            if r['floor'] < 0 and abs(r['y']-r['floor']) < .001 and r['flags'] & 3), None)
        # The native trace labels update 1 after the scene's frame-0 update.
        for row in actor['search']['states']:
            assert row['mario_y'] == f32(timeline[row['frame']-1]['elevator_y'])
    else:
        actor['search'] = None
        actor['firstLowLanding'] = None
parent = fields(next(s for s in scene if s.startswith('TRIPLET_PARENT,')))
assert parent['minHorizontalDistance'] > parent['activationThreshold'] == 3000
assert [p['firstLowLanding'] is not None for p in inventory] == [True,False,False,True,True,False,False,False,False]
direct = search('west-direct')
assert direct['coverage']['rim'] == 0
result = dict(scope='Bounded native source search and stock scene measurements; no complete gameplay route or global shortest-path proof.',
              versions=['US','JP'], fps=30, timing=timing, elevator=timeline,
              actors=inventory, tripletParent=parent, westernDirect=direct)
(OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(timing=timing,actors=[dict(name=p['name'],homeY=p['homeY'],
    minimumBaseGap=p['search']['coverage']['minBaseGap'] if p['search'] else None,
    highestSample=p['search']['coverage']['highestY'] if p['search'] else None) for p in inventory],
    directBest=direct['best'],tripletParent=parent),indent=2))

# Use the existing cutaway renderer for the new direct-rim replay. The same
# source mesh and documented schematic artwork are retained.
original = json.loads((ROOT/'build/instrumentation/western-goomba-rng/video/data.json').read_text())
order = ['frame','x','y','z','yaw','action','timer','flags','floor','active']
original['frames'] = [[r[k] for k in order] for r in direct['states']]
original['csvSha256'] = direct['csvSha256']
original['grantedMario'] = [-410,128,667]
original['waypoint'] = dict(frame=direct['best']['frame'],position=[direct['best'][k] for k in ('x','y','z')])
original['home']['distances'] = [math.dist([-3638,0,1928],[r[k] for k in ('x','y','z')]) for r in direct['states']]
folder = OUT/'video-direct';folder.mkdir(exist_ok=True)
(folder/'data.json').write_text(json.dumps(original))
