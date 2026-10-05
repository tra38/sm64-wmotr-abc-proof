"""Bounded chosen-XYZ transfer check; no supplied size or route claim.

Reuse initialized stock actors in the checked JP scene. Relocate one actor and
supply synchronized Mario once, then advance continuously with neutral input.
An actor relocation is the user's conditional clone-placement grant, not a
constructed fake pickup. Native behavior, tangibility, scale and hitbox remain
untouched. This intentionally includes the already-contacting warp pose.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from observe import ROOT, RUNTIME, FREEFALL, snapshot
from replay import create_game, Observer, load_capture, set_input, bits
from benchmark_loop import require_match

def previous_positive_f32(value):
    return struct.unpack('>f', struct.pack('>I', bits(value)-1))[0]

def run():
    started=time.perf_counter()
    capture=RUNTIME/'capture.bKv95w/inputs.jsonl'
    rows=load_capture(capture); g=create_game(); observer=Observer(g)
    for row in rows[:499]:
        if 'positions' in row: require_match(observer.snapshot(),row)
        set_input(g,row); g.advance()
    require_match(observer.snapshot(),rows[499])
    scene=g.save_state(); actors=[]
    names=('bhvGoomba','bhvPokeyBodyPart','bhvFlyGuy','bhvKlepto')
    for slot in range(240):
        path='gObjectPool[%d].'%slot
        if not g.read(path+'activeFlags'): continue
        name=next((n for n in names if g.read(path+'behavior')==g.address(n)),None)
        if name:
            actors.append(dict(slot=slot,species=name,position=[g.read(path+'oPos'+a) for a in 'XYZ'],
                scale=g.read(path+'header.gfx.scale'),height=g.read(path+'hitboxHeight'),
                radius=g.read(path+'hitboxRadius'),downOffset=g.read(path+'hitboxDownOffset'),
                tangible=g.read(path+'oIntangibleTimer')==0,action=g.read(path+'oAction')))
    available_actors=len(actors)
    actors=actors[:8]
    if not actors:raise RuntimeError('No initialized actor candidates in the checked scene')
    trials=[]
    poses=[(-2400.,768.,-1024.),(-2400.,1280.,-1024.),(-2200.,768.,-1024.)]
    for actor in actors:
        for position in poses:
            g.load_state(scene); patch={}
            for j,a in enumerate('XYZ'):
                for field in ('gMarioState.pos[%d]'%j,'gMarioObject.oPos'+a,'gMarioObject.header.gfx.pos[%d]'%j):
                    g.write(field,position[j]);patch[field]=g.read(field)
                field='gMarioState.vel[%d]'%j
                g.write(field,-4. if j==1 else 0.);patch[field]=g.read(field)
                field='gObjectPool[%d].oPos'%actor['slot']+a
                value=previous_positive_f32(position[1]) if j==1 else position[j]
                g.write(field,value);patch[field]=g.read(field)
            for field,value in (('action',FREEFALL),('actionArg',0),('actionState',0),('actionTimer',0),
                                ('quicksandDepth',0.),('forwardVel',0.)):
                g.write('gMarioState.'+field,value);patch['gMarioState.'+field]=value
            before=snapshot(g);assert before['movement']==before['collision']==before['display']
            samples=[]
            for _ in range(3):
                set_input(g,dict(buttons=0,stick=[0,0]));g.advance()
                samples.append(dict(after=snapshot(g),floorNull=g.read('gMarioState.floor').is_null(),
                    warpOperation=g.read('sDelayedWarpOp'),
                    events=[e for e in g.frame_log() if e['type'] in
                        ('FLT_EXECUTE_ACTION','FLT_CHANGE_ACTION','FLT_WARP','FLT_INIT_MARIO')]))
            trials.append(dict(actor=actor,patch=patch,before=before,samples=samples))
    return dict(schema=1,runtime='Wafel 0.8.5 JP',poll=500,availableActors=available_actors,actors=actors,trials=trials,
        totalSeconds=time.perf_counter()-started,
        dllSha256=hashlib.sha256((RUNTIME/'sm64_jp.dll').read_bytes()).hexdigest(),
        captureSha256=hashlib.sha256(capture.read_bytes()).hexdigest(),
        scope='Conditional chosen actor XYZ and synchronized Mario pose. No size, tangibility, behavior, '
              'home, RNG, floor or collision-list patch. Three uninterrupted neutral A-released updates '
              'per trial. Not a clone construction or controller-reached contact.',
        observation='End-update exact movement/collision/display bits; action-entry log exposes movement '
              'only. No direct measured subframe collision gap or all-size-history claim.')

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.output.exists():p.error('Use a fresh report path')
    r=run();a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(r,indent=2)+'\n',encoding='utf8')
    print(json.dumps(dict(trials=len(r['trials']),updates=3*len(r['trials']),seconds=r['totalSeconds'])))

if __name__=='__main__':main()
