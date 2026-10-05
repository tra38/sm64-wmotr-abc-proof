"""Small conditional JP bounce/collision-copy diagnostic; no route claim.

Restore an ordinary stock SSL scene, supply synchronized Mario contact poses
over actual live bounce actors, then use only neutral controller advances.
Actor size/location and RNG are never patched. Wafel's action-entry log exposes
movement but not raw collision at that cut; report that limitation explicitly.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'instrumentation/wafel-jp-pilot'))
from replay import create_game, Observer, load_capture, RUNTIME, set_input, bits
from benchmark_loop import require_match

FREEFALL = 0x0100088C

def snapshot(g):
    def words(values): return [bits(v) for v in values]
    return dict(frame=g.frame(), timer=g.read('gGlobalTimer'), area=g.read('gCurrAreaIndex'),
                movement=words(g.read('gMarioState.pos')),
                collision=words([g.read('gMarioObject.oPos'+a) for a in 'XYZ']),
                display=words(g.read('gMarioObject.header.gfx.pos')),
                action=g.read('gMarioState.action'), vy=bits(g.read('gMarioState.vel[1]')),
                particleFlags=g.read('gMarioState.particleFlags'),
                buttonDown=g.read('gControllers[0].buttonDown'),
                buttonPressed=g.read('gControllers[0].buttonPressed'))

def run(args):
    start=time.perf_counter()
    capture=RUNTIME/'capture.bKv95w/inputs.jsonl'
    rows=load_capture(capture)
    g=create_game(); observer=Observer(g)
    # A fixed, already checked controller prefix supplies all surrounding state.
    for row in rows[:args.poll-1]:
        if 'positions' in row: require_match(observer.snapshot(),row)
        set_input(g,row); g.advance()
    require_match(observer.snapshot(), rows[args.poll-1])
    scene=g.save_state(); scene_observation=snapshot(g)
    assert scene_observation['area']==1
    species=('bhvGoomba','bhvPokeyBodyPart','bhvFlyGuy','bhvKlepto')
    actors=[]
    for i in range(240):
        path='gObjectPool[%d].'%i
        if not g.read(path+'activeFlags'): continue
        name=next((n for n in species if g.read(path+'behavior')==g.address(n)),None)
        if name:
            actors.append(dict(slot=i, species=name, position=[g.read(path+'oPos'+a) for a in 'XYZ'],
                               height=g.read(path+'hitboxHeight'),radius=g.read(path+'hitboxRadius'),
                               downOffset=g.read(path+'hitboxDownOffset'),
                               intangibleTimer=g.read(path+'oIntangibleTimer')))
    trials=[]
    for actor in actors[:args.actors]:
        for epsilon in (1.0, 32.0):
            g.load_state(scene)
            position=list(actor['position']); position[1]+=epsilon
            patch={}
            for j,a in enumerate('XYZ'):
                for field in ('gMarioState.pos[%d]'%j,'gMarioObject.oPos'+a,'gMarioObject.header.gfx.pos[%d]'%j):
                    g.write(field,position[j]); patch[field]=g.read(field)
                field='gMarioState.vel[%d]'%j
                g.write(field,-4.0 if j==1 else 0.0); patch[field]=g.read(field)
            for field,value in (('action',FREEFALL),('actionArg',0),('actionState',0),('actionTimer',0),
                                ('quicksandDepth',0.0),('forwardVel',0.0)):
                g.write('gMarioState.'+field,value);patch['gMarioState.'+field]=value
            before=snapshot(g); samples=[]
            assert before['movement']==before['collision']==before['display']
            for update in range(args.updates):
                set_input(g,dict(buttons=0,stick=[0,0]));g.advance()
                after=snapshot(g)
                samples.append(dict(after=after,events=[e for e in g.frame_log()
                    if e['type'] in ('FLT_EXECUTE_ACTION','FLT_CHANGE_ACTION')]))
                if after['area']!=1: break
            entries=[e for e in samples[0]['events'] if e['type']=='FLT_EXECUTE_ACTION']
            detected=bool(entries and entries[0]['vel'][1] in (30.0,80.0)
                          and bits(entries[0]['pos'][1])==bits(actor['position'][1]+actor['height']))
            trials.append(dict(actor=actor,epsilon=epsilon,patch=patch,before=before,
                               bounceDetectedByActionEntry=detected,updates=samples))
    return dict(schema=1,runtime='Wafel 0.8.5 JP',poll=args.poll,scene=scene_observation,
                actors=actors,trials=trials,totalSeconds=time.perf_counter()-start,
                dllSha256=hashlib.sha256((RUNTIME/'sm64_jp.dll').read_bytes()).hexdigest(),
                captureSha256=hashlib.sha256(capture.read_bytes()).hexdigest(),
                scope='Supplied synchronized Mario contact poses in a controller-reached full scene. '
                      'Stock actor fields untouched; neutral A-released suffix. Not a reachable pose or no-A route.',
                observation='Exact end-update movement/collision/display words; within-update log exposes '
                            'only movement and velocity at action entry. No measured subframe collision-gap peak.')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--poll',type=int,default=500)
    p.add_argument('--actors',type=int,default=8)
    p.add_argument('--updates',type=int,default=24)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not 1<=a.actors<=8 or not 1<=a.updates<=24: p.error('Bounded: at most 8 actors and 24 updates')
    if a.output.exists(): p.error('Use a new report path')
    result=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(actors=len(result['actors']),trials=len(result['trials']),
        bounces=sum(t['bounceDetectedByActionEntry'] for t in result['trials']),
        totalSeconds=result['totalSeconds'])))

if __name__=='__main__': main()
