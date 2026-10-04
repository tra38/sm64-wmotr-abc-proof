"""Audit exact saved parent failures; optionally replay their real suffixes.

The original strict search and its ledger are never changed. A diagnostic
continues past an unequal parent, without claiming equality or merging states.
Only its earliest pose is patched, and all A/history checks remain active.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json
from reverse_scattershot import (open_store,make_scene,verify_recipe_sources,controls_from,
                                DISAPPEARED,END_FIELDS,FIRST_APPLY,GameBudgetReached)
from search import differences,bits,A_BUTTON,number
from work_limits import WorkLimits,LimitReached

POSITION_FIELDS={'movement','collision','display'}
CONTROLLER_FIELDS={'pad','buttonDown','buttonPressed'}


def histogram(records):
    fields=Counter();patterns=Counter();families=Counter();actions=Counter();floors=Counter();rng=Counter()
    controller_mismatches=position_mismatches=0;selected=[]
    for r in records:
        d=r['detail'];c=d['proposal']
        if c['ticket']['kind']!='extend':continue
        if r['status']!='rejected' or d.get('stage')!='parent':
            raise ValueError('Selected earlier attempt is not a recorded parent rejection')
        diff=d['differences']; keys=set(diff)
        fields.update(keys);patterns[tuple(sorted(keys))]+=1;families[c['family']]+=1
        controller_mismatches+=bool(keys&CONTROLLER_FIELDS)
        position_mismatches+=bool(keys&POSITION_FIELDS)
        if 'action' in diff:actions[hex(diff['action']['actual'])]+=1
        if 'floorHeight' in diff:
            floors[(number(diff['floorHeight']['expected']),number(diff['floorHeight']['actual']))]+=1
        if 'rng' in diff:rng[(diff['rng']['expected'],diff['rng']['actual'])]+=1
        selected.append(dict(case=r['case'],family=c['family'],move=c['move'],parent=c['ticket']['parent'],
                             input=c['controls'][0],differences=diff))
    return dict(selectedAttempts=len(selected),fieldMismatchCounts=dict(sorted(fields.items())),
                familyCounts=dict(families),controllerMismatchAttempts=controller_mismatches,
                positionMismatchAttempts=position_mismatches,actualDifferentActions=dict(actions),
                floorPairs=[dict(expected=k[0],actual=k[1],count=n) for k,n in sorted(floors.items())],
                rngPairs=[dict(expected=k[0],actual=k[1],count=n) for k,n in sorted(rng.items())],
                patterns=[dict(fields=list(k),count=n) for k,n in patterns.most_common()],rows=selected,
                interpretation='Counts overlap. Unequal parent observations reject exact-parent reproduction, '
                    'not every possible useful continuation. pad is the OS pad buffer, not Controller.rawStickX/Y.')


def observation(backend):
    g=backend.game
    if g.read('gCurrAreaIndex')==1:return backend.observe()
    return dict(area=g.read('gCurrAreaIndex'),movement=[bits(v) for v in g.read('gMarioState.pos')],
                collision=[bits(g.read('gMarioObject.oPos'+axis)) for axis in 'XYZ'],
                display=[bits(v) for v in g.read('gMarioObject.header.gfx.pos')],
                action=g.read('gMarioState.action'),actionArg=g.read('gMarioState.actionArg'),
                usedSlot=backend.observer.slot(g.read('gMarioState.usedObj')),
                platform=backend.observer.slot(g.read('gMarioPlatform')),
                buttonDown=g.read('gControllers[0].buttonDown'),
                buttonPressed=g.read('gControllers[0].buttonPressed'))


def replay_actual_suffix(backend,context,record,signature,neutral,tick=None,update_limit=None):
    """One earliest restore/patch, all recorded inputs and 23 neutral advances.

    Parent differences are diagnostic only. Reaching a different parent does
    not change any later input or trigger a new patch. The shifted-installation
    observation is separate from matching the prescribed last-update target.
    """
    tick=tick or (lambda:None)
    c=record['detail']['proposal'];controls=controls_from(c['controls'])
    backend.restore(context);backend.patch(c['patch']);initial=backend.observe()
    current=initial;updates=0;raw_checks=0;parents=[];events=[];transitions=[]
    captured=False;retained=True;first_area2=None;observed=[];last_start=None;last_events=[]
    def advance(control,phase):
        nonlocal updates,current,raw_checks,captured,retained,first_area2
        if update_limit is not None and updates>=update_limit:raise GameBudgetReached(updates)
        tick();before=current;frame=backend.frame();timer=backend.game.read('gGlobalTimer')
        backend.advance(control);updates+=1
        if backend.frame()!=frame+1 or backend.game.read('gGlobalTimer')!=timer+1:
            raise RuntimeError('Diagnostic native update boundary changed')
        current=observation(backend);g=backend.game
        raw=[g.read('gControllers[0].'+k) for k in ('rawStickX','rawStickY')]
        if raw!=[control.x,control.y] or current['buttonDown']!=control.buttons:
            raise RuntimeError('Native Controller readback differs from requested input')
        raw_checks+=1
        if (bool(current['buttonDown']&A_BUTTON)!=(signature['aMode']=='held')
                or current['buttonPressed']&A_BUTTON):
            raise RuntimeError('Diagnostic violates recorded A history')
        log=[e for e in g.frame_log() if e['type']=='FLT_EXECUTE_ACTION']
        appeared=[e for e in log if e['action']==DISAPPEARED]
        if appeared:
            events.append(dict(update=updates,phase=phase,movement=[[bits(v) for v in e['pos']] for e in appeared]))
        # Contact can set ACT_DISAPPEARED before geometry returns early, and
        # executing that action can decrement its low argument from 2 to 1.
        # Keep entry into that state separate from observing the action execute.
        if (before.get('action')!=DISAPPEARED and current.get('action')==DISAPPEARED
                and current.get('usedSlot')==64 and current.get('actionArg') in (0x40001,0x40002)):
            transitions.append(dict(update=updates,phase=phase,
                                    movement=[bits(v) for v in appeared[0]['pos']] if appeared else None,
                                    actionEntryObserved=bool(appeared),endActionArg=current['actionArg'],
                                    actualStartRecords={k:before[k] for k in POSITION_FIELDS},
                                    endPlatform=current['platform'],endFloorOwner=current.get('floorOwner'),
                                    acceptedReturnRecords='Only movement is observed within update; '
                                       'raw/display are start-record observations, not accepted-return reads.'))
            if current['platform']==61:captured=True
        if captured and current['area']==1 and current['platform']!=61:retained=False
        if current['area']==2 and first_area2 is None:
            first_area2=dict(update=updates,endMovement=current['movement'],endCollision=current['collision'],
                            endPlatform=current['platform'],
                            actionEntries=[dict(action=e['action'],movement=[bits(v) for v in e['pos']]) for e in log])
        observed.append(dict(update=updates,phase=phase,observation=current,controllerRawStick=raw))
        return before,appeared
    for i,control in enumerate(controls):
        before,last_events=advance(control,'suffix')
        if i<len(c['checkpoints']):
            expected=c['checkpoints'][i]
            diff=differences(current,expected,tuple(expected))
            parents.append(dict(update=updates,differences=diff))
            if i==0 and diff!=record['detail']['differences']:
                raise RuntimeError('Replayed first-parent differences do not reproduce the saved attempt')
        if i==len(controls)-1:last_start=before
    decisions={}
    for name in c['targets']:
        target=signature['targets'][name];diff=differences(current,signature['endpoints'][name],END_FIELDS)
        movement_ok=len(last_events)==1 and [bits(v) for v in last_events[0]['pos']]==target['movement']
        prefix_ok=all(last_start.get(k)==target[k] for k in ('collision','display'))
        decisions[name]=dict(endDifferences=diff,movementEventMatches=movement_ok,
                             actualStartRecordsMatch=prefix_ok,
                             selectedConditionalEndpoint=not diff and movement_ok and prefix_ok,
                             pending=signature['entryRecordContract'])
    for _ in range(signature['retentionSuffix']['updates']):advance(neutral,'retention')
    first_exact=bool(first_area2 and first_area2['endMovement']==FIRST_APPLY
                     and len(first_area2['actionEntries'])==1
                     and first_area2['actionEntries'][0]['movement']==FIRST_APPLY)
    specific_payoff=captured and retained and first_exact
    return dict(case=record['case'],family=c['family'],move=c['move'],updates=updates,
                parentComparisons=parents,selectedTargets=decisions,
                strictParentMatched=all(not p['differences'] for p in parents),
                disappearedTransitions=transitions,actionEvents=events,
                capturedTopAfterTransition=captured,retainedCapturedTopInArea1=retained if captured else None,
                firstArea2=first_area2,checkedKnownPayoff=specific_payoff,
                selectedLastUpdateContinuation=any(v['selectedConditionalEndpoint'] for v in decisions.values()) and specific_payoff,
                nativeInputReadbacks=raw_checks,
                initialRecordsSynchronized=initial['movement']==initial['collision']==initial['display'],
                initialDepth=initial['depth'],observations=observed,
                scope='Actual continuous suffix after a different parent; full memory equality/reachability '
                    'are not claimed. Earlier warp transitions are timing variants, not two matching parent edges.')


def run(args):
    started=time.perf_counter();limits=WorkLimits(args.setup_seconds,args.verification_seconds,args.search_seconds,args.wall_seconds)
    result=dict(schema=1,status='started',gameUpdateBudget=args.game_updates,replay=[])
    signature=json.loads((args.ledger/'manifest.json').read_text())['payload']['signature']
    limits.enter('verification')
    try:
        selected_records=[]
        with open_store(args.ledger,signature,True,'full',check=limits.check,read_only=True) as s:
            def audited_records():
                for r in s.records():
                    if r['detail']['proposal']['ticket']['kind']=='extend':
                        if len(selected_records)>=146:raise ValueError('Diagnostic batch exceeds 146 saved extensions')
                        selected_records.append(r)
                    yield r
            h=histogram(audited_records());result.update(histogram=h,
              provenance=dict(sourceLedger=str(args.ledger),manifestSha256=s.manifest_sha,
                              commitSha256=s.commit_sha,verifiedAttempts=s.state['nextCase'],fullHistoryVerified=True))
        if args.replay_suffix:
            limits.enter('preparation');verify_recipe_sources(signature,limits.check)
            b,contexts,targets,endpoints,recipes,neutral,presses=make_scene(signature['depth'],signature['aMode'],limits.check)
            if (endpoints!=signature['endpoints'] or recipes!=signature['jobOrder'] or targets!=signature['targets']
                    or [c.frame for c in contexts]!=signature['contextFrames']):
                raise RuntimeError('Pinned diagnostic scene differs from saved source')
            result['preparationGameUpdates']=contexts[-1].frame+3
            updates=0;result['nativeSearchUpdates']=0
            limits.enter('search')
            for r in selected_records:
                limits.check();c=r['detail']['proposal']
                try:
                    outcome=replay_actual_suffix(b,contexts[-c['depth']],r,signature,neutral,
                                                update_limit=args.game_updates-updates)
                except GameBudgetReached as exc:
                    updates+=exc.updates;result['nativeSearchUpdates']=updates;result['incompleteCase']=r['case'];break
                updates+=outcome['updates'];result['replay'].append(outcome)
                result['nativeSearchUpdates']=updates
            result['nativeSearchUpdates']=updates
            result['completedReplays']=len(result['replay'])
            result['nativeInputReadbacks']=sum(r['nativeInputReadbacks'] for r in result['replay'])
            result['replaySummary']=dict(
                firstParentDifferencesReproduced=len(result['replay']),
                checkedKnownPayoffs=sum(r['checkedKnownPayoff'] for r in result['replay']),
                selectedLastUpdateContinuations=sum(r['selectedLastUpdateContinuation'] for r in result['replay']),
                earlyWarpStates=sum(any(t['update']==1 for t in r['disappearedTransitions']) for r in result['replay']),
                earlyExecutedDisappearedEntries=sum(any(t['update']==1 and t['actionEntryObserved']
                                                        for t in r['disappearedTransitions']) for r in result['replay']),
                topCaptures=sum(r['capturedTopAfterTransition'] for r in result['replay']),
                firstArea2Entries=sum(r['firstArea2'] is not None for r in result['replay']))
        result['status']='complete' if 'incompleteCase' not in result else 'native-update-budget-incomplete'
    except LimitReached as exc:
        result['status']='verification incomplete' if exc.phase=='verification' else exc.phase+' incomplete'
        result['completedReplays']=len(result['replay'])
    limits.enter('finalization')
    result['sourceHashes']={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                           for name in ('parent_diagnostics.py','reverse_scattershot.py','search.py','chunk_ledger.py')}
    result['timing']=limits.finish()
    result['timing']['diagnosticSearchCheckBoundary']='Between complete suffix+retention replays; '
    result['timing']['diagnosticSearchCheckBoundary']+='native update allowance checks before each advance.'
    result['scope']=('Exact saved finite trials, no new inverse proposals or state merging; '
                     'no gameplay reachability, formal exclusion, Coq result or route-estimate change.')
    atomic_json(args.output,result)
    print(json.dumps({k:result[k] for k in ('status','histogram','replaySummary','nativeSearchUpdates','timing') if k in result},
                     default=str) if args.verbose else json.dumps({k:result[k] for k in
                     ('status','completedReplays','replaySummary','nativeSearchUpdates','timing') if k in result}))
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ledger',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--replay-suffix',action='store_true');p.add_argument('--verbose',action='store_true')
    p.add_argument('--game-updates',type=int,default=5000)
    p.add_argument('--setup-seconds',type=float,default=30);p.add_argument('--verification-seconds',type=float,default=30)
    p.add_argument('--search-seconds',type=float,default=30);p.add_argument('--wall-seconds',type=float,default=90)
    a=p.parse_args()
    if a.output.exists():p.error('Choose a new diagnostic output; source ledgers are read-only')
    if not 1<=a.game_updates<=5000:p.error('Bounded diagnostic update limit is 1..5000')
    run(a)


if __name__=='__main__':main()
