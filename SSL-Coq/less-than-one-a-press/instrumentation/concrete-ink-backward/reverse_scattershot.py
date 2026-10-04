"""Bounded concrete backward sampling; recipes and complete suffixes, no SMT.

Contexts are reconstructed from a pinned complete initialization/controller
recipe. Only the earliest pose is patched; the whole suffix then runs natively.
Coarse buckets schedule/retain candidates, never establish state equivalence.
"""
import argparse
from collections import Counter
from dataclasses import replace
import hashlib
import json
import math
import platform
from importlib.metadata import version
from functools import lru_cache
from pathlib import Path
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import ChunkLedger, STATUSES, atomic_json, encoded
from work_limits import WorkLimits, LimitReached
from product_sweep import (NAMES, specification, pose_templates, decode_input, selected_bits,
                           peak_rss_bytes, hash_file)
from search import (Backend, Observer, create_game, prepare, load_capture, RUNTIME, ROOT,
                    Input, Move, bits, number, differences, END_FIELDS, DISAPPEARED,
                    previous_templates, A_BUTTON)

BUTTON_CLASSES = ('none','B','Z','B+Z','camera','R','Start')
RECTS = ((-8,8,-8,8),(-128,-9,-8,8),(9,127,-8,8),(-8,8,-128,-9),
         (-8,8,9,127),(-128,-9,-128,-9),(-128,-9,9,127),(9,127,-128,-9),(9,127,9,127))
PARENT_FIELDS = None  # all fields in the stored observation, explicitly not all game memory
FIRST_APPLY = [bits(365.5927734375),bits(5500.),bits(-1096.8026123046875)]


class GameBudgetReached(Exception):
    def __init__(self, updates):
        self.updates=updates


def digest(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def button_class(mask):
    if mask & 0x1000: return 'Start'
    if mask & 0x10: return 'R'
    if mask & 0xf: return 'camera'
    return ('none','B','Z','B+Z')[bool(mask&0x4000)+2*bool(mask&0x2000)]


MASKS = {name:[] for name in BUTTON_CLASSES}
for _code in range(256):
    _mask=sum(bit for i,bit in enumerate(selected_bits('stock-gameplay')) if _code&(1<<i))
    MASKS[button_class(_mask)].append(_code)


def permutation(ordinal, size, seed, key):
    """Seeded affine bijection, constant memory, for this declared finite stratum."""
    if not 0<=ordinal<size: raise ValueError('Sampling stratum exhausted')
    raw=bytes.fromhex(digest([seed,key]))
    stride=int.from_bytes(raw[:8],'little')%size or 1
    while math.gcd(stride,size)!=1: stride=(stride+1)%size or 1
    return (ordinal*stride+int.from_bytes(raw[8:16],'little'))%size


def sampled_input(serial, seed, key, a_mode):
    # Coprime cycles visit all 7x9 class pairs once per 63 draws, while
    # short prefixes already span every stick rectangle and button class.
    category=BUTTON_CLASSES[serial%len(BUTTON_CLASSES)]; rectangle=serial%9
    ordinal=serial//(9*len(BUTTON_CLASSES))
    x0,x1,y0,y1=RECTS[rectangle]; width=x1-x0+1; height=y1-y0+1
    masks=MASKS[category]; size=width*height*len(masks)
    point=permutation(ordinal,size,seed,[key,category,rectangle])
    mask_id,point=divmod(point,width*height); x,y=divmod(point,height)
    index=masks[mask_id]*65536+(x+x0+128)*256+y+y0+128
    return index,decode_input(index,a_mode,'stock-gameplay'),category,rectangle


def initial_aux():
    return dict(fresh=0,expansions=0,archive=[],updates=0,deepest=0)


def bucket(entry):
    p=entry['patch']; first=entry['controls'][0]
    return (entry['depth'],entry['family'],p['movement'][1],p['display'][1],button_class(first['buttons']))


def retain(entries, limit):
    # Four places reserved for shorter branches. Diversity is a retention
    # preference, not a merge: every chosen entry keeps its own exact recipe.
    chosen=[]; buckets=set()
    short=[e for e in entries if e['depth']==1]
    for e in reversed(short):
        if bucket(e) not in buckets:
            chosen.append(e); buckets.add(bucket(e))
        if len(chosen)>=max(1,min(4,limit//3)): break
    if len(chosen)>=limit: return sorted(chosen,key=lambda e:e['id'])
    for e in sorted(entries,key=lambda e:(e['depth'],e['id']),reverse=True):
        if e['id'] not in {x['id'] for x in chosen} and bucket(e) not in buckets:
            chosen.append(e); buckets.add(bucket(e))
        if len(chosen)==limit: return sorted(chosen,key=lambda e:e['id'])
    for e in sorted(entries,key=lambda e:(e['depth'],e['id']),reverse=True):
        if e['id'] not in {x['id'] for x in chosen}: chosen.append(e)
        if len(chosen)==limit: break
    return sorted(chosen,key=lambda e:e['id'])


def next_ticket(aux, signature):
    recipes=signature['jobOrder']; depth=signature['depth']
    eligible=[e for e in aux['archive'] if e['depth']<depth]
    extend=bool(eligible) and signature['scheduler']=='scattershot' and (aux['fresh']+aux['expansions'])%2==1
    if not extend:
        n=aux['fresh']; recipe=n%len(recipes); serial=n//len(recipes)
        return dict(kind='fresh',recipe=recipe,serial=serial,parent=None)
    eligible.sort(key=lambda e:(e['depth'],e['id']),reverse=True)
    # Every fourth expansion explores the shortest retained branches.
    pool=sorted(eligible,key=lambda e:(e['depth'],e['id'])) if aux['expansions']%4==3 else eligible
    parent=pool[(aux['expansions']//4)%len(pool)]
    return dict(kind='extend',recipe=0,serial=parent['attempts'],parent=parent['id'])


def advance_aux(aux, record, signature):
    result=json.loads(json.dumps(aux)); detail=record['detail']; ticket=detail['ticket']
    if ticket!=next_ticket(aux,signature): raise ValueError('Scheduler ticket skips/repeats a proposal')
    candidate=proposal(aux,signature)
    if (detail['proposal']!=candidate or record['jobId']!=candidate['jobId']
            or record['inputIndex']!=candidate['inputIndex']):
        raise ValueError('Proposal differs from seeded inverse schedule')
    if record['status']=='incomplete-budget':
        result['updates']+=detail['updates']
        return result  # cursor is an attempt ID; unfinished proposal remains next
    if ticket['kind']=='fresh': result['fresh']+=1
    else:
        result['expansions']+=1
        next(e for e in result['archive'] if e['id']==ticket['parent'])['attempts']+=1
    updates=detail['updates']
    if type(updates) is not int or not 1<=updates<=signature['depth']+23:
        raise ValueError('Invalid game-update accounting')
    result['updates']+=updates
    if record['status']=='accepted-projection':
        entry=detail['entry']
        if entry['id']!=record['case'] or entry['depth']!=len(entry['controls']):
            raise ValueError('Invalid retained recipe identity/suffix')
        result['deepest']=max(result['deepest'],entry['depth'])
        result['archive']=retain(result['archive']+[entry],signature['archiveLimit'])
    return result


class ScatterCodec:
    name='scattershot-recipes-gzip-v1'
    def __init__(self,signature): self.signature=signature
    def encode(self,r):
        return [r['case'],r['jobId'],r['inputIndex'],STATUSES.index(r['status']),r['detail']]
    def decode(self,row):
        if (not isinstance(row,list) or len(row)!=5 or any(type(x) is not int for x in row[:4])
                or not 0<=row[1]<len(self.signature['jobOrder']) or not 0<=row[3]<len(STATUSES)):
            raise ValueError('Invalid scattershot record')
        case,job,index,status,detail=row
        return dict(case=case,jobId=job,inputIndex=index,status=STATUSES[status],detail=detail,
                    setup=self.signature['jobOrder'][job]['setup'])


def validate_record(signature):
    def validate(r,cursor):
        if r['case']!=cursor or r['status'] not in STATUSES or not 0<=r['jobId']<len(signature['jobOrder']):
            raise ValueError('Invalid scattershot trial cursor/status')
        if r['setup']!=signature['jobOrder'][r['jobId']]['setup']:
            raise ValueError('Scattershot setup differs')
        decode_input(r['inputIndex'],signature['aMode'],'stock-gameplay')
    return validate


def controls_from(records):
    return [Input(r['buttons'],*r['stick']) for r in records]


def continuous(backend, context, patch, controls, checkpoints, targets, endpoints, a_mode,
               retention_control=Input(), tick=None, update_limit=None, exact_parent=True):
    """One restore+patch, complete suffix, then 23 unpatched retention updates.

    No intermediate restores/patches. Parent checkpoints compare every named
    observation; endpoint predicates stay distinct. No full-memory equality.
    """
    tick=tick or (lambda: None)
    backend.restore(context); backend.patch(patch); earlier=backend.capture()
    updates=0; samples=[]; parent_comparisons=[]; last_start=None
    def advance(c):
        nonlocal updates
        if update_limit is not None and updates>=update_limit:
            raise GameBudgetReached(updates)
        frame=backend.frame(); timer=backend.game.read('gGlobalTimer')
        tick(); backend.advance(c); updates+=1
        if backend.frame()!=frame+1 or backend.game.read('gGlobalTimer')!=timer+1:
            raise RuntimeError('Unexpected native update boundary')
        if backend.game.read('gCurrAreaIndex')==1:
            o=backend.observe()
        else:
            g=backend.game
            o=dict(area=g.read('gCurrAreaIndex'),movement=[bits(v) for v in g.read('gMarioState.pos')],
                   platform=backend.observer.slot(g.read('gMarioPlatform')),
                   buttonDown=g.read('gControllers[0].buttonDown'),buttonPressed=g.read('gControllers[0].buttonPressed'))
        if bool(o['buttonDown']&A_BUTTON)!=(a_mode=='held') or o['buttonPressed']&A_BUTTON:
            return o,False
        return o,True
    for i,c in enumerate(controls):
        last_start=earlier.observation if not samples else samples[-1]
        actual,a_valid=advance(c)
        if not a_valid: return dict(status='rejected-a-history',updates=updates,reason='A edge/history'),None
        if i<len(checkpoints):
            diff=differences(actual,checkpoints[i],tuple(checkpoints[i]))
            parent_comparisons.append(dict(update=i+1,differences=diff))
            if diff and exact_parent:
                return dict(status='rejected',updates=updates,stage='parent',differences=diff),None
        samples.append(actual)
    if actual.get('area') != 1:
        return dict(status='rejected-event',updates=updates,stage='departed-before-installation',
                    parentComparisons=parent_comparisons),None
    events=[e for e in backend.game.frame_log() if e['type']=='FLT_EXECUTE_ACTION' and e['action']==DISAPPEARED]
    decisions={}
    entry_start=(checkpoints[-1] if checkpoints else patch) if exact_parent else last_start
    for name,target in targets.items():
        diff=differences(actual,endpoints[name],END_FIELDS)
        event_ok=len(events)==1 and [bits(v) for v in events[0]['pos']]==target['movement']
        # The native log exposes movement only. Preserve the distinct intended
        # raw/display requirements under an EXPLICIT pending prefix contract;
        # never silently treat Variant and Hybrid as the same full checkpoint.
        required={key:target[key] for key in ('collision','display') if key in target}
        prefix_matches=all(entry_start.get(key)==value for key,value in required.items())
        decisions[name]=dict(status='rejected' if diff else (
                             'accepted-projection' if event_ok and prefix_matches else 'rejected-event'),
                             differences=diff,eventMatches=event_ok,requiredEntryRecords=required,
                             conditionalPrefixMatches=prefix_matches,
                             pending='Raw/display preservation to accepted return is source-guided, '
                                 'not independently observed by Wafel for this input.')
    good=[n for n,d in decisions.items() if d['status']=='accepted-projection']
    if not good:
        status='rejected' if all(d['status']=='rejected' for d in decisions.values()) else 'rejected-event'
        return dict(status=status,updates=updates,targets=decisions,
                    parentComparisons=parent_comparisons),None
    event_words=[bits(v) for v in events[0]['pos']]
    retained=True; area2=False; first_apply=None; area2_platform=None
    for i in range(23):
        o,a_valid=advance(retention_control)
        if not a_valid: return dict(status='rejected-a-history',updates=updates,stage='retention'),None
        if o['area']==1 and o['platform']!=61: retained=False
        if o['area']==2 and first_apply is None:
            first_apply=o['movement']; area2_platform=o['platform']
            entries=[e for e in backend.game.frame_log() if e['type']=='FLT_EXECUTE_ACTION']
            area2=(first_apply==FIRST_APPLY and len(entries)==1
                   and [bits(v) for v in entries[0]['pos']]==FIRST_APPLY)
    if not retained or not area2:
        return dict(status='rejected-event',updates=updates,stage='retention',targets=decisions,
                    retained=retained,firstArea2=first_apply,parentComparisons=parent_comparisons),None
    return dict(status='accepted-projection',updates=updates,targets=decisions,matched=good,
                eventWords=event_words,retained=retained,firstArea2=first_apply,
                firstArea2PlatformAfterUpdate=area2_platform,
                observations=samples,parentComparisons=parent_comparisons),earlier


def make_scene(depth,a_mode,check,predecessor_menu='legacy'):
    if predecessor_menu=='contact-approach':
        from contact_predecessors import ContactBackend
        backend_type=ContactBackend
    else: backend_type=Backend
    b=backend_type(create_game(),None); b.observer=Observer(b.game)
    c=Input(A_BUTTON if a_mode=='held' else 0); presses=[]
    contexts=prepare(b,load_capture(RUNTIME/'capture.bKv95w/inputs.jsonl'),depth,c,presses,check)
    endpoints={}; targets={}; recipes=[]; seen={}
    for name in NAMES:
        check(); target,fixture=specification(name); targets[name]=target
        b.restore(contexts[-1]); b.patch(fixture); b.advance(c)
        endpoints[name]=b.observe()
        for move in pose_templates(target):
            key=digest(move.patch)
            if key in seen:
                recipes[seen[key]]['targets'].append(name)
            else:
                seen[key]=len(recipes)
                recipes.append(dict(setup=name,move=move.name,patch=move.patch,targets=[name],
                                    family='pre-action-retry' if number(move.patch['movement'][1])<1202 else 'first-floor-query'))
    return b,contexts,targets,endpoints,recipes,c,presses


@lru_cache(maxsize=48)
def earlier_menu(observation_json, profile):
    target=json.loads(observation_json)
    if profile=='contact-approach':
        from contact_predecessors import contact_templates
        return tuple(contact_templates(target, previous_templates(target)))
    menus=[]; seen=set()
    for move in previous_templates(target):
        identity=digest(move.patch)
        if identity not in seen:
            seen.add(identity); menus.append(move)
    menus=menus[::3]+menus[1::3]+menus[2::3]
    groups=[[m for m in menus if m.name.startswith(prefix)] for prefix in ('ground','freefall','dialog')]
    return tuple(group[i] for i in range(max(map(len,groups))) for group in groups if i<len(group))


def proposal(aux,signature):
    ticket=next_ticket(aux,signature)
    if ticket['kind']=='fresh':
        recipe=signature['jobOrder'][ticket['recipe']]
        serial=ticket['serial']; key=['fresh',ticket['recipe']]
        patch=recipe['patch']; checkpoints=[]; suffix=[]; targets=recipe['targets']; depth=1
        family=recipe['family']; move=recipe['move']
    else:
        parent=next(e for e in aux['archive'] if e['id']==ticket['parent'])
        # Interleave ground, freefall and dialog rather than exhausting ground.
        interleaved=earlier_menu(json.dumps(parent['observation'],sort_keys=True),
                                signature.get('predecessorMenu','legacy'))
        candidate=interleaved[ticket['serial']%len(interleaved)]
        serial=ticket['serial']//len(interleaved); key=['extend',parent['id'],candidate.name]
        patch=candidate.patch; checkpoints=[parent['observation']]+parent['checkpoints']
        suffix=parent['controls']; targets=parent['targets']; depth=parent['depth']+1
        family=candidate.name.split('-')[0]; move=candidate.name
    index,control,category,rectangle=sampled_input(serial,signature['seed'],key,signature['aMode'])
    return dict(ticket=ticket,jobId=ticket['recipe'],inputIndex=index,patch=patch,
                controls=[control.record()]+suffix,checkpoints=checkpoints,targets=targets,
                depth=depth,family=family,move=move,buttonClass=category,stickRectangle=rectangle)


def verify_recipe_sources(signature,check):
    expected=signature['sourceHashes']
    for name,digest_ in expected.items():
        if hash_file(ROOT/name,check)!=digest_: raise ValueError('Reconstruction source changed: '+name)


def open_store(root,signature,resume=False,verify='full',check=None,read_only=False,chunk_records=50,fault=None):
    return ChunkLedger(root,signature,signature['maxTrials'],validate_record(signature),resume=resume,
        verify=verify,chunk_records=chunk_records,codec=ScatterCodec(signature),check=check,
        reduce_aux=lambda aux,r:advance_aux(aux,r,signature),read_only=read_only,fault=fault)


def run(args):
    limits=WorkLimits(args.setup_seconds,args.verification_seconds,args.search_seconds,args.wall_seconds)
    root=args.output.with_suffix('.ledger'); s=None; result=None
    phase=time.perf_counter(); preparation_updates=0
    try:
        limits.check()
        profile=getattr(args,'predecessor_menu','legacy')
        b,contexts,targets,endpoints,recipes,neutral,presses=make_scene(args.depth,args.a_mode,limits.check,profile)
        preparation_updates=contexts[-1].frame+3
        names=('reverse_scattershot.py','chunk_ledger.py','work_limits.py','search.py','product_sweep.py',
               'controller_inputs.py','compact_store.py')
        if profile!='legacy': names=names+('contact_predecessors.py',)
        sources={str(Path('instrumentation/concrete-ink-backward')/n).replace('\\','/'):hash_file(Path(__file__).with_name(n),limits.check) for n in names}
        for n in ('replay.py','backward_wafel.py','backward_validation.py'):
            sources['instrumentation/wafel-jp-pilot/'+n]=hash_file(ROOT/'instrumentation/wafel-jp-pilot'/n,limits.check)
        if profile!='legacy':
            for stem in ('mario', 'mario_actions_moving', 'mario_actions_airborne',
                         'mario_actions_cutscene', 'interaction'):
                for region in ('us','jp'):
                    name='generated/'+region+'_'+stem+'.v'
                    sources[name]=hash_file(ROOT/name,limits.check)
                name='../../../reference-sm64-decomp/src/game/'+stem+'.c'
                sources[name]=hash_file(ROOT/name,limits.check)
        for name,path in (('build/wafel-pilot/sm64_jp.dll',RUNTIME/'sm64_jp.dll'),
                          ('build/wafel-pilot/capture.bKv95w/inputs.jsonl',RUNTIME/'capture.bKv95w/inputs.jsonl')):
            sources[name]=hash_file(path,limits.check)
        signature=dict(seed=args.seed,scheduler=args.scheduler,depth=args.depth,archiveLimit=args.archive,
                       maxTrials=args.max_trials,jobOrder=recipes,order='seeded-strata-v1',aMode=args.a_mode,
                       sourceHashes=sources,initialAux=initial_aux(),contextFrames=[c.frame for c in contexts],
                       endpoints=endpoints,targets=targets,reconstruction='pinned-init-capture360-pillar4-neutral-to131-v1')
        signature['predecessorMenu']=profile
        signature['parentPolicy']='exact-observation' if profile=='legacy' else 'diagnose-and-replay-actual-suffix'
        signature['entryRecordContract']=('For this IDLE installation menu, raw/display records at accepted warp '
            'return equal those at the start of the installation update (the last parent checkpoint for an '
            'extension). This is an explicit unproved per-input prefix frame; the native event directly '
            'observes movement only. Earlier proposals are not required to inherit those records.')
        signature.update(python=platform.python_version(),wafel=version('wafel'),architecture=platform.machine())
        signature['retentionSuffix']=dict(input=neutral.record(),updates=23)
        limits.enter('verification')
        s=open_store(root,signature,args.resume,args.resume_verify,limits.check,chunk_records=args.chunk_records)
        # Reconstruct complete native snapshots; check all archived observations.
        live={}
        for e in s.state['aux']['archive']:
            limits.check(); b.restore(contexts[-e['depth']]); b.patch(e['patch']); snap=b.capture()
            if snap.observation!=e['observation'] or snap.frame!=e['frame']:
                raise ValueError('Retained full-context reconstruction differs')
            live[e['id']]=snap
        start_cursor=s.state['nextCase']; start_updates=s.state['aux']['updates']
        limits.enter('search'); s.check=lambda:None
        stop='trial-limit'; tested_inputs=Counter(); proposals=Counter(); target_counts=Counter()
        distinct=set(); incomplete=0
        coherent_witnesses=[]; runtime_snapshot_peak=len(live)
        parent_mismatches=Counter(); extension_successes=[]
        while s.state['nextCase']<args.max_trials:
            if s.state['nextCase']-start_cursor>=args.trials: break
            try: limits.check()
            except LimitReached: stop='search-or-wall-limit'; break
            remaining=args.game_updates-(s.state['aux']['updates']-start_updates)
            if remaining<=0: stop='game-update-budget'; break
            candidate=proposal(s.state['aux'],signature)
            names=candidate['targets']; expected={n:targets[n] for n in names}
            try:
                report,snapshot=continuous(b,contexts[-candidate['depth']],candidate['patch'],
                    controls_from(candidate['controls']),candidate['checkpoints'],expected,endpoints,args.a_mode,
                    neutral,update_limit=remaining,exact_parent=profile=='legacy')
            except GameBudgetReached as exc:
                report=dict(status='incomplete-budget',updates=exc.updates,
                            reason='Native update limit; no gameplay verdict; retry this proposal on resume')
                snapshot=None; incomplete+=1
            if report['status']!='incomplete-budget':
                distinct.add(digest([contexts[-candidate['depth']].frame,candidate['patch'],candidate['controls']]))
            entry=None
            if snapshot is not None:
                entry=dict(id=s.state['nextCase'],frame=snapshot.frame,depth=candidate['depth'],
                           patch=candidate['patch'],controls=candidate['controls'],
                           checkpoints=(report['observations'][:-1] if profile!='legacy' else candidate['checkpoints']),
                           targets=report['matched'],observation=snapshot.observation,family=candidate['family'],
                           move=candidate['move'],attempts=0,parent=candidate['ticket']['parent'],
                           provenance='supplied conditional earliest pose; suffix controller-replayed')
                # End-of-update copies can erase an intermediate split. Classify
                # the earliest seed, not the absence of a split at frame end.
                before=snapshot.observation
                synced=before['movement']==before['collision']==before['display']
                entry['initialRecordsSynchronized']=synced
                if synced: coherent_witnesses.append(entry['id'])
                if entry['depth']>1: extension_successes.append(entry['id'])
            for comparison in report.get('parentComparisons',[]):
                parent_mismatches.update(comparison['differences'].keys())
            detail={k:v for k,v in report.items() if k not in ('status','observations')}
            detail.update(ticket=candidate['ticket'],proposal=candidate,entry=entry)
            record=dict(case=s.state['nextCase'],jobId=candidate['jobId'],inputIndex=candidate['inputIndex'],
                        setup=recipes[candidate['jobId']]['setup'],status=report['status'],detail=detail)
            s.append(record)
            if entry:
                live[entry['id']]=snapshot
            kept={e['id'] for e in s.state['aux']['archive']}; live={key:value for key,value in live.items() if key in kept}
            runtime_snapshot_peak=max(runtime_snapshot_peak,len(live))
            proposals[candidate['family']]+=1; tested_inputs[candidate['buttonClass']]+=1
            for name,d in report.get('targets',{}).items(): target_counts[name+':'+d['status']]+=1
            if s.ready():
                limits.enter('checkpoint'); s.commit(); limits.enter('search')
                if getattr(args,'progress',False):
                    print(json.dumps(dict(progress=True,attempts=s.state['nextCase'],
                        searchSeconds=limits.phases['search'],updates=s.state['aux']['updates'],
                        deepest=s.state['aux']['deepest'],extendedAccepted=len(extension_successes))),flush=True)
            if incomplete: stop='game-update-budget'; break
        limits.enter('checkpoint'); s.commit(); limits.enter('finalization')
        aux=s.state['aux']
        result=dict(schema=1,status=stop,seed=args.seed,scheduler=args.scheduler,
            batchTrials=s.state['nextCase']-start_cursor,completedTrials=s.state['nextCase']-start_cursor-incomplete,
            incompleteBudgetAttempts=incomplete,distinctTestedCombinations=len(distinct),
            nextCase=s.state['nextCase'],batchGameUpdates=aux['updates']-start_updates,
            preparationGameUpdates=preparation_updates,counts=s.state['counts'],targetEvaluations=dict(target_counts),
            reusedPredicates=sum(len(r['targets'])-1 for r in recipes),poseRecipes=len(recipes),
            proposalFamilies=dict(proposals),buttonClasses=dict(tested_inputs),archive=aux['archive'],
            distinctRetainedBuckets=len({bucket(e) for e in aux['archive']}),nativeSnapshotsPeak=runtime_snapshot_peak,
            deepestValidatedUpdates=aux['deepest'],acceptedFromSynchronizedRecords=coherent_witnesses,
            acceptedExtendedSuffixes=extension_successes,parentMismatchFieldCounts=dict(parent_mismatches),
            splitClassification='List accepted Ink suffixes whose earliest movement/collision/display records '
                'all agreed. An empty list means no such witness in this sample; end-of-update agreement '
                'does not disprove a within-update split. Other seed fields and the scene remain conditional.',
            integrity=dict(verification=args.resume_verify if args.resume else 'new',
                           fullHistoryVerified=not args.resume or args.resume_verify=='full'),
            ledger=dict(path=str(root),format='compact-gzip-v3',io=s.io,generation=s.generation,commitSha256=s.commit_sha),
            signature=signature,peakRssBytes=peak_rss_bytes(),preparationAPresses=presses,
            generators='Target-derived pre-action retry/first-query poses, ground copy/sink, four-quarter freefall '
                       'arithmetic, final automatic-dialog sink. Missing horizontal/support/rotation inverses, '
                       'other actions and writers, and a controller-reached predecessor context.',
            matching='Every stored parent observation, distinct endpoint END_FIELDS, exact ACT_DISAPPEARED '
                     'movement event, top platform persistence in Area 1 and first Area-2 action-entry displacement. '
                     'The pointer may clear later in that Area-2 update. Collision/display at '
                     'accepted return are conditional on the explicit entry-record contract and separate '
                     'emulator fixtures; no per-input observation or full-memory equality.',
            reachability='All earliest poses and pillar completion supplied conditionally. No patch-free no-A route '
                         'or mechanism impossibility follows from this finite menu/sample.')
        if profile!='legacy':
            result['generators']=('Legacy vertical proposals plus target-derived collision offsets, '
                'horizontal walking/air target-minus-speed proposals, and stock intangible message states. '
                'Moving support/rotation, other writers/actions and controller-reached scene contexts remain absent.')
            result['matching']=('Unequal saved parents are diagnosed, never substituted. Replay uses the actual '
                'continuous suffix and archives its actual intermediate observations. Acceptance still requires '
                'the selected within-update movement event, distinct raw/display start requirements under '
                'the explicit per-input prefix condition, the original top and the checked first Area-2 payoff.')
    except LimitReached as exc:
        result=dict(status='verification incomplete' if exc.phase=='verification' else 'setup incomplete',
                    batchTrials=0,batchGameUpdates=0)
    finally:
        if s: s.close()
    result['timing']=limits.finish()
    result['timing']['searchCheckBoundary']=('Between complete candidate replays, at most depth+23 native updates. '
        'The game-update budget is checked before each individual update.')
    result['totalStoredBytes']=sum(f.stat().st_size for f in root.rglob('*') if f.is_file()) if root.exists() else 0
    atomic_json(args.output.with_suffix('.attempt-limit.json') if result['status'].endswith('incomplete') else args.output,result)
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seed',type=int,default=20261003)
    p.add_argument('--scheduler',choices=('scattershot','menu-first'),default='scattershot')
    p.add_argument('--depth',type=int,choices=range(1,31),default=3)
    p.add_argument('--predecessor-menu',choices=('legacy','contact-approach'),default='legacy')
    p.add_argument('--progress',action='store_true')
    p.add_argument('--archive',type=int,default=12)
    p.add_argument('--game-updates',type=int,default=2000)
    p.add_argument('--trials',type=int,default=2000)
    p.add_argument('--max-trials',type=int,default=5000)
    p.add_argument('--chunk-records',type=int,default=50)
    p.add_argument('--a-mode',choices=('released','held'),default='released')
    p.add_argument('--setup-seconds',type=float,default=30)
    p.add_argument('--verification-seconds',type=float,default=30)
    p.add_argument('--search-seconds',type=float,default=30)
    p.add_argument('--wall-seconds',type=float,default=90)
    p.add_argument('--resume',action='store_true')
    p.add_argument('--resume-verify',choices=('full','latest'),default='full')
    p.add_argument('--audit',action='store_true',help='Offline full-history audit; constructs no game')
    args=p.parse_args()
    if not 4<=args.archive<=24 or not 1<=args.trials<=args.max_trials<=1000000 or args.game_updates<1:
        p.error('Bounded limits: archive 4..24, at most 1000000 trials, positive update budget')
    if args.audit:
        root=args.output.with_suffix('.ledger')
        signature=json.loads((root/'manifest.json').read_text())['payload']['signature']
        limits=WorkLimits(verification=args.verification_seconds,overall=args.wall_seconds);limits.enter('verification')
        try:
            with open_store(root,signature,True,'full',limits.check,True,args.chunk_records) as s:
                result=dict(status='full-audit-passed',verifiedAttempts=s.state['nextCase'],io=s.io,timing=limits.finish())
        except LimitReached:
            result=dict(status='verification incomplete',timing=limits.finish())
        print(json.dumps(result));return
    result=run(args)
    print(json.dumps({k:result[k] for k in ('status','batchTrials','batchGameUpdates','deepestValidatedUpdates',
                                          'distinctRetainedBuckets','timing') if k in result}))


if __name__=='__main__': main()
