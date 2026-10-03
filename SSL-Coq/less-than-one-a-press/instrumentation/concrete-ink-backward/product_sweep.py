"""Resumable one-update predecessor counts over the full encoded input product.

Real Wafel updates; no SMT, representative equivalence, or forward input tree.
Prepared candidate states cache the same initial context-plus-patch operation.
Matches cover only the explicitly selected projection and action-entry event.
"""
import argparse
from collections import Counter
from dataclasses import replace
import hashlib
import json
import math
from pathlib import Path
import sys
import time
import platform
from importlib.metadata import version

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chunk_ledger import ChunkLedger, STATUSES, atomic_json
from search import (A_BUTTON, Backend, DISAPPEARED, END_FIELDS, Input, Observer,
                    ROOT, RUNTIME, accepted_target, bits, create_game, differences,
                    installation_templates, load_capture, prepare, replay,
                    target_fixture)
from controller_inputs import NON_A_BITS

INPUTS = 1 << 29
NAMES = ('original', 'variant', 'hybrid')
GATED_MASK = 0x0f20  # L plus all four D-pad bits, excluded at the user's request.
INPUT_STRIDE = 13254001  # Odd: invertible on either power-of-two domain.


def ordered_input(index, buttons_mode, order):
    count = input_count(buttons_mode)
    if not 0 <= index < count:
        raise ValueError('Input ordinal outside product')
    if order == 'linear':
        return index
    if order != 'mixed' or math.gcd(INPUT_STRIDE, count) != 1:
        raise ValueError('Input order is not a bijection')
    return (index * INPUT_STRIDE) % count


def selected_bits(buttons_mode):
    if buttons_mode == 'all-non-a':
        return NON_A_BITS
    if buttons_mode == 'stock-gameplay':
        return tuple(bit for bit in NON_A_BITS if not bit & GATED_MASK)
    raise ValueError('Unknown button mode')


def input_count(buttons_mode):
    return 65536 * (1 << len(selected_bits(buttons_mode)))


def decode_input(index, a_mode, buttons_mode='all-non-a'):
    if not 0 <= index < input_count(buttons_mode):
        raise ValueError('Input index outside complete product')
    mask_id, stick_id = divmod(index, 65536)
    buttons = sum(bit for i, bit in enumerate(selected_bits(buttons_mode)) if mask_id & (1 << i))
    if a_mode == 'held':
        buttons |= A_BUTTON
    elif a_mode != 'released':
        raise ValueError('Unknown A mode')
    return Input(buttons, stick_id // 256 - 128, stick_id % 256 - 128)


def specification(name):
    if name == 'original':
        target = accepted_target('raised-display')
        fixture = target_fixture(target)
    elif name == 'variant':
        target = accepted_target('low-display')
        fixture = target_fixture(target)
    elif name == 'hybrid':
        target = accepted_target('low-display')
        target['display'] = accepted_target('raised-display')['display']
        fixture = target_fixture(target)
        fixture['movement'] = list(target['movement'])
    else:
        raise ValueError('Unknown setup')
    return target, fixture


def pose_templates(target):
    seen = set()
    for move in installation_templates(target):
        key = json.dumps(move.patch, sort_keys=True)
        if key not in seen:
            seen.add(key)
            yield move


def projection(backend):
    g = backend.game
    read = g.read
    return dict(movement=[bits(v) for v in read('gMarioState.pos')],
                collision=[bits(read('gMarioObject.oPos' + axis)) for axis in 'XYZ'],
                display=[bits(v) for v in read('gMarioObject.header.gfx.pos')],
                action=read('gMarioState.action'),
                depth=bits(read('gMarioState.quicksandDepth')),
                actionArg=read('gMarioState.actionArg'),
                usedSlot=backend.observer.slot(read('gMarioState.usedObj')),
                floorHeight=bits(read('gMarioState.floorHeight')),
                floorOwner=backend.observer.slot(read('gMarioState.floor?.object')),
                platform=backend.observer.slot(read('gMarioPlatform')))


def cached_trial(job, control, details=False):
    b = job['backend']
    b.load_state(job['predecessor'].state)
    if b.frame() != job['predecessor'].frame:
        raise RuntimeError('Cached predecessor frame mismatch')
    b.advance(control)
    if b.frame() != job['predecessor'].frame + 1 or b.game.read('gGlobalTimer') != job['timer'] + 1:
        raise RuntimeError('Update boundary mismatch')
    actual = projection(b)
    down = b.game.read('gControllers[0].buttonDown')
    pressed = b.game.read('gControllers[0].buttonPressed')
    if bool(down & A_BUTTON) != (job['aMode'] == 'held') or pressed & A_BUTTON:
        return 'rejected-a-history', {'buttonDown':down, 'buttonPressed':pressed}
    diff = differences(actual, job['endpoint'].observation, END_FIELDS)
    if diff:
        return 'rejected', diff if details else None
    events = [e for e in b.game.frame_log()
              if e['type'] == 'FLT_EXECUTE_ACTION' and e['action'] == DISAPPEARED]
    if len(events) != 1 or [bits(v) for v in events[0]['pos']] != job['accepted']['movement']:
        return 'rejected-event', events if details else None
    return 'accepted-projection', actual if details else None


def make_jobs(a_mode, buttons_mode):
    started = time.perf_counter()
    b = Backend(create_game(), None)
    b.observer = Observer(b.game)
    presses = []
    control = Input(A_BUTTON if a_mode == 'held' else 0)
    context = prepare(b, load_capture(RUNTIME/'capture.bKv95w/inputs.jsonl'), 1, control, presses)[0]
    jobs = []
    controls = []
    for name in NAMES:
        accepted, fixture = specification(name)
        b.restore(context)
        b.patch(fixture)
        b.advance(control)
        endpoint = b.capture()
        events = [e for e in b.game.frame_log() if e['type']=='FLT_EXECUTE_ACTION' and e['action']==DISAPPEARED]
        if len(events)!=1 or [bits(v) for v in events[0]['pos']]!=accepted['movement']:
            raise RuntimeError('Setup recognition control failed: '+name)
        if endpoint.observation['platform']!=61 or endpoint.observation['floorOwner']!=61:
            raise RuntimeError('Setup top capture failed: '+name)
        retained = False
        for _ in range(23):
            b.advance(control)
            if b.game.read('gCurrAreaIndex')==2 and [bits(v) for v in b.game.read('gMarioState.pos')]==[
                    bits(365.5927734375),bits(5500.),bits(-1096.8026123046875)]:
                retained = True
        if not retained:
            raise RuntimeError('First Area-2 apply control failed: '+name)
        controls.append(dict(setup=name,fixture=fixture,accepted=accepted,endpoint=endpoint.observation,
                             retainedFirstArea2Apply=retained))
        for move in pose_templates(accepted):
            b.restore(context)
            b.patch(move.patch)
            predecessor = b.capture()
            jobs.append(dict(setup=name,move=move,backend=b,context=context,
                             predecessor=predecessor,endpoint=endpoint,accepted=accepted,
                             timer=predecessor.observation['timer'],aMode=a_mode))
    metadata=dict(aMode=a_mode,frame=context.frame,preparationAPresses=presses,
                  buttonDown=context.observation['buttonDown'],recognitionControls=controls,
                  preparationSeconds=time.perf_counter()-started,
                  poseCounts=dict(Counter(j['setup'] for j in jobs)),
                  inputSpace=dict(stickPairs=65536,nonAMasks=1<<len(selected_bits(buttons_mode)),
                                  choicesPerPose=input_count(buttons_mode),buttonsMode=buttons_mode,
                                  gatedMask=GATED_MASK if buttons_mode=='stock-gameplay' else 0,
                                  gating='L and D-pad excluded by user-selected scope, not a proved equivalence'),
                  totalCases=input_count(buttons_mode)*len(jobs),
                  jobOrder=[dict(setup=j['setup'],move=j['move'].name,patch=j['move'].patch) for j in jobs])
    return jobs, metadata


def compare_reference(jobs):
    controls = (Input(),Input(0x1000,13,-27),Input(0x7f3f,-128,127),Input(0x400f,127,-128))
    comparisons = 0
    for job in jobs:
        b = job['backend']
        for c in controls:
            if job['aMode']=='held':
                c=Input(c.buttons|A_BUTTON,c.x,c.y)
            fast,_=cached_trial(job,c)
            move=replace(job['move'],control=c)
            reference,_=replay(b,job['context'],move,[job['endpoint']],[c],
                               job['accepted']['movement'],held_a=job['aMode']=='held')
            if fast!=reference['status']:
                raise RuntimeError('Cached/reference disagreement: '+job['setup']+'/'+job['move'].name)
            comparisons += 1
    return comparisons


def atomic_write(path, report):
    atomic_json(path,report)


def hash_file(path):
    digest=hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda:source.read(65536),b''):
            digest.update(block)
    return digest.hexdigest()


def peak_rss_bytes():
    if sys.platform=='win32':
        import ctypes
        from ctypes import wintypes
        class Counters(ctypes.Structure):
            _fields_=[('cb',wintypes.DWORD),('faults',wintypes.DWORD)]+[(n,ctypes.c_size_t) for n in
                ('peakWorkingSet','workingSet','peakPaged','paged','peakNonpaged','nonpaged','pagefile','peakPagefile')]
        counters=Counters(); counters.cb=ctypes.sizeof(counters)
        kernel=ctypes.WinDLL('kernel32'); kernel.GetCurrentProcess.restype=ctypes.c_void_p
        psapi=ctypes.WinDLL('psapi')
        psapi.GetProcessMemoryInfo.argtypes=[ctypes.c_void_p,ctypes.POINTER(Counters),wintypes.DWORD]
        if not psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(),ctypes.byref(counters),counters.cb):
            raise ctypes.WinError()
        return counters.peakWorkingSet
    import resource
    peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak if sys.platform=='darwin' else peak*1024


def resume_counts(old, signature, total_cases):
    if old['signature'] != signature or old['mode'] != 'contiguous-exhaustive-stream':
        raise ValueError('Resume signature or mode differs')
    cursor = old['nextCase']
    counts = {name:Counter(old['counts'][name]) for name in NAMES}
    if not isinstance(cursor, int) or not 0 <= cursor <= total_cases:
        raise ValueError('Invalid resume cursor')
    if any(not isinstance(n, int) or n < 0 for c in counts.values() for n in c.values()):
        raise ValueError('Invalid resume count')
    if sum(sum(c.values()) for c in counts.values()) != cursor:
        raise ValueError('Resume counts do not match cursor')
    return cursor, counts, old['searchSeconds']


def check_ledger(path, old, signature, jobs):
    """Read-only legacy v1 audit. Never used for new checkpoints."""
    if hash_file(path) != old['ledger']['sha256']:
        raise ValueError('Ledger hash differs; preserve it for recovery')
    counts = {name:Counter() for name in NAMES}
    with path.open(encoding='utf-8') as source:
        header = json.loads(next(source))
        if header != {'kind':'manifest','signature':signature}:
            raise ValueError('Ledger signature differs')
        cursor = 0
        for line in source:
            record = json.loads(line)
            ordinal, job_id = divmod(cursor, len(jobs))
            index = ordered_input(ordinal, signature['inputSpace']['buttonsMode'], signature['order'])
            control = decode_input(index, signature['aMode'], signature['inputSpace']['buttonsMode'])
            if (record['case'] != cursor or record['jobId'] != job_id or record['inputIndex'] != index
                    or record['input'] != control.record() or record['setup'] != jobs[job_id]['setup']
                    or record['pose'] != jobs[job_id]['move'].name
                    or record['status'] not in ('accepted-projection','rejected','rejected-event','rejected-a-history')):
                raise ValueError('Ledger case differs from declared enumeration')
            counts[record['setup']][record['status']] += 1
            cursor += 1
    if cursor != old['nextCase'] or {n:dict(c) for n,c in counts.items()} != old['counts']:
        raise ValueError('Ledger counts differ from checkpoint')
    return cursor


def validate_record(signature):
    jobs=signature['jobOrder']
    def validate(record,cursor):
        ordinal,job_id=divmod(cursor,len(jobs))
        index=ordered_input(ordinal,signature['inputSpace']['buttonsMode'],signature['order'])
        control=decode_input(index,signature['aMode'],signature['inputSpace']['buttonsMode'])
        if (record['case']!=cursor or record['jobId']!=job_id or record['inputIndex']!=index
                or record['input']!=control.record() or record['setup']!=jobs[job_id]['setup']
                or record['pose']!=jobs[job_id]['move'] or record['status'] not in STATUSES):
            raise ValueError('Record skips, duplicates or changes the declared enumeration')
    return validate


def audit_output(args):
    """Offline full audit; no game construction and no historical-file rewrite."""
    started=time.perf_counter()
    root=args.output.with_suffix('.ledger')
    if not root.exists():
        old=json.loads(args.output.read_text(encoding='utf-8'))
        from types import SimpleNamespace
        jobs=[dict(setup=j['setup'],move=SimpleNamespace(name=j['move'])) for j in old['signature']['jobOrder']]
        cursor=check_ledger(args.output.with_suffix('.trials.jsonl'),old,old['signature'],jobs)
        return dict(format='legacy-v1',verifiedCases=cursor,wallSeconds=time.perf_counter()-started,
                    readOnly=True,scope='Entire legacy ledger hash, enumeration and counts')
    with (root/'manifest.json').open('rb') as source:
        raw=source.read(262145)
    if len(raw)>262144:
        raise ValueError('Oversize manifest')
    manifest=json.loads(raw)['payload']
    with ChunkLedger(root,manifest['signature'],manifest['totalCases'],validate_record(manifest['signature']),
                     resume=True,verify='full',chunk_records=manifest['chunkRecords'],read_only=True) as store:
        return dict(format='chunk-v2',verifiedCases=store.state['nextCase'],retained=store.state['retained'],
                    wallSeconds=time.perf_counter()-started,io=store.io,peakRssBytes=peak_rss_bytes(),
                    readOnly=True,scope='All committed metadata, trial bytes, exact enumeration, counts and retained recipes; '
                        'uncommitted recovery/pending files are not part of coverage')


def run(args):
    started=time.perf_counter()
    root=args.output.with_suffix('.ledger')
    if args.resume and not root.exists():
        raise ValueError('Chunk checkpoint missing; legacy JSONL is preserved for --audit, not silently migrated')
    if not args.resume and (root.exists() or args.output.exists() or args.output.with_suffix('.trials.jsonl').exists()):
        raise ValueError('Output/ledger already exists; use --resume or a new path')
    if args.resume and args.benchmark:
        raise ValueError('Timing sample cannot resume a coverage stream')
    phases={}
    phase_start=time.perf_counter()
    jobs,meta=make_jobs(args.a_mode,args.buttons)
    phases['preparation']=time.perf_counter()-phase_start
    phase_start=time.perf_counter()
    reference_count=compare_reference(jobs)
    phases['referenceValidation']=time.perf_counter()-phase_start
    phase_start=time.perf_counter()
    hashes={name:hash_file(ROOT/'instrumentation/concrete-ink-backward'/name)
            for name in ('product_sweep.py','chunk_ledger.py','search.py','controller_inputs.py')}
    hashes.update({name:hash_file(ROOT/'instrumentation/wafel-jp-pilot'/name)
                   for name in ('replay.py','backward_wafel.py','backward_validation.py')})
    order='mixed' if args.benchmark else args.order
    signature=dict(aMode=args.a_mode,inputSpace=meta['inputSpace'],sourceHashes=hashes,
                   jobOrder=meta['jobOrder'],order=order,inputStride=INPUT_STRIDE,
                   mode='stratified-timing' if args.benchmark else 'contiguous-exhaustive-stream',
                   python=platform.python_version(),wafel=version('wafel'),architecture=platform.machine())
    signature.update(captureSha256=hash_file(RUNTIME/'capture.bKv95w/inputs.jsonl'),
                     dllSha256=hash_file(RUNTIME/'sm64_jp.dll'),
                     contextFrame=meta['frame'],buttonDown=meta['buttonDown'])
    phases['configuration']=time.perf_counter()-phase_start
    phase_start=time.perf_counter()
    store=ChunkLedger(root,signature,meta['totalCases'],validate_record(signature),resume=args.resume,
                      verify=args.resume_verify,chunk_records=args.chunk_records)
    phases['resumeValidation' if args.resume else 'storeInitialization']=time.perf_counter()-phase_start
    start_cursor=store.state['nextCase']
    recent_samples=[]
    limit=meta['totalCases']
    if args.benchmark:
        limit=min(args.cases,meta['totalCases'])
    phases.update(trials=0.,append=0.,finalization=0.)
    try:
        while store.state['nextCase']<limit and store.state['nextCase']-start_cursor<args.cases and time.perf_counter()-started<args.seconds:
            cursor=store.state['nextCase']
            ordinal,job_id=divmod(cursor,len(jobs))
            index=ordered_input(ordinal,args.buttons,order)
            job=jobs[job_id]
            control=decode_input(index,args.a_mode,args.buttons)
            phase_start=time.perf_counter()
            status,detail=cached_trial(job,control,True)
            phases['trials']+=time.perf_counter()-phase_start
            record=dict(case=cursor,inputIndex=index,jobId=job_id,
                        setup=job['setup'],pose=job['move'].name,input=control.record(),
                        status=status,detail=detail)
            phase_start=time.perf_counter()
            prior_checkpoint=store.io['checkpointSeconds']
            store.append(record)
            phases['append']+=time.perf_counter()-phase_start-(store.io['checkpointSeconds']-prior_checkpoint)
            if len(recent_samples)<12:
                recent_samples.append(record)
            if store.ready():
                store.commit()
        store.commit()
    except BaseException:
        # No error-path checkpoint: a partial append must never advance HEAD.
        # Pending bytes are preserved and quarantined on the next resume.
        store.close()
        raise
    phase_start=time.perf_counter()
    state=store.state
    ledger=dict(format='chunk-v2',path=str(root),generation=store.generation,
                commitSha256=store.commit_sha,retained=state['retained'],io=store.io,
                recovered=store.recovered,archive='Accepted predecessor recipes, not portable Wafel memory dumps')
    store.close()
    phases['finalization']+=time.perf_counter()-phase_start
    phases['checkpoints']=store.io['checkpointSeconds']
    elapsed=time.perf_counter()-started
    cursor=state['nextCase']
    done=cursor==meta['totalCases'] and not args.benchmark
    result=dict(schema=2,status='complete-product' if done else ('timing-sample' if args.benchmark else 'partial-product'),
                complete=done,mode=signature['mode'],order=order,metadata=meta,signature=signature,
                inputsPerPose=input_count(args.buttons),nextCase=cursor,
                unprocessedCases=meta['totalCases']-cursor,counts=state['counts'],sampling=state['sampling'],
                referenceComparisons=reference_count,ledger=ledger,samples=recent_samples,
                phaseSeconds=phases,peakRssBytes=peak_rss_bytes(),
                thisBatch=dict(tested=cursor-start_cursor,seconds=elapsed,
                               casesPerSecond=(cursor-start_cursor)/elapsed if elapsed else 0,
                               timingScope='Whole run including preparation, reference checks, configuration, resume, '
                                           'trial/append/checkpoint/close; final report write and process startup/shutdown '
                                           'are included by the external benchmark wall clock.'),
                integrity=dict(resumeVerification=args.resume_verify if args.resume else 'new-ledger',
                               historicalContentVerified=not args.resume or args.resume_verify=='full',
                               warning='Explicit latest mode trusts older chunk contents; run --audit for complete corruption checks.'
                                       if args.resume and args.resume_verify=='latest' else None),
                coverage='Every tested input uses an actual Wafel update. Unprocessed cases are not classified; '
                         'no sampled equivalence or gameplay-history coverage is claimed.',
                matching='END_FIELDS plus exact movement at ACT_DISAPPEARED entry; not full-state equality.',
                context='Saved normally initialized SSL after supplied pillar completion; conditional pose proposals.',
                aHistory='Held mode has one earlier preparation press; no new A edge during a tested update.')
    atomic_write(args.output,result)  # A convenience receipt, never the transaction authority.
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--a-mode',choices=('released','held'),default='released')
    parser.add_argument('--buttons',choices=('stock-gameplay','all-non-a'),default='stock-gameplay')
    parser.add_argument('--order',choices=('linear','mixed'),default='linear',
                        help='Mixed is an exact permutation, not representative grouping')
    parser.add_argument('--cases',type=int,default=5000)
    parser.add_argument('--seconds',type=float,default=60)
    parser.add_argument('--benchmark',action='store_true')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--resume-verify',choices=('full','latest'),default='full',
                        help='Full detects old payload corruption; explicit latest trusts the historical prefix')
    parser.add_argument('--chunk-records',type=int,default=1000)
    parser.add_argument('--audit',action='store_true',help='Read-only full integrity audit; does not create a game')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.cases<1 or args.seconds<=0 or not 1<=args.chunk_records<=4096:
        parser.error('Positive limits required')
    if args.audit:
        print(json.dumps(audit_output(args)))
        return
    result=run(args)
    print(json.dumps({k:result[k] for k in ('status','complete','inputsPerPose','nextCase',
                                          'unprocessedCases','counts','thisBatch')}))


if __name__=='__main__':
    main()
