"""Audit a stopped concrete run and count actual proposals, not available moves."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json
from reverse_scattershot import open_store, digest
from work_limits import WorkLimits, LimitReached


def summarize(path, seconds=300):
    started = time.perf_counter()
    report = json.loads(path.read_text(encoding='utf8'))
    if report['nextCase'] != report['completedTrials'] or report['incompleteBudgetAttempts']:
        raise ValueError('This summary requires a complete, fresh-run receipt, not a resumed/incomplete batch')
    signature = report['signature']
    root = path.with_suffix('.ledger')
    manifest = json.loads((root/'manifest.json').read_text(encoding='utf8'))['payload']
    limits = WorkLimits(verification=seconds, overall=seconds)
    limits.enter('verification')
    kinds = defaultdict(Counter); families = Counter(); classes = Counter(); rectangles = Counter()
    moves = set(); recipes = set(); combinations = set(); stages = Counter(); targets = Counter()
    fields = Counter(); goal_fields = Counter(); samples = {}; synchronized = 0; earlier_passes = []
    with open_store(root, signature, True, 'full', limits.check, True, manifest['chunkRecords']) as store:
        audit_seconds = time.perf_counter()-started
        assert store.state['nextCase'] == report['nextCase']
        assert store.state['counts'] == report['counts']
        assert store.state['aux']['archive'] == report['archive']
        assert store.state['aux']['updates'] == report['batchGameUpdates']
        for r in store.records():
            limits.check()
            d = r['detail']; p = d['proposal']; kind = d['ticket']['kind']
            kinds[kind][r['status']] += 1
            for target, decision in d.get('targets', {}).items():
                targets[target+':'+decision['status']] += 1
            if kind != 'extend': continue
            families[p['family']] += 1; classes[p['buttonClass']] += 1
            rectangles[str(p['stickRectangle'])] += 1
            moves.add(p['move']); recipes.add(digest(p['patch']))
            combinations.add(digest([p['patch'],p['controls']]))
            synced = p['patch']['movement'] == p['patch']['collision'] == p['patch']['display']
            synchronized += synced
            stages[d.get('stage', 'installation-goal')] += 1
            for comparison in d.get('parentComparisons', []):
                fields.update(comparison['differences'].keys())
            for decision in d.get('targets', {}).values():
                goal_fields.update(decision.get('differences', {}).keys())
            if r['status'] == 'accepted-projection': earlier_passes.append(r['case'])
            if p['family'] not in samples:
                samples[p['family']] = dict(case=r['case'], parent=d['ticket']['parent'],
                    move=p['move'], patch=p['patch'], controls=p['controls'], status=r['status'],
                    stage=d.get('stage'), parentComparisons=d.get('parentComparisons'),
                    targets=d.get('targets'), updates=d['updates'])
        assert sum(sum(c.values()) for c in kinds.values()) == report['completedTrials']
        assert earlier_passes == report['acceptedExtendedSuffixes']
        assert dict(fields) == report['parentMismatchFieldCounts']
        io = dict(store.io)
    result = dict(schema=1, fullAudit='passed', verifiedAttempts=report['nextCase'],
        auditSeconds=audit_seconds, auditAndSummarySeconds=time.perf_counter()-started, auditIO=io,
        kindOutcomes=dict(kinds), extendedFamilies=dict(families), extendedButtonClasses=dict(classes),
        extendedStickRectangles=dict(rectangles), distinctExtendedMoveLabels=len(moves),
        distinctExtendedPoseRecipes=len(recipes), distinctExtendedPatchSuffixes=len(combinations),
        extendedSynchronizedStartingRecords=synchronized, extendedGoalStages=dict(stages),
        parentMismatchFieldCounts=dict(fields), goalMismatchFieldCounts=dict(goal_fields),
        acceptedExtendedSuffixes=earlier_passes, examplesByFamily=samples,
        verificationScope='Every chunk hash, record/cursor/count, retained reference, '
                          'archive and deterministic sampler transition; not a gameplay proof.',
        report=report)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seconds', type=float, default=300)
    args = p.parse_args()
    try: result = summarize(args.report, args.seconds)
    except LimitReached:
        result = dict(status='verification incomplete', gameplayTrials=0)
    atomic_json(args.output, result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('report','examplesByFamily')}))
