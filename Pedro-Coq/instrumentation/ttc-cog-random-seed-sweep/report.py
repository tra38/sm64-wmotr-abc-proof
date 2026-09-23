#!/usr/bin/env python3
"""Verify capture provenance, selection and coverage; export metadata only."""
import collections
import csv
import json
from run import HERE, OUT, PROJECT, FRAME, sha, trace_rows


def observations(trial):
    return [(kind,row) for kind,row in trace_rows(trial/'trace.csv') if kind!='CRNG']


def main():
    survey=PROJECT/'build/cog-placement/random_phase_survey_us'
    rows=observations(survey)
    frames={int(r['rel']):r for kind,r in rows if kind=='CFRAME'}
    cogs=collections.defaultdict(dict)
    for kind,row in rows:
        if kind=='CCOG':cogs[int(row['rel'])][int(row['slot'])]=row
    assert list(frames)==list(range(11625))
    assert all(r['mode']=='2' and r['timeStop']=='00000000' for r in frames.values())
    assert all([float(r[x]) for x in ['x','y','z']]==[1742,-2088,-125] for r in frames.values())
    eligible={}
    for pair in [(29,32),(29,33),(33,31),(32,31)]:
        eligible['/'.join(map(str,pair))]=[f for f in frames if all(
            float(cogs[f][s]['target'])==0 and abs(float(cogs[f][s]['speed']))<=50 for s in pair)]
    assert eligible['29/32']==[FRAME]
    survey_summary=json.loads((survey/'summary.json').read_text())
    assert survey_summary['cheats_disabled'] and not survey_summary['observer_errors']
    cases=[];normalized=[];provenance={};validation={};geometry={};capture_rows={}
    for v in ['us','jp']:
        out=OUT/v;trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{v}'
        capture=observations(trial)
        capture_rows[v]=capture
        result=json.loads((out/'results.json').read_text())
        build=json.loads((out/'build.json').read_text())
        assert result['csv_sha256']==sha(out/'seeds.csv')
        assert result['build_sha256']==sha(out/'build.json')
        assert result['validation_sha256']==sha(out/'validation.json')
        seeds=list(csv.DictReader((out/'seeds.csv').open()))
        assert [int(r['seed']) for r in seeds]==list(range(65536))
        normalized.append([{k:w for k,w in r.items() if k!='pc'} for r in seeds])
        result['isolated_longest_replays']=len(result['longest_cases'])
        result['longest_seeds']=[int(r['seed']) for r in result.pop('longest_cases')]
        result['dma_call_histogram']=dict(collections.Counter(r['dma_calls'] for r in seeds))
        cases.append(result)
        validation[v]=json.loads((out/'validation.json').read_text())
        geometry[v]=json.loads((out/'geometry.json').read_text())
        geometry[v].pop('compiler')
        provenance[v]={k:w for k,w in build.items() if k not in ['symbols','command','snapshot_directory','rom_file']}
        provenance[v]['initialization']=json.loads((trial/'manifest.json').read_text())['initialization']
        provenance[v]['summary_sha256']=sha(trial/'summary.json')
    assert capture_rows['us']==[(k,r) for k,r in rows if int(r['rel'])<=844]
    # Relocate only recorded pointers, not game state or angles, for the US/JP comparison.
    def logical(items):
        return [(k,{a:b for a,b in r.items() if a not in ['object','floor','ceil','floorOwner','ceilOwner']}) for k,r in items]
    assert logical(capture_rows['us'])==logical(capture_rows['jp'])
    assert geometry['us']['records']==geometry['jp']['records']
    report={'date':'2026-09-23','source_pin':provenance['us']['source_pin'],
        'evidence_class':'finite offline RANDOM cog-schedule experiment with explicit external-I/O assumptions; not a Pedro preservation or Coq theorem',
        'correction':'Previous family changed STOPPED snapshots to RANDOM offline. This family preserves already-RANDOM mode and all non-seed starting fields.',
        'survey':{'frames':len(frames),'trace_sha256':sha(survey/'trace.csv'),
                  'manifest_sha256':sha(survey/'manifest.json'),'eligible_incoming_frames':eligible,
                  'selection':'both target zero and absolute angular speed at most 50, so next approach step leaves both yaws unchanged',
                  'all_frames_random_without_time_stop':True,'snapshot_prefix_matches_survey':True,
                  'us_jp_845_frame_logical_prefix_identical':True},
        'starting_frame':FRAME,'starting_mario':frames[FRAME],
        'starting_cogs':[cogs[FRAME][s] for s in sorted(cogs[FRAME])],
        'candidate_fields':['seed'],'controller':'neutral stick; no buttons',
        'total_seed_cases':sum(c['seeds'] for c in cases),'cases':cases,
        'normalized_us_jp_csvs_identical':normalized[0]==normalized[1],
        'geometry':geometry,'validation':validation,'build_provenance':provenance,
        'source_sha256':{str(p.relative_to(HERE.parent)):sha(p) for p in sorted(HERE.glob('*')) if p.suffix in ['.c','.py','.md']},
        'limits':['Authorized near-cog initialization, not normal level-entry provenance.',
                  'Only the original seed is observed with this non-seed state; alternative seed combinations are hypotheses.',
                  'Mario remains on the ledge. Moving him to candidate geometry changes object activity and requires a new sweep.',
                  'Audio, OS scheduling, cache and device side effects are not fully modeled or proved irrelevant.',
                  'One RANDOM phase per version is not all RANDOM preparations; inputs remain fixed.']}
    dest=PROJECT/'docs/notes/ttc-cog-random-seed-sweep-results.json'
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'cases':report['total_seed_cases'],'eligible':eligible,'normalized_identical':report['normalized_us_jp_csvs_identical'],
                      'maximum':[c['maximum_complete_updates'] for c in cases]}))


if __name__=='__main__':main()
