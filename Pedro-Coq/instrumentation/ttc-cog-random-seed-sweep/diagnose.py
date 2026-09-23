#!/usr/bin/env python3
"""Compare both-cog and single-cog criteria on the existing longest seeds.

Only the offline acceptance predicate varies. Game state and controller input
remain identical. This is a diagnostic sample, not another exhaustive sweep
and not a check that moving the other cog preserves Pedro geometry.
"""
import collections
import csv
import io
import json
import os
from pathlib import Path
import subprocess
from run import HERE, OUT, PROJECT, FRAME, sha

DEST=PROJECT/'build/cog-sweep-diagnosis'


def execute(exe, snapshots, seed, trace=False, baseline=0, horizon=20):
    env=dict(os.environ);env.pop('SWEEP_FUEL',None);env['SWEEP_TRACE']=str(int(trace))
    p=subprocess.run([str(exe),str(snapshots),'0',str(seed),'1',str(horizon),str(baseline)],
                     text=True,capture_output=True,check=True,timeout=30,env=env)
    result,=list(csv.DictReader(io.StringIO(p.stdout)))
    events=[line.split(',') for line in p.stderr.splitlines() if line.startswith(('DRAW,','COG,'))]
    return result,events


def main():
    cases=[]
    for family in ['stopped','random']:
        for version in ['us','jp']:
            if family=='random':
                original=OUT/version
                csv_path=original/'seeds.csv'
                trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{version}'
            else:
                original=PROJECT/f'build/cog-seed-sweep/{version}'
                csv_path=original/'seeds-0.csv'
                trial=PROJECT/f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
            build=json.loads((original/'build.json').read_text())
            header=(original/'config.h').read_text()
            rows=list(csv.DictReader(csv_path.open()))
            longest=[r for r in rows if int(r['complete_updates'])==3]
            out=DEST/f'{family}-{version}';out.mkdir(parents=True,exist_ok=True)
            executables={}
            for mask in [3,1,2]:
                config=out/str(mask);config.mkdir(exist_ok=True)
                # Single-cog diagnostics deliberately drop Mario's preservation
                # predicate. The mask-3 control retains the historical predicate.
                extra=f'\n#define REQUIRED_COG_MASK {mask}\n'
                if mask!=3:extra+='\n#undef COG_SCHEDULE_ONLY\n#define COG_SCHEDULE_ONLY 1\n'
                (config/'config.h').write_text(header+extra)
                exe=config/'sweep';command=build['command'].copy()
                command[command.index('-I'+str(original))]='-I'+str(config)
                command[-1]=str(exe)
                subprocess.run(command,check=True)
                executables[mask]=exe
            summaries={str(m):[] for m in [3,1,2]}
            for row in longest:
                seed=int(row['seed'])
                for mask in [3,1,2]:
                    actual,_=execute(executables[mask],trial/'snapshots',seed)
                    if mask==3:
                        assert all(actual[k]==v for k,v in row.items()),(family,version,row,actual)
                    summaries[str(mask)].append(actual)
            # Capture the clearest same-seed comparison, including every draw.
            best=max(summaries['1']+summaries['2'],key=lambda r:int(r['complete_updates']))
            example={}
            for mask in [3,1,2]:
                result,events=execute(executables[mask],trial/'snapshots',int(best['seed']),True)
                assert result==next(r for r in summaries[str(mask)] if r['seed']==best['seed'])
                path=out/f'example-{mask}.json'
                path.write_text(json.dumps({'result':result,'events':events},indent=2)+'\n')
                example[str(mask)]={'result':result,'events':events}
            if family=='random':
                # Compare the added detailed draw hook against the independent
                # original-seed read-only emulator trace, not just a checksum.
                result,events=execute(executables[3],trial/'snapshots',0,True,baseline=1,horizon=3)
                expected=[];pool=build['symbols']['gObjectPool'][0]
                for line in (trial/'trace.csv').read_text().splitlines():
                    if line.startswith('CRNG,'):
                        r=dict(s.split('=',1) for s in line.split(',')[2:])
                        if FRAME<=int(r['rel'])<FRAME+3:
                            expected.append([int(r['rel'])-FRAME,(int(r['object'],16)-pool)//0x260,
                                             int(r['before']),int(r['after']),int(r['result'])])
                actual=[[int(e[1]),*map(int,e[3:])] for e in events if e[0]=='DRAW']
                assert actual==expected and result['status']=='survived'
            histograms={m:dict(sorted(collections.Counter(int(r['complete_updates']) for r in rs).items())) for m,rs in summaries.items()}
            status={m:dict(collections.Counter(r['status'] for r in rs)) for m,rs in summaries.items()}
            record={'family':family,'version':version,'seeds':len(longest),'horizon':20,
                    'seed_sample':[int(r['seed']) for r in longest],
                    'masks':{'3':'both fixed, original predicate','1':'lower only, no Mario predicate','2':'upper only, no Mario predicate'},
                    'histograms':histograms,'statuses':status,'example':example,
                    'source_build_sha256':sha(original/'build.json'),'source_csv_sha256':sha(csv_path),
                    'example_seed':int(best['seed']),
                    'sample_results':summaries}
            (out/'results.json').write_text(json.dumps(record,indent=2)+'\n')
            cases.append(record)
            print(json.dumps({k:record[k] for k in ['family','version','seeds','histograms','statuses','example_seed']}),flush=True)
    for family in ['stopped','random']:
        us,jp=[c for c in cases if c['family']==family]
        assert us['histograms']==jp['histograms'] and us['statuses']==jp['statuses']
        for mask in ['3','1','2']:
            assert us['example'][mask]['events']==jp['example'][mask]['events']
    # Keep full sampled outputs and traces in ignored build artifacts. Export
    # compact outcomes and the relevant per-update evidence, without game RAM.
    exported=[]
    for case in cases:
        item={k:v for k,v in case.items() if k not in ['sample_results','example']}
        item['longest_sampled_by_mask']={m:max(rs,key=lambda r:int(r['complete_updates']))
                                         for m,rs in case['sample_results'].items()}
        item['unknown_cases']={m:[r for r in rs if r['status']=='unknown'] for m,rs in case['sample_results'].items()}
        item['example']={}
        for mask,example in case['example'].items():
            frames=[]
            for frame in range(int(example['result']['complete_updates'])+1):
                events=[e for e in example['events'] if int(e[1])==frame]
                draws=[e for e in events if e[0]=='DRAW']
                frames.append({'update':frame,'rng_calls':len(draws),
                    'rng_calls_by_object':dict(collections.Counter(e[3] for e in draws)),
                    'cog_draw_columns':['global_draw_index','slot','before_seed','result'],
                    'cog_draws':[[int(e[2]),int(e[3]),int(e[4]),int(e[6])] for e in draws if e[3] in ['29','32']],
                    'cog_exits':[{'slot':int(e[3]),'yaw':int(e[4]),'speed':float(e[5]),'target':float(e[6])}
                                 for e in events if e[0]=='COG' and e[2]=='exit' and e[3] in ['29','32']]})
            item['example'][mask]={'result':example['result'],'frames':frames,
                'full_trace_sha256':sha(DEST/f'{case["family"]}-{case["version"]}'/f'example-{mask}.json')}
        exported.append(item)
    report={'date':'2026-09-23','source_pin':build['source_pin'],'scope':'diagnostic sample of the previous longest seeds; no whole-state or single-cog exhaustive bound',
            'cases':exported,'sweep_source_sha256':sha(HERE.parent/'ttc-cog-seed-sweep/sweep.c'),
            'diagnostic_source_sha256':sha(Path(__file__)),
            'video_comparison':'video counts one stationary cog; previous sweeps require both slots 29 and 32 fixed',
            'limits':'Same external-system execution model; single-cog success does not establish Mario preservation or other-cog collision adequacy.'}
    (PROJECT/'docs/notes/ttc-cog-sweep-diagnosis-results.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
