#!/usr/bin/env python3
"""Enumerate seeds from captured RANDOM states, without changing clock or cogs.

This first corrected search asks only whether cog slots 29/32 remain still.
Mario remains in the recorded ledge state and follows neutral controller input.
It is not an in-spot preservation or entry proof.
"""
import argparse
import collections
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ttc-cog-seed-sweep'))
from prepare import prepare, sha, PROJECT
from validate import differences, trace_draws

OUT = PROJECT/'build/cog-random-seed-sweep'
FRAME = 836


def trace_rows(path):
    rows = []
    for line in path.read_text().splitlines():
        if line.startswith(('CINPUT,','CFRAME,','CCOG,','CRNG,')):
            p=line.split(',')
            rows.append((p[0],dict(x.split('=',1) for x in p[2:])))
    return rows


def invoke(version, horizon, *, seed=0, count=1, baseline=0, save=None, fuel=None):
    out=OUT/version
    trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{version}'
    cmd=[str(out/'sweep'),str(trial/'snapshots'),'0',str(seed),str(count),str(horizon),str(baseline)]
    if save:cmd.append(str(save))
    env=dict(os.environ)
    env.pop('SWEEP_FUEL',None)
    if fuel is not None:env['SWEEP_FUEL']=str(fuel)
    p=subprocess.run(cmd,capture_output=True,text=True,check=True,timeout=60,env=env)
    return list(csv.DictReader(io.StringIO(p.stdout)))


def build_and_validate(version):
    trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{version}'
    out=OUT/version
    prepare(version,trial=trial,frames=[FRAME],out=out,natural_random=True,cog_only=True,animation_dma=True)
    build=json.loads((out/'build.json').read_text()); symbols=build['symbols']
    required=['gObjectPool','gMarioStates','gMarioPlatform','gLakituState','gCurrentObject',
              'gGlobalTimer','gControllers','gGfxPools','gMatStack','gTimeStopState','gTTCSpeedSetting',
              'gMarioAnimsBuf','gMarioAnimsMemAlloc']
    comparisons=[]
    for horizon in [1,2,3]:
        save=out/f'baseline-{horizon}.ram'
        row,=invoke(version,horizon,baseline=1,save=save)
        if row['status']!='survived':
            raise RuntimeError(f'baseline unsupported: {version} {horizon} {row}')
        actual=save.read_bytes(); expected_path=trial/f'snapshots/{FRAME+horizon-1}-exit.ram'
        expected=expected_path.read_bytes()
        manifest=json.loads((trial/'manifest.json').read_text())
        seed_address=manifest['symbols']['gRandomSeed16 (verified static load)']&0x1fffffff
        assert actual[seed_address:seed_address+2]==expected[seed_address:seed_address+2]
        assert int(row['final_seed'])==int.from_bytes(expected[seed_address:seed_address+2],'big')
        for name in required:
            address,size=symbols[name];address &= 0x1fffffff
            assert actual[address:address+size]==expected[address:address+size],(version,horizon,name)
        pointer=symbols['gMarioAnimsMemAlloc'][0]&0x1fffffff
        address=int.from_bytes(expected[pointer:pointer+4],'big')&0x1fffffff
        assert actual[address:address+0x4000]==expected[address:address+0x4000],(version,horizon,'animation-buffer')
        calls,digest=trace_draws(trial/'trace.csv',FRAME,FRAME+horizon-1,symbols['gObjectPool'][0])
        assert row['rng_calls']==str(calls) and row['rng_hash']==digest,(row,calls,digest)
        comparisons.append({'updates':horizon,'result':row,'actual_sha256':sha(save),
                            'expected_sha256':sha(expected_path),'full_ram_differences':differences(actual,expected,symbols)})
    positive,=invoke(version,1,baseline=2)
    assert positive['status']=='survived',positive
    unknown,=invoke(version,1200,fuel=1)
    assert unknown['status']=='unknown' and unknown['reason']=='instruction-budget'
    pilot=invoke(version,1200,count=128)
    isolated,=invoke(version,1200,seed=127)
    assert pilot[-1]==isolated
    raw=(trial/f'snapshots/{FRAME}-enter.ram').read_bytes()
    cogs=[]
    for slot in [29,32]:
        address=(symbols['gObjectPool'][0]+slot*0x260)&0x1fffffff
        cogs.append({'slot':slot,'yaw':struct.unpack_from('>i',raw,address+0xd4)[0],
                     'speed':struct.unpack_from('>f',raw,address+0xf8)[0],
                     'target':struct.unpack_from('>f',raw,address+0xfc)[0]})
    report={'version':version,'frame':FRAME,'required_identical_regions':required,
            'comparisons':comparisons,'original_seed_one_still_update':positive,
            'fuel_unknown':unknown,'isolated_seed':isolated,'cogs':cogs,
            'build_sha256':sha(out/'build.json'),'pilot_statuses':dict(collections.Counter(r['status'] for r in pilot))}
    (out/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'version':version,'baseline_updates':[1,2,3],'cogs':cogs,'pilot':report['pilot_statuses']}),flush=True)


def sweep(version):
    out=OUT/version
    trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{version}'
    validation=json.loads((out/'validation.json').read_text());build=json.loads((out/'build.json').read_text())
    assert validation['build_sha256']==sha(out/'build.json') and build['executable_sha256']==sha(out/'sweep')
    assert sha(Path(build['rom_file']))==build['rom_sha256']
    assert sha(trial/f'snapshots/{FRAME}-enter.ram')==build['snapshots'][0]['ram_sha256']
    path=out/'seeds.csv';begin=time.perf_counter()
    with path.open('x') as rows,(out/'seeds.log').open('x') as log:
        subprocess.run([str(out/'sweep'),str(trial/'snapshots'),'0','0','65536','1200','0'],
                       stdout=rows,stderr=log,check=True,timeout=7200)
    rows=list(csv.DictReader(path.open()));elapsed=time.perf_counter()-begin
    assert [int(r['seed']) for r in rows]==list(range(65536))
    best=max(int(r['complete_updates']) for r in rows)
    longest=[r for r in rows if int(r['complete_updates'])==best]
    for row in longest:
        isolated,=invoke(version,1200,seed=int(row['seed']))
        assert isolated==row
    report={'version':version,'frame':FRAME,'seeds':len(rows),'horizon':1200,
            'predicate':'both cog yaws fixed; Mario stays in recorded ledge context, not required in Pedro spot',
            'status_counts':dict(collections.Counter(r['status'] for r in rows)),
            'reasons':dict(collections.Counter(r['reason'] for r in rows)),
            'completed_update_histogram':dict(sorted(collections.Counter(int(r['complete_updates']) for r in rows).items())),
            'maximum_complete_updates':best,'longest_cases':longest,'elapsed_seconds':elapsed,
            'csv_sha256':sha(path),'build_sha256':sha(out/'build.json'),'validation_sha256':sha(out/'validation.json')}
    (out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage',choices=['validate','sweep']);p.add_argument('--version',choices=['us','jp','both'],default='both')
    a=p.parse_args();versions=['us','jp'] if a.version=='both' else [a.version]
    if 'SWEEP_FUEL' in os.environ:p.error('unset SWEEP_FUEL for this runner')
    if a.stage=='validate':
        for v in versions:build_and_validate(v)
    else:
        with ThreadPoolExecutor(max_workers=2) as pool:
            for f in as_completed([pool.submit(sweep,v) for v in versions]):f.result()
