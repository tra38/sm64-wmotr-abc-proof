#!/usr/bin/env python3
"""Calibrate RANDOM branches against unedited emulator snapshots and trace draws."""
import json
from pathlib import Path
from offline import Execution, load_trial
from prepare import OUT, PROJECT, sha
from validate import invoke


def main():
    receipts = []
    for version in ['us', 'jp']:
        trial = PROJECT/f'build/cog-placement/search_edge_a/seed_random_calibration_{version}'
        manifest = json.loads((trial/'manifest.json').read_text())
        summary = json.loads((trial/'summary.json').read_text())
        assert summary['cheats_disabled'] and not summary['observer_errors']
        build = json.loads((OUT/version/'build.json').read_text())
        # Profiling samples CP0 COUNT; this executor does not model real time.
        address, size = build['symbols']['gProfilerFrameData']
        begin = address & 0x1fffffff
        for frame in [0, 1, 2]:
            e = Execution(trial, manifest, frame)
            result = e.run()
            if result['status'] != 'complete':
                assert frame != 0, result
                receipts.append({'version':version,'frame':frame,'status':'unknown',
                                 'error':result['error'],'pc':result['pc'],'unmapped':e.unmapped,
                                 'manifest_sha256':sha(trial/'manifest.json')})
                continue
            actual = bytes(e.vm.mem_read(0, len(e.initial)))
            expected_path = trial/f'snapshots/{frame}-exit.ram'
            expected = expected_path.read_bytes()
            differences = [i for i in range(len(actual)) if actual[i] != expected[i]]
            assert all(begin <= i < begin+size for i in differences), (version, frame, differences[:20])
            draws = []
            for line in (trial/'trace.csv').read_text().splitlines():
                if line.startswith('CRNG,'):
                    fields = dict(x.split('=',1) for x in line.split(',')[2:])
                    if int(fields['rel']) == frame:
                        draws.append([int(fields['before']), int(fields['object'],16)])
            assert result['rng'] == draws
            receipts.append({'version':version,'frame':frame,'status':'matched','rng_calls':len(draws),
                             'different_profiler_bytes':len(differences),'entry_sha256':sha(trial/f'snapshots/{frame}-enter.ram'),
                             'exit_sha256':sha(expected_path),'manifest_sha256':sha(trial/'manifest.json')})
        # Native batch hooks and Python reference hooks must agree on varied seeds.
        trial, manifest = load_trial(version)
        for seed in [0,1,2,3,42,12345,58704,65535]:
            e = Execution(trial,manifest,0)
            result = e.run(seed,True)
            assert result['status'] == 'complete', result
            row, = invoke(version,0,1,baseline=0,first=seed)
            assert row['status'] == 'survived', row
            digest=14695981039346656037
            for state,obj in e.rng:
                for value in [state,(obj-manifest['symbols']['gObjectPool'])//0x260]:
                    digest=((digest^value)*1099511628211)&((1<<64)-1)
            assert row['rng_calls'] == str(len(e.rng)) and row['rng_hash'] == f'{digest:016x}', (version,seed,row)
    report={'random_emulator_baselines':receipts,'native_reference_seed_samples_per_version':8}
    (OUT/'random-calibration.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
