#!/usr/bin/env python3
"""Run the explicit three-state US/JP family, with independent seed continuations."""
import argparse
import collections
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import json
import os
import subprocess
import time

from prepare import OUT, PROJECT, FRAMES, sha


def sweep(version, case):
    out = OUT/version
    build = json.loads((out/'build.json').read_text())
    validation = json.loads((out/'validation.json').read_text())
    assert validation['build_sha256'] == sha(out/'build.json'), 'rerun validation after rebuilding'
    assert build['executable_sha256'] == sha(out/'sweep')
    frame = FRAMES[case]
    trial = PROJECT/f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
    assert sha(trial/f'snapshots/{frame}-enter.ram') == build['snapshots'][case]['ram_sha256']
    csv_path = out/f'seeds-{frame}.csv'
    command = [str(out/'sweep'), str(trial/'snapshots'), str(case), '0', '65536', '1200', '0']
    begin = time.perf_counter()
    with csv_path.open('x') as rows, (out/f'seeds-{frame}.log').open('x') as log:
        # A supervisory timeout aborts coverage; it cannot become rejection.
        subprocess.run(command, stdout=rows, stderr=log, check=True, timeout=7200)
    elapsed = time.perf_counter()-begin
    rows = list(csv.DictReader(csv_path.open()))
    assert [int(r['seed']) for r in rows] == list(range(65536))
    assert all(r['status'] in ['rejected', 'unknown', 'survived'] for r in rows)
    counts = dict(collections.Counter(r['status'] for r in rows))
    best = max(int(r['complete_updates']) for r in rows)
    report = {'version': version, 'snapshot_frame': frame, 'horizon': 1200, 'seed_count': len(rows),
              'status_counts': counts, 'reasons': dict(collections.Counter(r['reason'] for r in rows)),
              'completed_update_histogram': dict(sorted(collections.Counter(int(r['complete_updates']) for r in rows).items())),
              'longest_complete_prefix': best, 'longest_cases': [r for r in rows if int(r['complete_updates']) == best],
              'total_complete_updates': sum(int(r['complete_updates']) for r in rows),
              'total_rng_calls': sum(int(r['rng_calls']) for r in rows),
              'min_rng_calls': min(int(r['rng_calls']) for r in rows),
              'max_rng_calls': max(int(r['rng_calls']) for r in rows),
              'elapsed_seconds': elapsed, 'csv_sha256': sha(csv_path), 'build_sha256': sha(out/'build.json'),
              'validation_sha256': sha(out/'validation.json'), 'command': command}
    (out/f'summary-{frame}.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['version', 'snapshot_frame', 'status_counts', 'longest_complete_prefix', 'elapsed_seconds']}), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=3, choices=range(1,7))
    args = parser.parse_args()
    # Ambient diagnostic settings must not silently change published coverage.
    if 'SWEEP_FUEL' in os.environ:
        parser.error('unset SWEEP_FUEL before the full sweep')
    begin = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = [f.result() for f in as_completed([pool.submit(sweep, v, i) for v in ['us','jp'] for i in range(3)])]
    report = {'family': 'search_edge_a STOPPED snapshots, hypothetical RANDOM seed variants',
              'wall_seconds': time.perf_counter()-begin, 'parallel_jobs': args.jobs,
              'cases': sorted(results, key=lambda r: (r['version'], r['snapshot_frame']))}
    (OUT/'results.json').write_text(json.dumps(report, indent=2)+'\n')
