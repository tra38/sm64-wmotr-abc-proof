"""Finite controller-policy sweep, 90 real updates per conditional start.

This is not exhaustive over controller sequences, positions or object phases.
Every trial starts a fresh process; no outcome is fed back as a game fixture.
"""
import argparse
import concurrent.futures
import hashlib
import json
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent


def cases():
    starts = [(0, 41), (1, 41), (2, 41), (2, 60), (2, 100), (2, 130),
              (3, 41), (4, 41), (5, 41)]
    return [(kind, phase, policy) for kind, phase in starts
            for policy in (range(36) if (kind, phase) == (2, 130) else (0, 1, 10, 28))]


def trial(rom, case, directory):
    kind, phase, policy = case
    label = f'k{kind}-t{phase}-p{policy}'
    before = time.monotonic()
    try:
        process = subprocess.run(['bash', str(HERE/'run.sh'), str(rom), *map(str, case)],
                                 capture_output=True, text=True, timeout=280)
    except subprocess.TimeoutExpired as error:
        (directory/f'{label}.log').write_text(f'Trial timed out: {error}\n')
        return dict(case=case, exit=124, seconds=round(time.monotonic()-before, 2), output=None)
    (directory/f'{label}.log').write_text(process.stdout+process.stderr)
    output = next((line.removeprefix('Output: ') for line in process.stdout.splitlines()
                   if line.startswith('Output: ')), None)
    result = dict(case=case, exit=process.returncode, seconds=round(time.monotonic()-before, 2),
                  output=output)
    if output and (Path(output)/'result.json').exists():
        result['result'] = json.loads((Path(output)/'result.json').read_text())
        result['traceSha256'] = hashlib.sha256((Path(output)/'trace.txt').read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('rom', type=Path)
    parser.add_argument('--workers', type=int, choices=(1, 2, 3), default=3)
    args = parser.parse_args()
    root = PROJECT/'build/instrumentation/jp-dialog-support-search'
    root.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix='search.', dir=root))
    (directory/'cases.json').write_text(json.dumps(cases(), indent=2)+'\n')
    print(f'Search output: {directory}; {len(cases())} cases; 90 updates each', flush=True)
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        jobs = [executor.submit(trial, args.rom, case, directory) for case in cases()]
        for job in concurrent.futures.as_completed(jobs):
            result = job.result()
            results.append(result)
            (directory/'results.json').write_text(json.dumps(results, indent=2)+'\n')
            print(f"{len(results)}/{len(jobs)} {result['case']} exit={result['exit']} "
                  f"targets={result.get('result', {}).get('targetCandidates', 'unvalidated')}", flush=True)
    failures = [r for r in results if r['exit'] != 0 or 'result' not in r]
    print(f'Completed {len(results)} trials; {len(failures)} failed validation; output: {directory}')
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
