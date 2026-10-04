"""External wall-clock receipt and hard process ceiling for one bounded run."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seed', type=int, default=20261004)
    p.add_argument('--seconds', type=float, default=600.)
    p.add_argument('--hard-seconds', type=float, default=1000.)
    p.add_argument('--trials', type=int, default=1000000)
    a = p.parse_args()
    if not 0 < a.seconds <= 600 or a.hard_seconds < a.seconds + 180:
        p.error('Search at most 600 seconds; allow 180 seconds for setup/checkpoints/finalization')
    a.output.mkdir(parents=True, exist_ok=False)
    command = [sys.executable, '-X', 'utf8', str(Path(__file__).with_name('reverse_scattershot.py')),
               '--predecessor-menu', 'contact-approach', '--seed', str(a.seed),
               '--depth', '8', '--archive', '24', '--game-updates', '3000000',
               '--trials', str(a.trials), '--max-trials', '1000000', '--chunk-records', '100',
               '--search-seconds', str(a.seconds), '--setup-seconds', '60',
               '--verification-seconds', '60', '--wall-seconds', str(a.hard_seconds - 30),
               '--progress', '--output', str(a.output / 'report.json')]
    atomic_json(a.output / 'plan.json', dict(command=command, seed=a.seed,
        searchWorkSeconds=a.seconds, hardProcessSeconds=a.hard_seconds,
        description='All three supplied installation targets; expanded concrete predecessor menu; '
                    'actual suffix replay without intermediate patches; A released; no long search.'))
    started = time.perf_counter(); timed_out = False; exit_code = None
    with (a.output / 'stdout.log').open('wb') as out, (a.output / 'stderr.log').open('wb') as err:
        try:
            result = subprocess.run(command, stdout=out, stderr=err, timeout=a.hard_seconds)
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
    receipt = dict(command=command, processWallSeconds=time.perf_counter() - started,
                   timedOut=timed_out, exitCode=exit_code)
    atomic_json(a.output / 'process.json', receipt)
    print(json.dumps(receipt), flush=True)
    if timed_out or exit_code:
        raise SystemExit('Incomplete runtime: inspect stderr.log and preserved ledger')


if __name__ == '__main__': main()
