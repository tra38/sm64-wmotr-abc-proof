"""External total-wall timing of two bounded, equal-native-update pilot arms."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json


def execute(directory,name,arguments):
    started=time.perf_counter()
    cmd=[sys.executable,'-X','utf8',str(Path(__file__).with_name('reverse_scattershot.py')),
         '--output',str(directory/(name+'.json'))]+arguments
    with (directory/(name+'.stdout.log')).open('wb') as out,(directory/(name+'.stderr.log')).open('wb') as err:
        try:
            process=subprocess.run(cmd,stdout=out,stderr=err,timeout=100)
        except subprocess.TimeoutExpired:
            atomic_json(directory/(name+'.attempt.json'),dict(command=cmd,processWallSeconds=time.perf_counter()-started,timedOut=True))
            raise
    wall=time.perf_counter()-started
    atomic_json(directory/(name+'.attempt.json'),dict(command=cmd,processWallSeconds=wall,exitCode=process.returncode))
    if process.returncode:raise RuntimeError('Runtime failed; inspect '+str(directory/(name+'.stderr.log')))
    report=json.loads((directory/(name+'.json')).read_text())
    return dict(name=name,processWallSeconds=wall,report=report)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seed',type=int,default=20261003)
    p.add_argument('--game-updates',type=int,default=2000)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    started=time.perf_counter()
    arms=[]
    for scheduler in ('menu-first','scattershot'):
        print('Starting bounded arm: '+scheduler,flush=True)
        arms.append(execute(a.output,scheduler,['--scheduler',scheduler,'--seed',str(a.seed),
                    '--game-updates',str(a.game_updates),'--trials','2000','--depth','3','--archive','12',
                    '--setup-seconds','30','--verification-seconds','30','--search-seconds','30','--wall-seconds','90']))
    if any(arm['report']['batchGameUpdates']!=a.game_updates for arm in arms):
        raise RuntimeError('Equal native-update budgets were not consumed; inspect receipts before comparing')
    atomic_json(a.output/'comparison.json',dict(seed=a.seed,nativeUpdateBudgetEach=a.game_updates,
            totalExternalWallSeconds=time.perf_counter()-started,arms=arms,
            comparisonScope='Old installation-menu-first scheduling versus interleaved backward expansion, '
                'using the same new compact storage, predicate reuse and continuous suffix/retention validator. '
                'The old product executable did not validate retention per candidate, so it is not timed as '
                'an equivalent check. All native suffix/retention updates and incomplete final attempts count.'))
    print(json.dumps([dict(name=arm['name'],wall=arm['processWallSeconds'],
                   trials=arm['report']['batchTrials'],updates=arm['report']['batchGameUpdates'],
                   depth=arm['report']['deepestValidatedUpdates']) for arm in arms]))


if __name__=='__main__':main()
