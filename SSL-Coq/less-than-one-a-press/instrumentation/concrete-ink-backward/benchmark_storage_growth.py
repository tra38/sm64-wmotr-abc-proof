"""External whole-process costs for compacting fixed prefixes of existing data."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False);started=time.perf_counter();rows=[]
    for count in (5000,20000,80000):
        dest=a.output/str(count);begin=time.perf_counter()
        cmd=[sys.executable,'-X','utf8',str(Path(__file__).with_name('benchmark_compaction.py')),
             '--source',str(a.source),'--output',str(dest),'--cases',str(count)]
        with (a.output/(str(count)+'.stdout.log')).open('wb') as out,(a.output/(str(count)+'.stderr.log')).open('wb') as err:
            try:run=subprocess.run(cmd,stdout=out,stderr=err,timeout=60)
            except subprocess.TimeoutExpired:
                atomic_json(a.output/(str(count)+'.attempt.json'),dict(command=cmd,timedOut=True,processWallSeconds=time.perf_counter()-begin))
                raise
        wall=time.perf_counter()-begin
        atomic_json(a.output/(str(count)+'.attempt.json'),dict(command=cmd,exitCode=run.returncode,processWallSeconds=wall))
        if run.returncode:raise RuntimeError('Compaction failed; inspect saved stderr')
        row=json.loads((dest/'report.json').read_text());row['processWallSeconds']=wall;rows.append(row)
        print(json.dumps(dict(cases=count,bytes=row['compactTotalBytes'],processWallSeconds=wall)),flush=True)
    atomic_json(a.output/'growth.json',dict(rows=rows,totalExternalWallSeconds=time.perf_counter()-started,
                                          source=str(a.source),scope='Compaction/audit of old game results, no new gameplay search'))


if __name__=='__main__':main()
