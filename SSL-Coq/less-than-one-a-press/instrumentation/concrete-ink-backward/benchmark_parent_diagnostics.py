"""One bounded diagnostic process; preserve source HEAD and inclusive timing."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ledger',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    head=lambda:hashlib.sha256((a.ledger/'HEAD.json').read_bytes()).hexdigest()
    before=head();started=time.perf_counter()
    cmd=[sys.executable,'-X','utf8',str(Path(__file__).with_name('parent_diagnostics.py')),
         '--ledger',str(a.ledger),'--output',str(a.output/'report.json'),'--replay-suffix',
         '--game-updates','5000','--setup-seconds','30','--verification-seconds','30',
         '--search-seconds','30','--wall-seconds','90']
    with (a.output/'stdout.log').open('wb') as out,(a.output/'stderr.log').open('wb') as err:
        try:process=subprocess.run(cmd,stdout=out,stderr=err,timeout=100)
        except subprocess.TimeoutExpired:
            atomic_json(a.output/'attempt.json',dict(command=cmd,processWallSeconds=time.perf_counter()-started,
                           timedOut=True,sourceHeadUnchanged=head()==before));raise
    wall=time.perf_counter()-started
    receipt=dict(command=cmd,processWallSeconds=wall,exitCode=process.returncode,
                 sourceHeadSha256=before,sourceHeadUnchanged=head()==before)
    atomic_json(a.output/'attempt.json',receipt)
    if process.returncode or not receipt['sourceHeadUnchanged']:
        raise RuntimeError('Diagnostic failed or source HEAD changed; inspect saved logs')
    r=json.loads((a.output/'report.json').read_text())
    print(json.dumps(dict(status=r['status'],processWallSeconds=wall,
                         updates=r.get('nativeSearchUpdates'),summary=r.get('replaySummary'))))


if __name__=='__main__':main()
