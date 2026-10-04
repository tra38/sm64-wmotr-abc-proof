"""Small real-Wafel deterministic stop/resume and verification-limit controls."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from benchmark_scattershot import execute
from chunk_ledger import atomic_json
from reverse_scattershot import open_store


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False);started=time.perf_counter()
    common=['--seed','20261003','--game-updates','1000','--depth','3','--archive','12']
    first=execute(a.output,'segmented',common+['--trials','8'])
    # Save the first receipt before the successful resume replaces it.
    atomic_json(a.output/'first-eight.json',first)
    second=execute(a.output,'segmented',common+['--trials','8','--resume'])
    whole=execute(a.output,'whole',common+['--trials','16'])
    snapshots=[]
    for name in ('segmented','whole'):
        root=a.output/(name+'.ledger');manifest=json.loads((root/'manifest.json').read_text())['payload']
        with open_store(root,manifest['signature'],True,read_only=True) as s:
            snapshots.append((s.state,list(s.records())))
    if snapshots[0]!=snapshots[1]:raise AssertionError('Real resumed sampler/archive/records differ')
    if second['report']['batchGameUpdates']+first['report']['batchGameUpdates']!=whole['report']['batchGameUpdates']:
        raise AssertionError('Game-update accounting differs across complete-trial checkpoints')
    root=a.output/'segmented.ledger';head=(root/'HEAD.json').read_bytes();receipt=(a.output/'segmented.json').read_bytes()
    cmd=[sys.executable,'-X','utf8',str(Path(__file__).with_name('reverse_scattershot.py')),
         '--output',str(a.output/'segmented.json')]+common+['--trials','1','--resume','--verification-seconds','0']
    with (a.output/'verification-limit.stdout.log').open('wb') as out,(a.output/'verification-limit.stderr.log').open('wb') as err:
        done=subprocess.run(cmd,stdout=out,stderr=err,timeout=100)
    if done.returncode:raise AssertionError('Verification-limit control errored')
    incomplete=json.loads((a.output/'segmented.attempt-limit.json').read_text())
    if (incomplete['status']!='verification incomplete' or incomplete['batchTrials']!=0
            or (root/'HEAD.json').read_bytes()!=head or (a.output/'segmented.json').read_bytes()!=receipt):
        raise AssertionError('Verification failure modified committed history/receipt or ran candidates')
    report=dict(status='passed',seed=20261003,completedTrialsEach=16,
                nativeSearchUpdatesEach=whole['report']['batchGameUpdates'],
                samplerArchiveAndEveryRecordEqual=True,fullAuditsPassed=True,
                verificationLimitStatus=incomplete['status'],headAndPriorReceiptUnchanged=True,
                totalExternalWallSeconds=time.perf_counter()-started,
                scope='Two eight-trial real runs equal one sixteen-trial run on declared observations/recipes '
                      'and all recorded updates. No full-memory equality or gameplay reachability.')
    atomic_json(a.output/'verification.json',report);print(json.dumps(report))


if __name__=='__main__':main()
