"""Measure actual Wafel batches with an external whole-process wall clock.

Increasing cumulative ledger sizes, default full-verify resume. Does not
reuse the old 5,000-trial receipt or infer exhaustive multi-update coverage.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import atomic_json


def disk_size(root):
    size, files=0,0
    for path in root.rglob('*'):
        if path.is_file():
            size+=path.stat().st_size
            files+=1
    return dict(bytes=size,files=files)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--sizes',type=int,nargs='+',default=[5000,20000,80000])
    parser.add_argument('--process-timeout',type=float,default=180)
    args=parser.parse_args()
    if args.output.exists() or sorted(set(args.sizes))!=args.sizes or args.sizes[0]<1:
        parser.error('New output path and increasing positive sizes required')
    args.output.mkdir(parents=True)
    sweep=Path(__file__).with_name('product_sweep.py')
    report=args.output/'report.json'
    rows=[]
    audits=[]
    cursor=0
    all_started=time.perf_counter()
    for size in args.sizes:
        print('Starting real Wafel batch: %d -> %d'%(cursor,size),flush=True)
        command=[sys.executable,'-X','utf8',str(sweep),'--buttons','stock-gameplay','--order','mixed',
                 '--cases',str(size-cursor),'--seconds',str(args.process_timeout-10),'--output',str(report)]
        if cursor: command.append('--resume')
        started=time.perf_counter()
        try:
            process=subprocess.run(command,capture_output=True,text=True,timeout=args.process_timeout)
        except subprocess.TimeoutExpired as exc:
            elapsed=time.perf_counter()-started
            stdout=exc.stdout or ''; stderr=exc.stderr or ''
            if isinstance(stdout,bytes): stdout=stdout.decode('utf-8',errors='replace')
            if isinstance(stderr,bytes): stderr=stderr.decode('utf-8',errors='replace')
            (args.output/('batch-%d.stdout.log'%size)).write_text(stdout,encoding='utf-8')
            (args.output/('batch-%d.stderr.log'%size)).write_text(stderr+'\nProcess timeout; resume uses HEAD.\n',encoding='utf-8')
            atomic_json(args.output/('attempt-%d.json'%size),dict(command=command,
                        processWallSeconds=elapsed,returncode=None,timedOut=True,
                        requestedFrom=cursor,requestedThrough=size))
            raise RuntimeError('Batch timed out; diagnostics preserved and HEAD controls recovery') from exc
        elapsed=time.perf_counter()-started
        (args.output/('batch-%d.stdout.log'%size)).write_text(process.stdout,encoding='utf-8')
        (args.output/('batch-%d.stderr.log'%size)).write_text(process.stderr,encoding='utf-8')
        atomic_json(args.output/('attempt-%d.json'%size),dict(command=command,
                    processWallSeconds=elapsed,returncode=process.returncode,
                    requestedFrom=cursor,requestedThrough=size))
        if process.returncode:
            raise RuntimeError('Batch failed: '+process.stderr)
        result=json.loads(report.read_text(encoding='utf-8'))
        if result['nextCase']!=size or result['thisBatch']['tested']!=size-cursor:
            raise RuntimeError('Wall/candidate limit reached; no skipped cases permitted')
        snapshot=args.output/('batch-%d.json'%size)
        atomic_json(snapshot,result)
        rows.append(dict(cumulativeCases=size,newCases=size-cursor,processWallSeconds=elapsed,
                         inclusiveCasesPerSecond=(size-cursor)/elapsed,
                         cumulativeProcessWallSeconds=sum(r['processWallSeconds'] for r in rows)+elapsed,
                         phaseSeconds=result['phaseSeconds'],io=result['ledger']['io'],
                         peakRssBytes=result['peakRssBytes'],ledgerDisk=disk_size(report.with_suffix('.ledger')),
                         counts=result['counts'],retained=result['ledger']['retained']))
        cursor=size
        # Pure integrity audits demonstrate how complete corruption detection
        # grows with history. These separately timed processes do not advance
        # the cursor or manufacture additional accepted states.
        started=time.perf_counter()
        check=subprocess.run([sys.executable,'-X','utf8',str(sweep),'--audit','--output',str(report)],
                             capture_output=True,text=True,timeout=args.process_timeout)
        audit_wall=time.perf_counter()-started
        if check.returncode:
            raise RuntimeError('Full audit failed: '+check.stderr)
        audit=json.loads(check.stdout)
        if audit['verifiedCases']!=size: raise RuntimeError('Audit cursor differs')
        audits.append(dict(cases=size,processWallSeconds=audit_wall,**audit))
        summary=dict(schema=1,batches=rows,audits=audits,
                     wholeBenchmarkWallSeconds=time.perf_counter()-all_started,
                     runtime=result['signature'],
                     scope='Real supplied-scene, one-update trials, not reachable gap generation; '
                           'all batch clocks include interpreter startup/shutdown and report finalization. '
                           'Whole benchmark also includes separate audits and benchmark receipt/stat work.',
                     newCasesPerCumulativeProcessSecond=size/sum(r['processWallSeconds'] for r in rows))
        atomic_json(args.output/'benchmark.json',summary)
        print(json.dumps(rows[-1]),flush=True)
    print('Stopped after %d real trials; all %d full audits passed.'%(cursor,len(audits)),flush=True)


if __name__=='__main__': main()
