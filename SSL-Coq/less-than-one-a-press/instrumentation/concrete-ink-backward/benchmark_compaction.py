"""Non-destructive real-log compaction cost/storage measurements, no game trials."""
import argparse
import json
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
from chunk_ledger import ChunkLedger, atomic_json
from compact_store import ProductCodec, open_product
from product_sweep import validate_record,peak_rss_bytes


def size(path):
    return sum(f.stat().st_size for f in path.rglob('*') if f.is_file())


def measure(source,destination,count):
    started=time.perf_counter()
    manifest=json.loads((source/'manifest.json').read_text())['payload']
    phase=time.perf_counter()
    old=open_product(source,manifest,read_only=True)
    phases={'sourceFullVerification':time.perf_counter()-phase}
    try:
        if count>old.state['nextCase']: raise ValueError('Not enough committed source trials')
        sig=dict(manifest['signature']); sig['migrationOrigin']=dict(manifestSha256=old.manifest_sha,
                    commitSha256=old.commit_sha,generation=old.generation,prefixCases=count)
        phase=time.perf_counter()
        new=ChunkLedger(destination,sig,manifest['totalCases'],validate_record(sig),codec=ProductCodec(sig),
                        chunk_records=manifest['chunkRecords'])
        phases['initialization']=time.perf_counter()-phase
        phase=time.perf_counter(); raw_source_bytes=0
        with new:
            for generation in range(old.generation+1):
                meta,_=old._read_sealed(old._chunk(generation)/'commit.json')
                if meta['firstCase']>=count: break
                # Consume the complete last chunk, so its trailing hash check
                # executes even if the selected prefix ends inside it.
                for record in old._rows(old._chunk(generation)/old._payload_name('trials'),meta['trials']):
                    if old.codec is not None: record=old.codec.decode(record)
                    if record['case']<count: new.append(record)
                    if new.ready(): new.commit()
                raw_source_bytes+=meta['trials']['bytes']+meta['retained']['bytes']
            new.commit(); checkpoint_seconds=new.io['checkpointSeconds']
            new_io=dict(new.io)
        phases['migrationIncludingCheckpoints']=time.perf_counter()-phase
        new_manifest=json.loads((destination/'manifest.json').read_text())['payload']
        phase=time.perf_counter()
        with open_product(destination,new_manifest,read_only=True) as audit:
            assert audit.state['nextCase']==count
            full_io=dict(audit.io)
        phases['compactFullAudit']=time.perf_counter()-phase
        phase=time.perf_counter()
        with open_product(destination,new_manifest,verify='latest',read_only=True) as audit:
            latest_io=dict(audit.io)
        phases['explicitLatestAudit']=time.perf_counter()-phase
        return dict(cases=count,oldPayloadBytes=raw_source_bytes,compactTotalBytes=size(destination),
                    phaseSeconds=phases,checkpointSeconds=checkpoint_seconds,
                    totalSeconds=time.perf_counter()-started,peakRssBytes=peak_rss_bytes(),
                    writeIo=new_io,fullAuditIo=full_io,explicitLatestIo=latest_io,
                    scope='Actual existing rows, decoded identically and non-destructively rewritten to a new ledger. '
                          'Includes a full 80000-row source audit for each measurement; no gameplay-search rate.')
    finally: old.close()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cases',type=int,required=True)
    a=p.parse_args(); a.output.mkdir(parents=True,exist_ok=False)
    report=measure(a.source,a.output/'compact.ledger',a.cases)
    atomic_json(a.output/'report.json',report); print(json.dumps(report))


if __name__=='__main__': main()
