"""Validate the declared end-update projection; no subframe peak claim."""
import argparse
import hashlib
import json
from pathlib import Path
import struct

def value(word): return struct.unpack('>f',struct.pack('>I',word))[0]

def summarize(report):
    tested=bounces=samples=0
    groups={}; max_gap=0.0; first_end=[]
    for trial in report['trials']:
        before=trial['before']
        if before['movement']!=before['collision'] or before['movement']!=before['display']:
            raise ValueError('Supplied initial records are not synchronized')
        group=groups.setdefault(trial['actor']['species'],dict(trials=0,bounces=0))
        tested+=1; group['trials']+=1
        bounces+=bool(trial['bounceDetectedByActionEntry']);group['bounces']+=bool(trial['bounceDetectedByActionEntry'])
        previous=before
        for sample in trial['updates']:
            after=sample['after']
            if after['frame']!=previous['frame']+1 or after['timer']!=previous['timer']+1:
                raise ValueError('Nonconsecutive update boundary')
            if after['buttonDown']&0x8000 or after['buttonPressed']&0x8000:
                raise ValueError('Unexpected A input in neutral suffix')
            samples+=1
            max_gap=max(max_gap,abs(value(after['movement'][1])-value(after['collision'][1])))
            previous=after
        first=trial['updates'][0]['after']
        first_end.append(dict(slot=trial['actor']['slot'],species=trial['actor']['species'],
            epsilon=trial['epsilon'],bounce=trial['bounceDetectedByActionEntry'],
            movementY=value(first['movement'][1]),collisionY=value(first['collision'][1]),
            displayY=value(first['display'][1]),particleFlags=first['particleFlags']))
    return dict(trials=tested,bounceDetections=bounces,updates=samples,species=groups,
                maxDetectedEndUpdateCollisionGap=max_gap,
                unequalEndUpdateY=sum(s['after']['movement'][1]!=s['after']['collision'][1]
                    for t in report['trials'] for s in t['updates']),
                unequalEndUpdateDisplayY=sum(s['after']['movement'][1]!=s['after']['display'][1]
                    for t in report['trials'] for s in t['updates']),
                firstUpdate=first_end,scope=report['scope'],observation=report['observation'])

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('report',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    d=json.loads(a.report.read_text(encoding='utf8'));r=summarize(d)
    r.update(reportSha256=hashlib.sha256(a.report.read_bytes()).hexdigest(),
             dllSha256=d['dllSha256'],captureSha256=d['captureSha256'],
             runtime=d['runtime'],poll=d['poll'],totalSeconds=d['totalSeconds'])
    a.output.write_text(json.dumps(r,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:r[k] for k in ('trials','bounceDetections','updates',
          'maxDetectedEndUpdateCollisionGap','unequalEndUpdateY','unequalEndUpdateDisplayY')}))

if __name__=='__main__':main()
