"""Summarize exact chosen-XYZ diagnostic checkpoints, never as coverage."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from receipt import value

def bits(number):return struct.unpack('>I',struct.pack('>f',number))[0]

def summarize(report):
    outcomes=[]; max_end_collision=max_end_display=max_bounce_entry=0.
    for t in report['trials']:
        b=t['before']; patch=t['patch'];a=t['actor'];slot=a['slot']
        if b['movement']!=b['collision'] or b['movement']!=b['display']:
            raise ValueError('Unsynchronized supplied entry')
        y=value(b['movement'][1]);ey=patch['gObjectPool[%d].oPosY'%slot]
        first=t['samples'][0];events=first['events']
        actions=[e for e in events if e['type']=='FLT_EXECUTE_ACTION']
        snap=ey+a['height']
        bounced=bool(actions and actions[0]['vel'][1] in (30.,80.) and
                     bits(actions[0]['pos'][1])==bits(snap))
        if bounced:max_bounce_entry=max(max_bounce_entry,actions[0]['pos'][1]-y)
        previous=b
        for sample in t['samples']:
            end=sample['after']
            if end['frame']!=previous['frame']+1 or end['timer']!=previous['timer']+1:
                raise ValueError('Noncontinuous suffix')
            if end['buttonDown']&0x8000 or end['buttonPressed']&0x8000:
                raise ValueError('Unexpected A')
            max_end_collision=max(max_end_collision,abs(value(end['movement'][1])-value(end['collision'][1])))
            max_end_display=max(max_end_display,abs(value(end['movement'][1])-value(end['display'][1])))
            previous=end
        outcomes.append(dict(slot=slot,species=a['species'],position=[value(w) for w in b['movement']],
            actorY=ey,height=a['height'],radius=a['radius'],downOffset=a['downOffset'],
            tangible=a['tangible'],bounceAtFirstActionEntry=bounced,
            actionEntries=[dict(action=e['action'],position=e['pos'],vy=e['vel'][1]) for e in actions],
            firstFloorNull=first['floorNull'],firstWarpOperation=first['warpOperation'],
            firstEndY=[value(first['after'][r][1]) for r in ('movement','collision','display')]))
    return dict(schema=1,runtime=report['runtime'],poll=report['poll'],
        reportSha256=None,dllSha256=report['dllSha256'],captureSha256=report['captureSha256'],
        availableActors=report['availableActors'],testedActors=len(report['actors']),
        trials=len(report['trials']),updates=sum(len(t['samples']) for t in report['trials']),
        bounces=sum(t['bounceAtFirstActionEntry'] for t in outcomes),
        maxDetectedBounceEntryRise=max_bounce_entry,
        maxDetectedEndUpdateCollisionGap=max_end_collision,maxDetectedEndUpdateDisplayGap=max_end_display,
        outcomes=outcomes,scope=report['scope'],observation=report['observation'])

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('report',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=summarize(json.loads(a.report.read_text(encoding='utf8')))
    r['reportSha256']=hashlib.sha256(a.report.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(r,indent=2)+'\n',encoding='utf8')
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()
