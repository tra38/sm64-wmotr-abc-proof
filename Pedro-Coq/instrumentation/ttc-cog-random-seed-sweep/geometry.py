#!/usr/bin/env python3
"""Sample the recorded cog angles with pinned collision code, without a replay."""
import json
import struct
import subprocess
import sys
from run import HERE, OUT, PROJECT, FRAME, sha

for version in ['us','jp']:
    # Reauthenticate source/inputs with the established small one-pose scan.
    subprocess.run([sys.executable,str(HERE.parent/'ttc-cog-geometry/run.py'),
                    '--angle-step','65536','--edge-segments','32','--version',version],
                   check=True,stdout=subprocess.DEVNULL)
    old=PROJECT/f'build/cog-geometry/{version}-step65536-edge32.json'
    receipt=json.loads(old.read_text())
    cmd=receipt['compiler']
    cmd[cmd.index(str(HERE.parent/'ttc-cog-geometry/search.c'))]=str(HERE/'geometry.c')
    exe=OUT/version/'geometry'
    cmd[-1]=str(exe)
    subprocess.run(cmd,check=True)
    trial=PROJECT/f'build/cog-placement/random_phase_snapshot_{version}'
    raw=(trial/f'snapshots/{FRAME}-enter.ram').read_bytes()
    pool=json.loads((trial/'manifest.json').read_text())['symbols']['gObjectPool']&0x1fffffff
    yaws=[struct.unpack_from('>i',raw,pool+s*0x260+0xd4)[0] for s in [29,30,31,32,33,34,35,94]]
    result=subprocess.check_output([str(exe),*map(str,yaws)],text=True)
    record={'version':version,'cog_yaws':yaws,'records':[json.loads(s) for s in result.splitlines()],
            'geometry_source_sha256':sha(HERE/'geometry.c'),'compiler':cmd,
            'source_authentication_sha256':sha(old),'snapshot_sha256':sha(trial/f'snapshots/{FRAME}-enter.ram'),
            'scope':'finite host geometry samples; no Mario entry, action continuation or N64 refinement'}
    (OUT/version/'geometry.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record['records']))
