#!/usr/bin/env python3
"""Authenticate read-only receipts and build the offline sweep executable."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
OUT = PROJECT / 'build/cog-seed-sweep'
FRAMES = [0, 30, 100]
PIN = '9921382a68bb0c865e5e45eb594d9c64db59b1af'
WHEEL_SHA256 = '9d6e6dea140560de4ebd8446661f7ef84a357d428c14a3ef09dacd306ec8c239'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(version):
    trial = PROJECT / f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
    manifest = json.loads((trial / 'manifest.json').read_text())
    assert manifest['version'] == version and manifest['initialization']['source_pin'] == PIN
    assert manifest['initialization']['mode'] == 'STOPPED'
    assert manifest['observer_sha256'] == sha(trial / 'observer.c')
    assert manifest['inputs_sha256'] == sha(trial / 'inputs.csv')
    assert (trial/'inputs.csv').read_bytes() == (HERE.parent/'ttc-cog-geometry/control-a-1200.csv').read_bytes()
    summary = json.loads((trial / 'summary.json').read_text())
    assert summary['cheats_disabled'] and not summary['observer_errors'] and summary['emulator_exit'] == 0
    elf = trial.parent / f'source/build/{version}/sm64.{version}.elf'
    assert sha(elf) == manifest['elf_sha256']
    symbols = {}
    for line in subprocess.check_output(['mips-linux-gnu-nm', '-n', '-S', str(elf)], text=True).splitlines():
        parts = line.split()
        if len(parts) == 4:
            symbols[parts[3]] = [int(parts[0],16), int(parts[1],16)]
    out = OUT / version
    out.mkdir(parents=True, exist_ok=True)
    header = (trial / 'addresses.h').read_text()
    macros = {k:int(v,16) for k,v in re.findall(r'#define (\w+) 0x([0-9a-f]+)u',header)}
    code_hashes = [(int(a,16),int(n),int(h,16)) for a,n,h in
                   re.findall(r'\{0x([0-9a-f]+)u, (\d+)u, 0x([0-9a-f]+)u\}', header)]
    code_hashes += [(macros['PC_AIR_ENTRY'],macros['AIR_WORD_COUNT'],macros['AIR_CODE_HASH']),
                    (macros['A_RANDOM_U16'],macros['RNG_WORD_COUNT'],macros['RNG_CODE_HASH'])]
    extra = {'GFX_SELECT':'select_gfx_pool', 'RENDER_FB':'sRenderedFramebuffer',
             'RENDERING_FB':'sRenderingFramebuffer','PROFILE_INDEX':'gCurrentFrameIndex1',
             'PROFILER':'gProfilerFrameData','AUDIO_TICK':'audio_game_loop_tick'}
    for macro, name in extra.items():
        header += f'#define {macro} 0x{symbols[name][0]:08x}u\n'
    arrays = []
    receipts = []
    for frame in FRAMES:
        path = trial / f'snapshots/{frame}-enter.ram'
        raw = path.read_bytes()
        state = json.loads(path.with_suffix('.json').read_text())
        end = json.loads((trial / f'snapshots/{frame}-exit.json').read_text())
        assert len(raw) == 0x800000
        assert state['frame'] == frame and end['frame'] == frame
        assert len(state['gpr']) == len(state['fpr']) == len(state['cp0']) == 32
        for address, count, expected in code_hashes:
            address &= 0x1fffffff
            value = 2166136261
            for i in range(count):
                value = ((value ^ int.from_bytes(raw[address+4*i:address+4*i+4], 'big'))*16777619) & 0xffffffff
            assert value == expected, (version, frame, hex(address))
        # Only declared fields may differ in a candidate's initialization.
        for slot in [29,32]:
            start = manifest['symbols']['gObjectPool'] + slot * 0x260
            for offset in [0xd4,0xf8,0xfc]:
                assert raw[(start+offset)&0x1fffffff:((start+offset)&0x1fffffff)+4] == bytes(4)
        arrays.append('{' + ','.join([str(frame),str(state['pc']),str(end['pc']),str(state['cp0'][12]),
            '{'+','.join('0x'+x+'ULL' for x in state['gpr'])+'}',
            '{'+','.join('0x'+x+'ULL' for x in state['fpr'])+'}']) + '}')
        receipts.append({'frame':frame, 'ram_sha256':sha(path), 'cpu_sha256':sha(path.with_suffix('.json'))})
    header += 'struct initial {unsigned frame,entry,finish,status; unsigned long long gpr[32],fpr[32];};\n'
    header += 'static const struct initial starts[]={' + ',\n'.join(arrays) + '};\n'
    (out / 'config.h').write_text(header)
    lib = OUT / 'python/unicorn'
    wheels = list((OUT/'packages').glob('unicorn-2.1.4-*.whl'))
    assert len(wheels) == 1 and sha(wheels[0]) == WHEEL_SHA256
    command = ['gcc','-std=c11','-O2','-Wall','-Wextra','-Werror','-I'+str(lib/'include'),
               '-I'+str(out),str(HERE/'sweep.c'),str(lib/'lib/libunicorn.so.2'),
               '-Wl,-rpath,'+str(lib/'lib'),'-o',str(out/'sweep')]
    subprocess.run(command,check=True)
    receipt = {'version':version,'frames':FRAMES,'snapshots':receipts,'source_pin':PIN,
               'unicorn_wheel_sha256':WHEEL_SHA256,'unicorn_library_sha256':sha(lib/'lib/libunicorn.so.2'),
               'trial_manifest_sha256':sha(trial/'manifest.json'), 'trace_sha256':sha(trial/'trace.csv'),
               'elf_sha256':sha(elf),'config_sha256':sha(out/'config.h'),'sweep_source_sha256':sha(HERE/'sweep.c'),
               'executable_sha256':sha(out/'sweep'),'symbols':symbols,'command':command,
               'snapshot_directory':str(trial/'snapshots')}
    (out/'build.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'version':version,'executable':str(out/'sweep')}))


if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('version',choices=['us','jp'])
    prepare(p.parse_args().version)
