#!/usr/bin/env python3
"""Offline bounded execution of read-only placement receipts.

Candidate initialization is local to this evaluator. No emulator, ROM, or
running game is changed. Unsupported execution is unknown, never rejection.
"""
import argparse
import json
from pathlib import Path
import struct
import sys
import time

PROJECT = Path(__file__).resolve().parents[2]
OUT = PROJECT / 'build/cog-seed-sweep'
sys.path.insert(0, str(OUT / 'python'))
import unicorn as uc
from unicorn import mips_const as mc


def sx(address):
    return address | 0xffffffff00000000 if address & 0x80000000 else address


def load_trial(version):
    trial = PROJECT / f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
    return trial, json.loads((trial / 'manifest.json').read_text())


class Execution:
    def __init__(self, trial, manifest, frame):
        self.manifest = manifest
        self.symbols = manifest['symbols']
        self.initial = (trial / f'snapshots/{frame}-enter.ram').read_bytes()
        self.state = json.loads((trial / f'snapshots/{frame}-enter.json').read_text())
        self.finish = json.loads((trial / f'snapshots/{frame}-exit.json').read_text())['pc']
        self.vm = uc.Uc(uc.UC_ARCH_MIPS, uc.UC_MODE_MIPS64 | uc.UC_MODE_BIG_ENDIAN)
        self.vm.ctl_set_cpu_model(mc.UC_CPU_MIPS64_R4000)
        self.vm.mem_map(0, len(self.initial))
        self.vm.mem_write(0, self.initial)
        self.vm.reg_write(mc.UC_MIPS_REG_CP0_STATUS, self.state['cp0'][12])
        self.vm.reg_write(mc.UC_MIPS_REG_HI, 0)
        self.vm.reg_write(mc.UC_MIPS_REG_LO, 0)
        self.vm.reg_write(mc.UC_MIPS_REG_FCSR, 0)
        for i, value in enumerate(self.state['gpr']):
            self.vm.reg_write(mc.UC_MIPS_REG_0 + i, int(value, 16))
        for i, value in enumerate(self.state['fpr']):
            self.vm.reg_write(mc.UC_MIPS_REG_F0 + i, int(value, 16))
        self.rng = []
        self.finished = False
        self.unmapped = []
        self.vm.hook_add(uc.UC_HOOK_MEM_UNMAPPED, self.on_unmapped)
        rng = sx(self.symbols['random_u16'])
        self.vm.hook_add(uc.UC_HOOK_CODE, self.on_rng, begin=rng, end=rng)
        self.vm.hook_add(uc.UC_HOOK_CODE, self.on_finish, begin=sx(self.finish), end=sx(self.finish))

    def on_finish(self, vm, address, size, data):
        self.finished = True
        vm.emu_stop()

    def on_unmapped(self, vm, access, address, size, value, data):
        self.unmapped.append({'access':access,'address':hex(address),'size':size})
        return False

    def read(self, address, size=4):
        return int.from_bytes(self.vm.mem_read(address & 0x1fffffff, size), 'big')

    def on_rng(self, vm, address, size, data):
        self.rng.append([self.read(self.symbols['gRandomSeed16 (verified static load)'], 2),
                         self.read(self.symbols['gCurrentObject'])])

    def run(self, seed=None, random_mode=False, fuel=5000000):
        if seed is not None:
            self.vm.mem_write(self.symbols['gRandomSeed16 (verified static load)'] & 0x1fffffff,
                              struct.pack('>H', seed))
        if random_mode:
            self.vm.mem_write(self.symbols['gTTCSpeedSetting'] & 0x1fffffff, b'\0\2')
        start = time.perf_counter()
        error = None
        try:
            self.vm.emu_start(sx(self.state['pc']), 0, timeout=10000000, count=fuel)
        except uc.UcError as exc:
            error = str(exc)
        pc = self.vm.reg_read(mc.UC_MIPS_REG_PC)
        return {'status': 'complete' if self.finished and error is None else 'unknown',
                'error': error, 'pc': hex(pc),
                'seconds': time.perf_counter()-start, 'rng': self.rng}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('version', choices=['us','jp'])
    p.add_argument('--frame', type=int, default=0)
    p.add_argument('--seed', type=int)
    p.add_argument('--random-mode', action='store_true')
    p.add_argument('--trial', type=Path, help='read-only receipt directory; defaults to the STOPPED sweep trial')
    a = p.parse_args()
    trial, manifest = load_trial(a.version)
    if a.trial:
        trial = a.trial
        manifest = json.loads((trial/'manifest.json').read_text())
    if a.seed is not None and not 0 <= a.seed <= 65535:
        p.error('seed must be in 0..65535')
    e = Execution(trial, manifest, a.frame)
    result = e.run(a.seed, a.random_mode)
    if a.seed is None and not a.random_mode:
        actual = bytes(e.vm.mem_read(0, len(e.initial)))
        expected = (trial / f'snapshots/{a.frame}-exit.ram').read_bytes()
        differences = [i for i in range(len(actual)) if actual[i] != expected[i]]
        result['different_bytes'] = len(differences)
        result['first_differences'] = [hex(i+0x80000000) for i in differences[:25]]
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
