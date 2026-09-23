#!/usr/bin/env python3
"""Compare the offline executor to captured emulator continuations.

This is empirical calibration, not a CPU or external-system refinement proof.
Full RAM difference inventories are retained, even outside the required regions.
"""
import bisect
import collections
import csv
import io
import json
import os
from pathlib import Path
import subprocess

from prepare import OUT, PROJECT, FRAMES, sha


def invoke(version, case, horizon, baseline=1, first=0, count=1, save=None, env=None):
    trial = PROJECT / f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
    cmd = [str(OUT/version/'sweep'), str(trial/'snapshots'), str(case), str(first),
           str(count), str(horizon), str(baseline)]
    if save:
        cmd.append(str(save))
    result = subprocess.run(cmd, capture_output=True, text=True, check=True, timeout=60,
                            env={**os.environ, **(env or {})})
    return list(csv.DictReader(io.StringIO(result.stdout)))


def trace_draws(path, first, last, pool):
    result = []
    for line in path.read_text().splitlines():
        if not line.startswith('CRNG,'):
            continue
        fields = dict(item.split('=', 1) for item in line.split(',')[2:])
        if first <= int(fields['rel']) <= last:
            result.append((int(fields['before']), (int(fields['object'], 16)-pool)//0x260))
    value = 14695981039346656037
    for draw in result:
        for part in draw:
            value = ((value ^ part)*1099511628211) & ((1 << 64)-1)
    return len(result), f'{value:016x}'


def differences(actual, expected, symbols):
    ordered = sorted((a, n, s) for n, (a, s) in symbols.items() if s and a >= 0x80000000)
    addresses = [a for a, n, s in ordered]
    groups = collections.Counter()
    for i, (a, b) in enumerate(zip(actual, expected)):
        if a == b:
            continue
        address = i+0x80000000
        index = bisect.bisect_right(addresses, address)-1
        start, name, size = ordered[index]
        groups[name if start <= address < start+size else f'unmapped-symbol-{address>>12:x}'] += 1
    return dict(groups.most_common())


def validate(version):
    out = OUT/version
    build = json.loads((out/'build.json').read_text())
    trial = PROJECT/f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
    manifest = json.loads((trial/'manifest.json').read_text())
    symbols = build['symbols']
    # Byte identity here covers whole structures, not only the preservation fields.
    required = ['gObjectPool', 'gMarioStates', 'gMarioPlatform', 'gLakituState',
                'gCurrentObject', 'gGlobalTimer', 'gControllers', 'gGfxPools',
                'gMatStack', 'gTimeStopState', 'gTTCSpeedSetting']
    cases = [(i, h) for i in range(len(FRAMES)) for h in [1, 2]] + [(0, 102)]
    receipts = []
    for case, horizon in cases:
        frame = FRAMES[case]
        save = out/f'validation-{frame}-{horizon}.ram'
        row, = invoke(version, case, horizon, save=save)
        assert row['status'] == 'survived', row
        assert int(row['complete_updates']) == horizon
        actual = save.read_bytes()
        expected_path = trial/f'snapshots/{frame+horizon-1}-exit.ram'
        expected = expected_path.read_bytes()
        for name in required:
            address, size = symbols[name]; address &= 0x1fffffff
            assert actual[address:address+size] == expected[address:address+size], (version, frame, horizon, name)
        count, digest = trace_draws(trial/'trace.csv', frame, frame+horizon-1, symbols['gObjectPool'][0])
        assert int(row['rng_calls']) == count and row['rng_hash'] == digest, (version, frame, row, count, digest)
        seed_address = manifest['symbols']['gRandomSeed16 (verified static load)'] & 0x1fffffff
        assert actual[seed_address:seed_address+2] == expected[seed_address:seed_address+2]
        receipts.append({'frame': frame, 'updates': horizon, 'result': row,
                         'expected_sha256': sha(expected_path), 'actual_sha256': sha(save),
                         'full_ram_differences': differences(actual, expected, symbols)})
    positive, = invoke(version, 0, 102, baseline=2)
    assert positive['status'] == 'survived' and positive['complete_updates'] == '102', positive
    unknown, = invoke(version, 0, 1200, baseline=0, env={'SWEEP_FUEL': '1'})
    assert unknown['status'] == 'unknown' and unknown['reason'] == 'instruction-budget', unknown
    batch = invoke(version, 0, 1200, baseline=0, first=0, count=128)
    longest = max(batch, key=lambda r: int(r['complete_updates']))
    isolated, = invoke(version, 0, 1200, baseline=0, first=int(longest['seed']))
    assert isolated == longest, (isolated, longest)
    second_batch = invoke(version, 0, 1200, baseline=0, first=int(longest['seed']), count=2)
    assert second_batch[0] == isolated
    # Horizon boundary must accept a stationary last update even when a nonzero
    # target has just been chosen; movement on the next update rejects it.
    one, = invoke(version, 0, 1, baseline=0, first=0)
    two, = invoke(version, 0, 2, baseline=0, first=0)
    assert one['status'] == 'survived' and two['status'] == 'rejected' and two['complete_updates'] == '1'
    report = {'version': version, 'build_sha256': sha(out/'build.json'), 'required_identical_regions': required,
              'baselines': receipts, 'positive_preservation': positive, 'fuel_exhaustion': unknown,
              'seed_isolation': isolated, 'last_update_selection': one, 'next_update_movement': two}
    (out/'validation.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'version': version, 'validated': len(cases), 'positive_updates': 102,
                      'full_ram_difference_symbols': sorted(set().union(*(r['full_ram_differences'] for r in receipts)))}))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('version', choices=['us', 'jp'])
    validate(parser.parse_args().version)
