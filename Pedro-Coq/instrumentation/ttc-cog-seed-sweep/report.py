#!/usr/bin/env python3
"""Audit completed coverage and export metadata only, never captured game RAM."""
import csv
import json
import struct
from prepare import OUT, PROJECT, HERE, FRAMES, sha
from validate import invoke


def main():
    result = json.loads((OUT/'results.json').read_text())
    assert len(result['cases']) == 6
    reference = None
    comparisons = []
    for case in result['cases']:
        version, frame = case['version'], case['snapshot_frame']
        out = OUT/version
        csv_path = out/f'seeds-{frame}.csv'
        assert sha(csv_path) == case['csv_sha256']
        rows = list(csv.DictReader(csv_path.open()))
        assert [int(r['seed']) for r in rows] == list(range(65536))
        normalized = [{k:v for k,v in r.items() if k != 'pc'} for r in rows]
        if reference is None:
            reference = normalized
        comparisons.append(normalized == reference)
        # Replay all longest cases in isolation to check batch-state independence.
        for row in case['longest_cases']:
            replay, = invoke(version, FRAMES.index(frame), 1200, baseline=0, first=int(row['seed']))
            assert replay == row, (version, frame, row['seed'])
        build = json.loads((out/'build.json').read_text())
        trial = PROJECT/f'build/cog-placement/search_edge_a_stopped/seed_snapshot_{version}'
        raw = (trial/f'snapshots/{frame}-enter.ram').read_bytes()
        mario = build['symbols']['gMarioStates'][0] & 0x1fffffff
        case['starting_mario'] = {'position':list(struct.unpack_from('>fff',raw,mario+0x3c)),
                                  'forward_speed':struct.unpack_from('>f',raw,mario+0x54)[0],
                                  'action':f'{struct.unpack_from(">I",raw,mario+0xc)[0]:08x}'}
        case['snapshot_receipt'] = build['snapshots'][FRAMES.index(frame)]
        case['isolated_longest_replays'] = len(case['longest_cases'])
        case['longest_seeds'] = [int(r['seed']) for r in case.pop('longest_cases')]
        case.pop('command')  # Absolute local command paths are not a public artifact.
    result['all_six_normalized_csvs_identical'] = all(comparisons)
    result['total_seed_cases'] = sum(c['seed_count'] for c in result['cases'])
    result['hypothetical_initialization'] = {'clock_mode':'RANDOM','seed_range':[0,65535],
        'other_state':'retained from STOPPED snapshots','fixed_raw_stick':[75,28],'buttons':[]}
    result['evidence_class'] = 'finite offline execution under an explicit external-system boundary model; not a Coq theorem or reachable-gameplay exclusion'
    result['source_pin'] = '9921382a68bb0c865e5e45eb594d9c64db59b1af'
    result['source_sha256'] = {p.name:sha(p) for p in sorted(HERE.iterdir()) if p.suffix in ['.py','.c','.md']}
    result['validation'] = {v:json.loads((OUT/v/'validation.json').read_text()) for v in ['us','jp']}
    result['build_provenance'] = {}
    for version in ['us','jp']:
        build = json.loads((OUT/version/'build.json').read_text())
        result['build_provenance'][version] = {k:v for k,v in build.items() if k not in ['symbols','command','snapshot_directory']}
    result['random_calibration'] = json.loads((OUT/'random-calibration.json').read_text())
    destination = PROJECT/'docs/notes/ttc-cog-seed-sweep-results.json'
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'exported':str(destination),'seed_cases':result['total_seed_cases'],
                      'normalized_identical':result['all_six_normalized_csvs_identical']}))


if __name__ == '__main__':
    main()
