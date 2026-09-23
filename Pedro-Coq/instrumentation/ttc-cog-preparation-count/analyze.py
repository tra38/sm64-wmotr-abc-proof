#!/usr/bin/env python3
"""Count recorded pause boundaries and reproduce the video's state product.

Read-only analysis of authenticated existing traces. No game execution,
state construction, reachability proof or all-preparation coverage claim.
"""
from collections import defaultdict
from decimal import Decimal, localcontext
import hashlib
import json
from math import prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
NOTES = PROJECT / 'docs/notes'

# Manual transcription of the supplied video's table at 4:00. These are
# assumptions of that table, not certified state domains for the real game.
VIDEO_ROWS = [
    ('rotating block', 6, 165),
    ('rotating triangular prism', 2, 170),
    ('pendulum', 4, 100),
    ('treadmill', 1, 135),
    ('pushers', 12, 264),
    ('cogs', 6, 259),
    ('spinning triangles', 2, 259),
    ('pit block', 1, 197),
    ('hands', 2, 13821),
    ('spinners', 14, 121),
    ('wheels', 6, 13821),
    ('elevators', 2, 181),
    ('thwomp', 1, 139),
    ('amps', 2, 1),
    ('bob-ombs', 2, 16),
    ('mario dust', 1, 2),
]
COGS = {29, 30, 31, 32, 33, 34, 35, 94}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace(path, expected_sha, version):
    assert sha(path) == expected_sha, path
    frames, inputs, cogs = {}, {}, defaultdict(dict)
    for line in path.read_text().splitlines():
        columns = line.split(',')
        if columns[0] not in {'CINPUT', 'CFRAME', 'CCOG'}:
            continue
        assert columns[1] == version.upper()
        row = dict(field.split('=', 1) for field in columns[2:])
        frame = int(row['rel'])
        dest = cogs[frame] if columns[0] == 'CCOG' else (
            frames if columns[0] == 'CFRAME' else inputs)
        key = int(row['slot']) if columns[0] == 'CCOG' else frame
        assert key not in dest
        dest[key] = row
    assert list(frames) == list(range(len(frames)))
    assert frames.keys() == inputs.keys() == cogs.keys()
    assert all(set(objects) == COGS for objects in cogs.values())
    assert all(row['mode'] == '2' and row['timeStop'] == '00000000'
               for row in frames.values())
    assert all([float(row[k]) for k in ('x', 'y', 'z')] == [1742, -2088, -125]
               for row in frames.values())
    assert all(all(int(row[k]) == 0 for k in ('x', 'y', 'A', 'B', 'Z', 'R', 'L'))
               for row in inputs.values())
    assert len({row['timer'] for row in frames.values()}) == len(frames)
    return frames, inputs, cogs


def logical(data, n):
    frames, inputs, cogs = data
    pointers = {'floor', 'ceil', 'floorOwner', 'ceilOwner', 'object'}
    def clean(row):
        return {k: v for k, v in row.items() if k not in pointers}
    return [(clean(frames[f]), inputs[f],
             [clean(cogs[f][s]) for s in sorted(COGS)]) for f in range(n)]


def census(data):
    frames, _, cogs = data
    selected = {s: {f for f in frames if float(cogs[f][s]['target']) == 0
                   and abs(float(cogs[f][s]['speed'])) <= 50} for s in COGS}
    lower, upper = selected[29], selected[32]
    return {
        'observed_boundaries': len(frames),
        'distinct_recorded_global_timers': len({r['timer'] for r in frames.values()}),
        'distinct_recorded_seeds': len({r['seed'] for r in frames.values()}),
        'zero_target_pause_counts_by_cog': {str(s): len(selected[s]) for s in sorted(COGS)},
        'lower_frames': sorted(lower), 'upper_frames': sorted(upper),
        'either_frames': sorted(lower | upper), 'both_frames': sorted(lower & upper),
        'either_count': len(lower | upper), 'both_count': len(lower & upper),
    }


def repeated_seed_example(data):
    frames, _, cogs = data
    by_seed = defaultdict(list)
    for f, row in frames.items():
        by_seed[int(row['seed'])].append(f)
    for seed, fs in by_seed.items():
        eligible = {f: any(float(cogs[f][s]['target']) == 0
                          and abs(float(cogs[f][s]['speed'])) <= 50
                          for s in (29, 32)) for f in fs}
        if len(set(eligible.values())) == 2:
            return {'seed': seed, 'boundaries': [
                {'frame': f, 'global_timer': int(frames[f]['timer']),
                 'either_pause_filter': eligible[f],
                 'cogs': {str(s): {k: cogs[f][s][k] for k in ('yaw', 'speed', 'target')}
                          for s in (29, 32)}} for f in fs]}
    raise AssertionError('Expected a repeated seed with different pause eligibility')


def main():
    receipt_path = NOTES / 'ttc-cog-random-seed-sweep-results.json'
    receipt = json.loads(receipt_path.read_text())
    survey = PROJECT / 'build/cog-placement/random_phase_survey_us/trace.csv'
    full = trace(survey, receipt['survey']['trace_sha256'], 'us')
    assert len(full[0]) == 11625
    captures, provenance = {}, {'survey_trace_sha256': sha(survey)}
    for v in ('us', 'jp'):
        path = PROJECT / f'build/cog-placement/random_phase_snapshot_{v}/trace.csv'
        captures[v] = trace(path, receipt['build_provenance'][v]['trace_sha256'], v)
        assert len(captures[v][0]) == 845
        provenance[f'{v}_prefix_trace_sha256'] = sha(path)
    assert logical(full, 845) == logical(captures['us'], 845)
    assert logical(captures['us'], 845) == logical(captures['jp'], 845)
    counts = {'us_survey': census(full),
              'us_prefix': census(captures['us']), 'jp_prefix': census(captures['jp'])}
    # Independent identities also check that an overlapping boundary is not
    # counted as two different starting states.
    for c in counts.values():
        assert c['either_count'] == len(c['lower_frames']) + len(c['upper_frames']) - c['both_count']
        assert c['both_frames'] == [836]
    image = PROJECT / 'build/cog-video-review/review-20260922-240.jpg'
    k = prod(states ** count for _, count, states in VIDEO_ROWS)
    baseline = max(Decimal(str(c['elapsed_seconds'])) for c in receipt['cases'])
    with localcontext() as ctx:
        ctx.prec = 40
        years = Decimal(k) * baseline / (Decimal('365.25') * 86400)
        video = {
            'source': 'user-supplied TTC Pedro Spot on Cogs Update, 4:00 table',
            'frame_sha256': sha(image),
            'source_game_version': 'unverified',
            'transcribed_rows': [{'label': label, 'count': count, 'states_each': states}
                                 for label, count, states in VIDEO_ROWS],
            'listed_row_multiplicity_excluding_dust': sum(c for _, c, _ in VIDEO_ROWS[:-1]),
            'non_seed_product_exact': str(k),
            'non_seed_product_scientific': f'{Decimal(k):.12E}',
            'video_seed_domain': 65114,
            'video_total_exact': str(k * 65114),
            'video_total_scientific': f'{Decimal(k * 65114):.12E}',
            'all_16_bit_seed_total_exact_per_version': str(k * 65536),
            'us_jp_full_seed_sweeps_years_at_baseline': f'{years:.12E}',
            'fixed_one_seed_per_preparation_years_at_mean_case_cost': f'{years / 65536:.12E}',
            'qualification': 'Arithmetic for the transcribed product only; neither a reachable-state count nor a proved lower/upper bound for complete TTC state.',
        }
    projections = []
    for name, count in [('matched_prefix_either', counts['us_prefix']['either_count']),
                        ('us_survey_lower', len(counts['us_survey']['lower_frames'])),
                        ('us_survey_upper', len(counts['us_survey']['upper_frames'])),
                        ('us_survey_either', counts['us_survey']['either_count'])]:
        seconds = baseline * count
        projections.append({'family': name, 'preparation_pairs_if_recaptured': count,
                            'seed_cases_us_jp': 131072 * count,
                            'seconds_at_baseline': str(seconds),
                            'hours_at_baseline': str(seconds / 3600)})
    result = {
        'date': '2026-09-23', 'source_pin': receipt['source_pin'],
        'evidence_class': 'existing-trace census and conditional arithmetic; no new game execution or proof',
        'definitions': {
            'literal_fixed_complete_state_inputs_and_seed': 'one deterministic continuation per version, including fixed external inputs',
            'preparation': 'complete non-seed initial state plus fixed continuation; a seed sweep varies the seed within it',
            'selection': 'incoming cog target equals zero and absolute speed is at most 50; this is not a geometry or Mario-preservation check',
        },
        'source_hashes': {**provenance, 'prior_receipt_sha256': sha(receipt_path), 'analyzer_sha256': sha(Path(__file__))},
        'counts': counts, 'same_seed_different_pause_example': repeated_seed_example(full),
        'us_jp_845_boundary_logical_prefix_identical': True,
        'video_product': video, 'baseline_pair_seconds': str(baseline),
        'conditional_projections': projections,
        'limits': [
            'Trace boundaries are not all captured complete checkpoints; the prefix only has snapshots at 836-838.',
            'The long 11,625-boundary census is US only; JP was checked only through boundary 844.',
            'Mario remains on the ledge; cog angle suitability, complete in-spot entry and preservation are unchecked for these new boundaries.',
            'Only the observed seed is reached at each boundary; substituted seed/state combinations need reachability evidence.',
            'Logical log equality is not whole-memory equivalence or a validated state quotient.',
            'Timings assume the same early-rejection cost and two-job hardware concurrency; recapture, validation, entry and reachability costs are excluded.',
            'No complete reachable preparation count, necessary search size or general solver runtime is established.',
        ],
    }
    target = NOTES / 'ttc-cog-preparation-count-results.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'counts': {name: {'boundaries': c['observed_boundaries'],
          'lower': len(c['lower_frames']), 'upper': len(c['upper_frames']),
          'either': c['either_count'], 'both': c['both_count']} for name, c in counts.items()},
          'video_non_seed_product': video['non_seed_product_scientific'],
          'video_conditional_years': video['us_jp_full_seed_sweeps_years_at_baseline'],
          'projections': projections}, indent=2))


if __name__ == '__main__':
    main()
