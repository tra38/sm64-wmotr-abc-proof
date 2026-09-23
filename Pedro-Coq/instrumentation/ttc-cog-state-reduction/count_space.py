#!/usr/bin/env python3
"""Arithmetic comparison of checked local domains with the video's product.

This does not enumerate reachable states or execute any game transition.
"""
from decimal import Decimal, localcontext
import hashlib
import json
from math import prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
NOTES = PROJECT / 'docs/notes'


def main():
    files = {name: NOTES / name for name in ('ttc-cog-preparation-count-results.json',
                                           'ttc-cog-state-reduction-results.json')}
    census, reductions = (json.loads(p.read_text()) for p in files.values())
    rows = census['video_product']['transcribed_rows']
    cog_rows = [r for r in rows if r['label'] in ('cogs', 'spinning triangles')]
    spinner_rows = [r for r in rows if r['label'] == 'spinners']
    nc, ns = sum(r['count'] for r in cog_rows), sum(r['count'] for r in spinner_rows)
    assert nc == 8 and ns == 14
    assert all(r['states_each'] == 259 for r in cog_rows)
    assert all(r['states_each'] == 121 for r in spinner_rows)
    video = prod(r['states_each'] ** r['count'] for r in rows)
    assert video == int(census['video_product']['non_seed_product_exact'])
    rest = video // (259 ** nc * 121 ** ns)
    assert rest * 259 ** nc * 121 ** ns == video
    for version in ('us', 'jp'):
        assert [reductions['versions'][version][key]['reduced_states']
                for key in ('cog', 'spinner', 'spinner_extended')] == [480, 121, 122]

    with localcontext() as ctx:
        ctx.prec = 65
        seconds = Decimal(census['baseline_pair_seconds'])
        seconds_per_year = Decimal('365.25') * 24 * 60 * 60
        variants = []
        for name, c, s in [('video', 259, 121), ('hybrid_recurrent', 480, 121),
                           ('hybrid_extended_spinner', 480, 122)]:
            partial = c ** nc * s ** ns
            total = rest * partial
            variants.append({
                'name': name, 'cog_states_each': c, 'spinner_states_each': s,
                'cog_spinner_cartesian_product_exact': str(partial),
                'cog_spinner_cartesian_product_scientific': f'{Decimal(partial):.15E}',
                'non_seed_product_exact': str(total),
                'non_seed_product_scientific': f'{Decimal(total):.15E}',
                'times_video_nonseed': str(Decimal(total) / video),
                'with_65114_seeds_per_version': f'{Decimal(total * 65114):.15E}',
                'with_65536_seeds_per_version': f'{Decimal(total * 65536):.15E}',
                'conditional_us_jp_full_sweep_years': f'{Decimal(total) * seconds / seconds_per_year:.15E}',
            })
        report = {
            'evidence_class': 'exact integer products and conditional timing arithmetic; no new execution or proof',
            'source_pin': census['source_pin'],
            'input_sha256': {n: hashlib.sha256(p.read_bytes()).hexdigest() for n, p in files.items()},
            'inherited_video_multiplicities': {'cogs_and_spinning_triangles': nc, 'spinners': ns},
            'unchanged_other_video_factors_exact': str(rest),
            'variants': variants,
            'timing': {'seconds_per_full_us_jp_preparation_pair': str(seconds),
                       'days_per_year': '365.25',
                       'meaning': 'arithmetic at the prior full-game early-rejection sweep rate; not a reduced-scheduler benchmark or runtime guarantee'},
            'implemented_random_sweep': {'preparation_pairs': 1, 'seeds_per_version': 65536,
                                         'us_jp_seed_cases': 131072, 'complete_in_spot_preparation': False},
            'limits': [
                'Hybrids replace only the eight cog-like and fourteen spinner factors; all other video counts remain unproved assumptions.',
                'Local scheduling equivalence has not been composed with actual activation, ordering, geometry or Mario preservation.',
                'Cartesian products need not be jointly reachable or complete for the real game; they are neither certified upper nor lower bounds.',
                '447296 counts prior local validation comparisons, not full-game preparations or seed cases.',
                'No new certified total full-game preparation count, solver speedup or 1200-update RANDOM witness follows.'
            ],
        }
    output = NOTES / 'ttc-cog-search-space-results.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    for row in variants:
        print(row['name'], row['non_seed_product_scientific'], row['conditional_us_jp_full_sweep_years'])


if __name__ == '__main__':
    main()
