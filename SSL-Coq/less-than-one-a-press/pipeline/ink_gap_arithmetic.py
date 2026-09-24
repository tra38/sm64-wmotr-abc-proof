#!/usr/bin/env python3
"""Finite parameter calculations for the backward Ink gap review.

Uses the actual generated US/JP sine-table initializers. The arithmetic
recipes are read from the named C functions, not a replacement game model.
This is not a Coq proof, a gameplay replay or a reachable-state maximum.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct

ROOT = Path(__file__).resolve().parents[1]


def f32(value):
    return struct.unpack('<f', struct.pack('<f', value))[0]


def from_bits(value):
    return struct.unpack('<f', struct.pack('<I', value))[0]


def bits(value):
    return struct.unpack('<I', struct.pack('<f', value))[0]


def compute():
    tables, hashes = [], {}
    for version in ('us', 'jp'):
        path = ROOT / f'generated/{version}_math_util.v'
        text = path.read_text(encoding='utf-8')
        body = re.search(r'Definition v_gSineTable := \{\|(.*?)\|\}\.', text, re.S)[1]
        words = [int(word) & 0xFFFFFFFF for word in re.findall(
            r'Init_float32 \(Float32.of_bits \(Int.repr \(?(-?\d+)\)?\)\)', body)]
        assert len(words) == 5120
        tables.append(words)
        hashes[path.name] = hashlib.sha256(text.encode()).hexdigest()
    assert tables[0] == tables[1]
    sine = list(map(from_bits, tables[0]))
    assert all(-1 <= value <= 1 for value in sine)
    sin = lambda angle: sine[(angle & 65535) >> 4]
    pitch_offsets = [f32(f32(60 * sin(angle)) * sin(angle)) for angle in range(1, 32768)]
    reset_heights = [f32(f32(pitch / 256) + 20) for pitch in range(-32768, 32768)]
    active_bob_sines = [sin(timer) for timer in range(32768)]
    assert min(active_bob_sines) >= 0 and max(active_bob_sines) == 1
    # Every product is <= max(reset_heights): the sine is in [0,1].
    # Rounding finite binary32 numbers is monotone; both maxima are attained.
    # This argument bounds these expressions only, assuming reset's height
    # and the stock table survive until use. It is not a live-state invariant.
    pitch_max, bob_max = max(pitch_offsets), max(reset_heights)
    anchor = 768.0
    water_display = f32(f32(anchor + pitch_max) + bob_max)
    cannon_rises = [f32(120 * sin(pitch)) for pitch in range(0x38E3 + 1)]
    target = from_bits(1156733869)
    gap = f32(target - anchor)
    assert pitch_max == 60 and bob_max == 147.99609375
    assert water_display - anchor == 207.99609375
    assert min(cannon_rises) == 0 and min(cannon_rises) >= 0
    assert f32(anchor - (-gap)) == target
    return {
        'scope': 'Finite expression calculations, not a live gameplay bound or a Coq certificate.',
        'revision': '9921382a68bb0c865e5e45eb594d9c64db59b1af',
        'generated_sine_table_sha256': hashes,
        'us_jp_sine_entries_equal': 5120,
        'target': {'actual_y': anchor, 'display_y': target, 'display_bits': bits(target),
                   'required_gap': gap, 'required_gap_bits': bits(gap)},
        'shell': {'air_added_y': 42, 'ground_added_y': 45,
                  'air_display_at_anchor': f32(anchor + 42),
                  'ground_display_at_anchor': f32(anchor + 45)},
        'water': {'positive_pitch_cases': len(pitch_offsets), 'max_pitch_addend': pitch_max,
                  'reset_pitch_cases': len(reset_heights), 'min_reset_bob_height': min(reset_heights),
                  'max_reset_bob_height': bob_max, 'active_bob_timer_cases': len(active_bob_sines),
                  'display_at_anchor_with_independent_max_addends': water_display,
                  'gap_at_anchor_with_independent_max_addends': water_display - anchor,
                  'caveat': 'Generous independent parameter envelope after one water copy, with reset-derived bob height and the unchanged stock sine table. Joint controller reachability is not asserted; this does not bound repeated calls without a refresh or later support changes.'},
        'cannon': {'permitted_pitch_cases': len(cannon_rises), 'max_vertical_launch_step': max(cannon_rises),
                   'min_vertical_launch_step': min(cannon_rises),
                   'caveat': 'At the position writes, starting synchronized, display minus movement Y is nonpositive. The normal firing branch requires INPUT_A_PRESSED. Subsequent calls and action transitions are not modeled here.'},
        'negative_depth': {'one_subtraction_depth': -gap, 'result_display_y': f32(anchor + gap),
                           'caveat': 'An arithmetic witness, not creation of that depth, a dialog history or a clean Ink setup.'},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    output = ROOT / 'docs/notes/ink-gap-arithmetic.json'
    receipt = json.dumps(compute(), ensure_ascii=False, indent=2) + '\n'
    if args.check:
        if output.read_text(encoding='utf-8') != receipt:
            raise SystemExit('Stale Ink gap arithmetic receipt')
    else:
        output.write_text(receipt, encoding='utf-8', newline='\n')
    print('PASS: US/JP sine tables agree; 32767 pitch, 65536 bob-height and 32768 bob-timer values checked; fixed-anchor arithmetic reproduced.')


if __name__ == '__main__':
    main()
