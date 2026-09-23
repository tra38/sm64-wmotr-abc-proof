#!/usr/bin/env python3
"""Finite, generated-AST/native-C audit of two LOCAL RNG-schedule quotients.

No ROM, emulator, game state or proof files are changed. This host checker is
not a verified Clight interpreter or a whole-game abstraction theorem.
"""
import argparse
from itertools import product
import hashlib
import json
from pathlib import Path
import re
import subprocess

from ast_exec import Engine, as_float, bits, rng

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
SOURCE = PROJECT.parent.parent / 'reference-sm64-decomp'
PIN = '9921382a68bb0c865e5e45eb594d9c64db59b1af'
OUT = PROJECT / 'build/cog-state-reduction'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def extract_function(text, name):
    start = re.search(r'^(?:static )?(?:void|s32|s16) ' + name + r'\([^;]*?\) \{', text, re.M).start()
    i, depth = text.index('{', start) + 1, 1
    while depth:
        depth += (text[i] == '{') - (text[i] == '}')
        i += 1
    return text[start:i]


def native(cc, cases, helper_words):
    sources = {}

    def source(path):
        if path not in sources:
            sources[path] = subprocess.check_output([
                'git', '-c', f'safe.directory={SOURCE}', '-C', str(SOURCE),
                'show', f'{PIN}:{path}']).decode()
        return sources[path]

    functions = {}
    for path, names in [
        ('src/game/obj_behaviors_2.c', ['approach_f32_ptr', 'random_mod_offset']),
        ('src/engine/behavior_script.c', ['random_sign']),
        ('src/game/behaviors/ttc_cog.inc.c', ['bhv_ttc_cog_update']),
        ('src/game/behaviors/ttc_spinner.inc.c', ['bhv_ttc_spinner_update']),
    ]:
        for name in names:
            functions[name] = extract_function(source(path), name)

    constants = []
    for file, name in [('ttc_cog', 'sTTCCogNormalSpeeds'), ('ttc_spinner', 'sTTCSpinnerSpeeds')]:
        text = source(f'src/game/behaviors/{file}.inc.c')
        constants.append(re.search(r'static s16 ' + name + r'\[\] = \{.*?\};', text, re.S)[0])

    # The raw word indices independently agree with the generated expressions.
    fields = source('include/object_fields.h')
    names = ['oTTCCogDir', 'oTTCCogSpeed', 'oTTCCogTargetVel', 'oTTCSpinnerDir',
             'oTTCChangeDirTimer', 'oTimer', 'oFaceAngleYaw', 'oAngleVelYaw',
             'oFaceAnglePitch', 'oAngleVelPitch', 'O_FACE_ANGLE_PITCH_INDEX',
             'O_FACE_ANGLE_YAW_INDEX', 'O_FACE_ANGLE_INDEX']
    field_macros = []
    for name in names:
        matches = re.findall(r'^#define\s+(?:/\*.*?\*/\s+)?' + name + r'\s+[^\n]*$', fields, re.M)
        assert len(matches) == 1, (name, matches)
        field_macros.extend(matches)
    constants_text = source('include/object_constants.h')
    for name in ['TTC_SPEED_SLOW', 'TTC_SPEED_FAST', 'TTC_SPEED_RANDOM', 'TTC_SPEED_STOPPED']:
        matches = re.findall(r'^#define\s+' + name + r'\s+[^\n]*$', constants_text, re.M)
        assert len(matches) == 1, name
        field_macros.extend(matches)

    header = r'''
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
typedef float f32;
typedef int32_t s32;
typedef int16_t s16;
typedef uint16_t u16;
typedef uint32_t u32;
struct Object { union { s32 asS32[80]; u32 asU32[80]; f32 asF32[80]; } rawData; };
static struct Object object, *gCurrentObject = &object;
static s16 gTTCSpeedSetting = 2;
static u16 words[2];
static unsigned draws;
#define o gCurrentObject
#define TRUE 1
#define FALSE 0
#define OBJECT_FIELD_S32(i) rawData.asS32[i]
#define OBJECT_FIELD_F32(i) rawData.asF32[i]
u16 random_u16(void) { assert(draws < 2); return words[draws++]; }
'''
    main = r'''
int main(void) {
    unsigned kind, a, b, w0, w1;
    int dir;
    while (scanf("%u %u %u %d %u %u", &kind, &a, &b, &dir, &w0, &w1) == 6) {
        assert(w0 <= 65535 && w1 <= 65535);
        memset(&object, 0, sizeof(object));
        words[0] = w0; words[1] = w1; draws = 0;
        if (kind == 0) {
            memcpy(&o->oTTCCogSpeed, &a, sizeof(a));
            memcpy(&o->oTTCCogTargetVel, &b, sizeof(b));
            o->oTTCCogDir = dir;
            bhv_ttc_cog_update();
            memcpy(&a, &o->oTTCCogSpeed, sizeof(a));
            memcpy(&b, &o->oTTCCogTargetVel, sizeof(b));
            printf("%u %u %u %d %d\n", draws, a, b, o->oFaceAngleYaw, o->oAngleVelYaw);
        } else if (kind == 1) {
            o->oTimer = a; o->oTTCChangeDirTimer = b; o->oTTCSpinnerDir = dir;
            bhv_ttc_spinner_update();
            assert(o->oTimer < 0x3fffffff);
            o->oTimer++; /* explicit generic-update boundary contract */
            printf("%u %d %d %d %d %d\n", draws, o->oTimer, o->oTTCChangeDirTimer,
                   o->oTTCSpinnerDir, o->oFaceAnglePitch, o->oAngleVelPitch);
        } else {
            assert(kind == 2 || kind == 3);
            s32 value = kind == 2 ? random_sign() : random_mod_offset(30, 30, 4);
            printf("%u %d\n", draws, value);
        }
    }
    return ferror(stdin) || ferror(stdout) ? 1 : 0;
}
'''
    harness = '\n'.join([header, *field_macros, *constants, *functions.values(), main])
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / 'unchanged-native-bodies.c'
    path.write_text(harness)
    executable = OUT / 'unchanged-native-bodies'
    flags = ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-fno-fast-math', '-ffp-contract=off']
    subprocess.run([cc, *flags, str(path), '-o', str(executable)], check=True)
    lines = []
    for kind, a, b, direction, w0, w1 in cases:
        if kind == 0:
            a, b = bits(a), bits(b)
        lines.append(f'{kind} {a} {b} {direction} {w0} {w1}\n')
    # All 16-bit selector inputs, independent of the quotient-state enumeration.
    for w in helper_words:
        lines.extend([f'0 0 0 1 {w} 32767\n', f'2 0 0 1 {w} 0\n', f'3 0 0 1 {w} 0\n'])
    data = subprocess.check_output([str(executable)], input=''.join(lines).encode())
    rows = [list(map(int, line.split())) for line in data.splitlines()]
    assert len(rows) == len(cases) + 3 * len(helper_words)
    return rows, {
        'compiler': subprocess.check_output([cc, '--version'], text=True).splitlines()[0],
        'compiler_flags': flags,
        'source_files_sha256': {p: sha(s.encode()) for p, s in sources.items()},
        'extracted_functions_sha256': {n: sha(s.encode()) for n, s in functions.items()},
        'harness_sha256': sha(harness.encode()),
        'output_sha256': sha(data),
    }


def cog_key(speed, target):
    delta = abs(target - speed)
    assert delta % 50 == 0
    return int(target), max(1, int(delta // 50))


def spinner_key(timer, threshold, direction):
    assert direction in (-1, 0, 1)
    return max(0, threshold - timer + 1)


def check_selector_structure(engine):
    """Check why all raw-word pairs factor through the finite input alphabet.

    Each RNG temporary has just the recorded use. Thus values in one modulo
    or sign class are interchangeable here; we do not pretend the pair space
    of 2**32 raw words was directly enumerated at every local state.
    """
    def nodes(node):
        if isinstance(node, list):
            yield node
            for child in node:
                yield from nodes(child)

    expected = {
        '_bhv_ttc_cog_update': ['_approach_f32_ptr', '_random_u16', '_random_sign'],
        '_bhv_ttc_spinner_update': ['_random_sign', '_random_mod_offset'],
        '_approach_f32_ptr': [],
        '_random_sign': ['_random_u16'],
        '_random_mod_offset': ['_random_u16'],
    }
    for name, callees in expected.items():
        body = engine.functions[name][1]
        calls = [n for n in nodes(body) if n[0] == 'Scall']
        assert [n[2][1] for n in calls] == callees

    for name, operator, right in [
        ('_bhv_ttc_cog_update', 'Omod', ['Econst_int', ['Int.repr', '7'], 'tint']),
        ('_random_sign', 'Oge', ['Econst_int', ['Int.repr', '32767'], 'tint']),
        ('_random_mod_offset', 'Omod', ['Etempvar', '_mod', 'tshort']),
    ]:
        body = engine.functions[name][1]
        raw_use = ['Etempvar', "_t'1", 'tushort']
        assert sum(n == raw_use for n in nodes(body)) == 1
        assert ['Ebinop', operator, raw_use, right, 'tint'] in list(nodes(body))

    body = engine.functions['_bhv_ttc_spinner_update'][1]
    call = next(n for n in nodes(body) if n[0] == 'Scall' and n[2][1] == '_random_mod_offset')
    expected_args = [["Econst_int", ["Int.repr", str(i)], "tint"] for i in (30, 30, 4)]
    from ast_exec import coq_list
    assert coq_list(call[3]) == expected_args


def partition_refinement(transitions):
    """Coarsest draw-count/labelled-successor congruence in this finite table."""
    states = list(transitions)
    colors = dict.fromkeys(states, 0)
    rounds = []
    while True:
        signatures = {}
        next_colors = {}
        for s in states:
            signature = tuple((draws, colors[t]) for draws, t in transitions[s])
            next_colors[s] = signatures.setdefault(signature, len(signatures))
        rounds.append(len(signatures))
        if next_colors == colors:
            return next_colors, rounds
        colors = next_colors


def quotient(kind, states, alphabet, rows):
    key = cog_key if kind == 0 else spinner_key
    concrete, reduced = {}, {}
    observed_keys = {key(*s) for s in states}
    all_states = set(states)
    for state in states:
        concrete[state] = []
        for letter in alphabet:
            out = rows[(state, letter)]
            if kind == 0:
                successor = tuple(int(as_float(b)) for b in out[1:3])
            else:
                successor = tuple(out[1:4])
            assert successor in all_states, ('closure', state, letter, out)
            observation = out[0], key(*successor)
            assert observation[1] in observed_keys
            reduced_key = key(*state), letter
            if reduced_key in reduced:
                assert reduced[reduced_key] == observation, ('congruence', state, letter)
            reduced[reduced_key] = observation
            concrete[state].append((out[0], successor))

    colors, rounds = partition_refinement(concrete)
    # Countdown keys might be sufficient without being minimal. Check both ways.
    by_key, by_color = {}, {}
    for s, color in colors.items():
        k = key(*s)
        by_key.setdefault(k, set()).add(color)
        by_color.setdefault(color, set()).add(k)
    assert all(len(v) == 1 for v in by_key.values())
    minimum = len(by_color)
    equivalent_minimal_partition = all(len(v) == 1 for v in by_color.values())
    table = [{'state': k, 'input': letter, 'draws': obs[0], 'next': obs[1]}
             for (k, letter), obs in sorted(reduced.items())]
    return {
        'numeric_concrete_states': len(states),
        'reduced_states': len(observed_keys),
        'outcome_classes': len(alphabet),
        'closed': True,
        'draw_count_and_successor_congruence': True,
        'minimal_states_for_this_local_input_output_contract': minimum,
        'proposed_key_equals_minimal_partition': equivalent_minimal_partition,
        'partition_refinement_class_counts': rounds,
        'quotient_transition_count': len(table),
        'quotient_transition_sha256': sha(canonical(table)),
    }, table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cc', default='gcc')
    parser.add_argument('--output', type=Path, default=PROJECT / 'docs/notes/ttc-cog-state-reduction-results.json')
    args = parser.parse_args()
    engines = {v: Engine(v) for v in ('us', 'jp')}
    for engine in engines.values():
        check_selector_structure(engine)
    for name, text in engines['us'].texts.items():
        normalize = lambda s: re.sub(r'__\d+', '__UNION', s)
        assert normalize(text) == normalize(engines['jp'].texts[name]), name
    assert engines['us'].speeds == engines['jp'].speeds

    cog_states = list(product(range(-1200, 1201, 50), range(-1200, 1201, 200)))
    cog_letters = list(product(range(7), (0, 32767)))
    spinner_states = [(timer, threshold, direction) for threshold in (30, 60, 90, 120)
                      for timer in range(1, threshold + 2) for direction in (-1, 1)]
    spinner_extended = [(timer, threshold, direction) for threshold in (0, 30, 60, 90, 120)
                        for timer in range(threshold + 2) for direction in (-1, 0, 1)]
    spinner_letters = list(product((0, 32767), range(4)))
    # Every numeric cog state plus all distinct binary32 signs of zero.
    cog_bit_states = [(s, t) for s in [*range(-1200, 1201, 50), -0.0]
                      for t in [*range(-1200, 1201, 200), -0.0]]
    cases = [(0, s, t, d, *letter) for s, t in cog_bit_states
             for d in (-1, 1) for letter in cog_letters]
    cases += [(1, timer, threshold, d, *letter) for timer, threshold, d in spinner_extended
              for letter in spinner_letters]
    raw_words = range(65536)
    print(f'Checking {len(cases)} local transition cases and {3 * len(raw_words)} selector cases per version.', flush=True)
    native_rows, provenance = native(args.cc, cases, raw_words)
    results = {}
    for version, engine in engines.items():
        cog_rows, spinner_rows = {}, {}
        for case, expected in zip(cases, native_rows):
            actual = engine.run(case)
            assert actual == expected, (version, case, actual, expected)
            kind, a, b, d, w0, w1 = case
            row_key = ((int(a), int(b)), (w0, w1)) if kind == 0 else ((a, b, d), (w0, w1))
            target_rows = cog_rows if kind == 0 else spinner_rows
            if row_key in target_rows:
                # Direction and signed zero can change angle/bit observations;
                # they must never change the proposed RNG quotient successor.
                prior = target_rows[row_key]
                assert prior[0] == actual[0]
                assert tuple(as_float(x) for x in prior[1:3]) == tuple(as_float(x) for x in actual[1:3])
            target_rows[row_key] = actual

        for i, w in enumerate(raw_words):
            actual_cog = engine.run((0, 0, 0, 1, w, 32767))
            engine.reset([w]); sign = engine.call('_random_sign', [])
            actual_sign = [len(engine.draws), sign]
            engine.reset([w]); timer = engine.call('_random_mod_offset', [30, 30, 4])
            actual_timer = [len(engine.draws), timer]
            actual = [actual_cog, actual_sign, actual_timer]
            expected = native_rows[len(cases) + 3*i:len(cases) + 3*i + 3]
            assert actual == expected, (version, w, actual, expected)
            assert as_float(actual_cog[2]) == 200 * (w % 7)
            assert sign == (1 if w >= 32767 else -1)
            assert timer == 30 + 30 * (w % 4)

        cog, cog_table = quotient(0, cog_states, cog_letters, cog_rows)
        spinner, spinner_table = quotient(1, spinner_states, spinner_letters, spinner_rows)
        extended, extended_table = quotient(1, spinner_extended, spinner_letters, spinner_rows)
        assert cog['reduced_states'] == 480 and spinner['reduced_states'] == 121 and extended['reduced_states'] == 122
        (OUT / f'{version}-cog-quotient.json').write_bytes(canonical(cog_table) + b'\n')
        (OUT / f'{version}-spinner-quotient.json').write_bytes(canonical(spinner_table) + b'\n')
        (OUT / f'{version}-spinner-extended-quotient.json').write_bytes(canonical(extended_table) + b'\n')
        results[version] = {
            'local_transition_cases': len(cases),
            'selector_cases': 3 * len(raw_words),
            'generated_ast_native_mismatches': 0,
            'generated_function_sha256': {n: sha(t.encode()) for n, t in engine.texts.items()},
            'cog': cog, 'spinner': spinner, 'spinner_extended': extended,
        }
        print(f'{version}: cog {len(cog_states)} -> {cog["reduced_states"]}; spinner {len(spinner_states)} -> {spinner["reduced_states"]}; extended spinner {len(spinner_extended)} -> {extended["reduced_states"]}; all checks pass.', flush=True)

    counterexamples = {}
    for version, engine in engines.items():
        body = rng.parse_body(rng.generated_function(version, 'behavior_script', 'random_u16'))
        def word_sequence(seed, count):
            words = []
            for _ in range(count):
                seed = rng.execute_rng(body, seed)
                words.append(seed)
            return words
        seed = next(s for s in range(65536) if (lambda w: w[0] % 7 == 1 and w[1] >= 32767)(word_sequence(s, 2)))
        words = word_sequence(seed, 4)
        traces = []
        for speed in (200, -200):
            target, cursor, trace = speed, 0, []
            for _ in range(2):
                out = engine.run((0, speed, target, 1, *words[cursor:cursor+2]))
                cursor += out[0]
                speed, target = map(as_float, out[1:3])
                trace.append({'speed': speed, 'target': target, 'draws': out[0], 'seed_after': words[cursor-1] if cursor else seed})
            traces.append(trace)
        assert [r['draws'] for r in traces[0]] == [2, 2]
        assert [r['draws'] for r in traces[1]] == [2, 0]
        motion = [engine.run((0, s, 200, 1, 0, 32767)) for s in (100, 300)]
        assert cog_key(100, 200) == cog_key(300, 200) and motion[0][3] != motion[1][3]
        spinner_motion = [engine.run((1, 6, 30, d, 0, 0)) for d in (-1, 1)]
        counterexamples[version] = {
            'signed_cog_target_cannot_be_discarded': {'initial_seed': seed, 'next_four_words': words,
                'positive_200_start': traces[0], 'negative_200_start': traces[1]},
            'cog_rng_key_does_not_preserve_motion': {'shared_key': cog_key(100, 200), 'yaw_increments': [r[3] for r in motion]},
            'spinner_rng_key_does_not_preserve_motion': {'shared_key': spinner_key(6, 30, 1), 'pitch_increments': [r[4] for r in spinner_motion]},
        }
    assert counterexamples['us'] == counterexamples['jp']
    report = {
        'status': 'finite local generated-AST/native-C checks; not a Coq or whole-game reduction proof',
        'source_commit': PIN,
        'checker_files_sha256': {str(p.relative_to(PROJECT)): sha(p.read_bytes()) for p in
                                 (HERE / 'analyze.py', HERE / 'ast_exec.py', HERE.parent / 'ttc-cog-rng-sequence/analyze.py')},
        'scope': {
            'versions': ['VERSION_US', 'VERSION_JP'], 'clock_mode': 'RANDOM',
            'observation': 'ordered number of RNG words consumed at each native invocation',
            'cog_domain': 'speed -1200..1200 step 50; signed target -1200..1200 step 200; both signs of binary32 zero; direction +/-1',
            'spinner_domain': 'threshold 30,60,90,120; entry timer 1..threshold+1; direction +/-1; exactly one stable-action generic timer increment after each native invocation',
            'spinner_extended_domain': 'threshold 0,30,60,90,120; entry timer 0..threshold+1; direction -1,0,+1; same boundary contract; includes initial zero fields and timer-zero boundaries but does not derive their gameplay reachability',
            'composition_requires': ['same invocation order and enable/skip decisions', 'same initial RNG seed and external draws',
                'no intervening writes to retained native state', 'valid memory and defined angle arithmetic',
                'proof that dropped motion cannot affect collisions, Mario, activation, future object order or any other RNG caller'],
            'no_claims': ['complete startup or arbitrary action-reset coverage', 'reachable joint preparation count',
                'geometry/Mario preservation', 'full-game observational equivalence', '1200-update RANDOM witness', 'Coq capstone discharge'],
        },
        'native_cross_check': provenance, 'versions': results, 'counterexamples': counterexamples,
        'selector_coverage': 'generated raw RNG temporaries have only the checked modulo/sign uses; all 65536 single-word inputs cross-checked; all class pairs enumerated at every domain state',
        'interpretation': {
            'spinner_video_121': 'supported for this explicit recurrent local domain; already reduced in the video product',
            'cog_video_259': 'the table does not specify an equivalence proof; merging absolute target/distance fails with identical future RNG words',
            'global_preparation_count': None,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Report: {args.output}', flush=True)


if __name__ == '__main__':
    main()
