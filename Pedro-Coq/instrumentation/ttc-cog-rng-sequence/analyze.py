#!/usr/bin/env python3
"""Finite RNG-sequence diagnostics, not a TTC scheduler or reachability proof.

Interpret the small integer-only generated Clight random_u16 body for every
16-bit input, cross-check against the unchanged pinned C function, and inspect
prescribed draw schedules. No ROM, emulator, or game state is modified.
"""
import argparse
from collections import Counter
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
SOURCE = PROJECT.parent.parent / "reference-sm64-decomp"
PIN = "9921382a68bb0c865e5e45eb594d9c64db59b1af"
OUT = PROJECT / "build/cog-rng-sequence"
N = 65536


def sha(data):
    return hashlib.sha256(data).hexdigest()


def generated_function(version, unit, name):
    text = (PROJECT / f"generated/{version}_{unit}.v").read_text()
    start = text.index(f"Definition f_{name} :=")
    return text[start:text.index("\n|}.", start) + 4]


def parse_body(function):
    text = function.split("  fn_body :=\n", 1)[1].rsplit("\n|}.", 1)[0]
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    cursor = 0

    def take():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token != "(":
            assert token != ")"
            return token
        value = []
        while tokens[cursor] != ")":
            value.append(take())
        cursor += 1
        return value

    body = take()
    assert cursor == len(tokens)
    return body


def execute_rng(body, initial):
    """Fail-closed evaluator for the scalar AST subset present in random_u16.

    Every integer operation here stays in signed-32 range; narrowing stores
    and explicit casts are unsigned-16. This host evaluator is not a Coq proof.
    """
    seed = initial
    temps = {}
    returned = None

    def expression(node):
        kind, *args = node
        if kind == "Econst_int":
            assert args[1] == "tint" and args[0][0] == "Int.repr"
            return int(args[0][1])
        if kind == "Evar":
            assert args == ["_gRandomSeed16", "tushort"]
            return seed
        if kind == "Etempvar":
            assert args[1] == "tushort"
            return temps[args[0]]
        if kind == "Ecast":
            assert args[1] == "tushort"
            return expression(args[0]) & 65535
        assert kind == "Ebinop", kind
        op, left, right, typ = args
        assert typ == "tint"
        a, b = expression(left), expression(right)
        if op == "Oadd":
            value = a + b
        elif op == "Oand":
            value = a & b
        elif op == "Oxor":
            value = a ^ b
        elif op in ("Oshl", "Oshr"):
            assert 0 <= b < 32 and a >= 0
            value = a << b if op == "Oshl" else a >> b
        elif op == "Oeq":
            value = int(a == b)
        else:
            raise ValueError(op)
        assert -(1 << 31) <= value < (1 << 31)
        return value

    def statement(node):
        nonlocal seed, returned
        if node == "Sskip":
            return
        assert returned is None
        kind, *args = node
        if kind == "Ssequence":
            statement(args[0])
            statement(args[1])
        elif kind == "Sset":
            value = expression(args[1])
            assert 0 <= value < N
            temps[args[0]] = value
        elif kind == "Sassign":
            assert args[0] == ["Evar", "_gRandomSeed16", "tushort"]
            seed = expression(args[1]) & 65535
        elif kind == "Sifthenelse":
            statement(args[1] if expression(args[0]) else args[2])
        elif kind == "Sreturn":
            assert args[0][0] == "Some"
            returned = expression(args[0][1])
        else:
            raise ValueError(kind)

    statement(body)
    assert returned == seed and 0 <= seed < N
    return seed


def pinned_c_function():
    git = ["git", "-c", f"safe.directory={SOURCE}", "-C", str(SOURCE)]
    source = subprocess.check_output(git + ["show", f"{PIN}:src/engine/behavior_script.c"])
    text = source.decode()
    start = text.index("u16 random_u16(void) {")
    depth = 1
    i = text.index("{", start) + 1
    while depth:
        depth += (text[i] == "{") - (text[i] == "}")
        i += 1
    return text[start:i], sha(source)


def native_table(cc):
    function, source_hash = pinned_c_function()
    # Only this test driver and type aliases are supplied by the harness.
    harness = "#include <stdint.h>\n#include <stdio.h>\ntypedef uint16_t u16;\nstatic u16 gRandomSeed16;\n"
    harness += function + "\nint main(void) {\n"
    harness += "for (uint32_t i=0; i<65536; ++i) { gRandomSeed16=(u16)i; u16 r=random_u16(); putchar(r >> 8); putchar(r & 255); }\nreturn ferror(stdout) ? 1 : 0;\n}\n"
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "stock-rng.c"
    path.write_text(harness)
    executable = OUT / "stock-rng"
    subprocess.run([cc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", str(path), "-o", str(executable)], check=True)
    data = subprocess.check_output([str(executable)])
    assert len(data) == 2 * N
    return list(struct.unpack(">65536H", data)), {
        "source_file_sha256": source_hash,
        "extracted_function_sha256": sha(function.encode()),
        "compiler": subprocess.check_output([cc, "--version"], text=True).splitlines()[0],
    }


def orbit(table, start):
    seen, path = {}, []
    value = start
    while value not in seen:
        seen[value] = len(path)
        path.append(value)
        value = table[value]
    split = seen[value]
    return path[:split], path[split:]


def graph_cycles(table):
    done, cycles = set(), []
    for start in range(N):
        seen, path = {}, []
        value = start
        while value not in done and value not in seen:
            seen[value] = len(path)
            path.append(value)
            value = table[value]
        if value in seen:
            cycle = path[seen[value]:]
            cycles.append({"length": len(cycle), "minimum_seed": min(cycle)})
        done.update(path)
    return sorted(cycles, key=lambda c: (-c["length"], c["minimum_seed"]))


def longest_good_run(table, transition, starts):
    # A seed is measured immediately BEFORE its magnitude draw.
    length = [0 if table[s] % 7 else -1 for s in range(N)]
    infinite = N + 1
    for start in starts:
        seen, path = {}, []
        value = start
        while length[value] == -1 and value not in seen:
            seen[value] = len(path)
            path.append(value)
            value = transition[value]
        count = infinite if value in seen else length[value]
        for previous in reversed(path):
            count = min(infinite, count + 1)
            length[previous] = count
    maximum = max(length[s] for s in starts)
    witness = min(s for s in starts if length[s] == maximum)
    result = {"max_good_selections": None if maximum == infinite else maximum,
              "has_infinite_run": maximum == infinite, "witness_seed_before_draw": witness}
    if maximum != infinite:
        values, current = [], witness
        for _ in range(maximum + 1):
            values.append(table[current])
            current = transition[current]
        result["witness_magnitude_draws_then_failure"] = values
        assert all(x % 7 == 0 for x in values[:-1]) and values[-1] % 7 != 0
    return result


def prescribed_draw_indices(table, indices):
    """Exact seed filtering for EXTERNALLY FIXED one-based global draw indices.

    This routine does not establish that a schedule is generated by TTC.
    A schedule observed at one seed cannot be assumed valid at another seed.
    """
    if not indices or any(type(x) is not int or x <= 0 for x in indices):
        raise ValueError("draw indices must be a nonempty list of positive integers")
    if any(b <= a for a, b in zip(indices, indices[1:])):
        raise ValueError("draw indices must be strictly increasing")
    powers = [table]
    for _ in range(1, indices[-1].bit_length()):
        prior = powers[-1]
        powers.append([prior[prior[s]] for s in range(N)])
    candidates = [(s, s) for s in range(N)]
    prior_index = 0
    for selection, index in enumerate(indices, 1):
        delta = index - prior_index
        updated = []
        for start, value in candidates:
            for bit, power in enumerate(powers):
                if delta & (1 << bit):
                    value = power[value]
            if value % 7 == 0:
                updated.append((start, value))
        candidates = updated
        prior_index = index
        if not candidates:
            return {"checked_selections": selection, "requested_selections": len(indices), "surviving_initial_seeds": []}
    return {"checked_selections": len(indices), "requested_selections": len(indices),
            "surviving_initial_seeds": [s for s, _ in candidates]}


def unconstrained_interference_example(table):
    # A deliberately relaxed arithmetic schedule: assign every rejected value
    # to an unspecified other consumer. TTC is NOT proved able to realize it.
    seed, index, indices = 0, 0, []
    for _ in range(1200):
        seed, index = table[seed], index + 1
        while seed % 7:
            seed, index = table[seed], index + 1
        indices.append(index)
        seed, index = table[seed], index + 1  # the cog's mandatory sign draw
    check = prescribed_draw_indices(table, indices)
    assert 0 in check["surviving_initial_seeds"]
    gaps = [b-a for a, b in zip(indices, indices[1:])]
    return {"scope": "Arithmetic example with freely assigned intervening consumers; not a TTC or controller witness",
            "initial_seed": 0, "successful_target_selections": len(indices),
            "first_magnitude_draw_index": indices[0],
            "total_draws_through_final_sign": index,
            "minimum_magnitude_spacing": min(gaps), "maximum_magnitude_spacing": max(gaps),
            "magnitude_draw_indices": indices, "fixed_schedule_check": check}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc", default="gcc")
    parser.add_argument("--draw-indices", type=Path, help="Optional JSON list of fixed global draw indices; not a derived TTC schedule")
    parser.add_argument("--output", type=Path, default=HERE / "results.json")
    args = parser.parse_args()
    functions, hashes = {}, {}
    for unit, name in [("behavior_script", "random_u16"), ("behavior_script", "random_sign"), ("obj_behaviors_2", "bhv_ttc_cog_update")]:
        us = generated_function("us", unit, name)
        jp = generated_function("jp", unit, name)
        # The object unit's anonymous union identifiers vary by version.
        normalize = lambda text: re.sub(r"\b__\d+\b", "__anonymous", text)
        assert normalize(us) == normalize(jp), name
        functions[name] = us
        hashes[name] = {"us_sha256": sha(us.encode()), "jp_sha256": sha(jp.encode()),
                        "normalized_us_jp_equal": True}
    body = parse_body(functions["random_u16"])
    table = [execute_rng(body, s) for s in range(N)]
    native, native_evidence = native_table(args.cc)
    assert native == table, "generated scalar interpretation differs from stock C"
    tail, cycle = orbit(table, 0)
    assert not tail
    strides, advance = [], list(range(N))
    for stride in range(1, 65):
        advance = [table[x] for x in advance]
        strides.append({"global_draw_stride": stride,
                        "all_16bit_inputs": longest_good_run(table, advance, range(N)),
                        "seed_zero_cycle": longest_good_run(table, advance, cycle)})
    # Independent bounded filtering checks the longest-run DP's exclusions.
    filters = {}
    for stride in range(1, 65):
        result = prescribed_draw_indices(table, [1 + stride*i for i in range(1200)])
        expected = strides[stride-1]["all_16bit_inputs"]
        assert not expected["has_infinite_run"]
        assert result["checked_selections"] == expected["max_good_selections"] + 1
        filters[str(stride)] = result
    with localcontext() as ctx:
        ctx.prec = 40
        heuristic = Decimal(7) ** -1200
        expected = Decimal(10) ** 155 * heuristic
    result = {
        "scope": "Finite generated-scalar/C cross-check and prescribed RNG schedules; not a full TTC scheduler, normal-entry result, or Coq theorem",
        "versions": ["VERSION_US", "VERSION_JP"], "source_pin": PIN,
        "analyzer_sha256": sha(Path(__file__).read_bytes()),
        "generated_functions": hashes, "native_cross_check": native_evidence,
        "all_input_results_agree": N,
        "transition_table_be_u16_sha256": sha(struct.pack(">65536H", *table)),
        "all_functional_graph_cycles": graph_cycles(table),
        "seed_zero_cycle": {"length": len(cycle), "good_magnitude_values": sum(x % 7 == 0 for x in cycle),
                            "mod7_counts": dict(sorted(Counter(x % 7 for x in cycle).items()))},
        "all_input_good_first_draws": sum(x % 7 == 0 for x in table),
        "fixed_strides": strides, "fixed_schedule_1200_filters": filters,
        "unconstrained_interference_example": unconstrained_interference_example(table),
        "video_independent_uniform_heuristic_only": {"seven_to_minus_1200": str(heuristic),
            "ten_to_155_times_that": str(expected),
            "qualification": "These numbers follow the video's probability model, not the deterministic game's exact probability or an impossibility proof"},
    }
    if args.draw_indices:
        result["user_prescribed_schedule"] = prescribed_draw_indices(table, json.loads(args.draw_indices.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "all_input_results_agree": N,
        "cycles": result["all_functional_graph_cycles"],
        "raw_stride_1": strides[0], "isolated_cog_stride_2": strides[1],
        "largest_run_strides_2_through_64": max(x["all_16bit_inputs"]["max_good_selections"] for x in strides[1:]),
        "heuristic": result["video_independent_uniform_heuristic_only"]}, indent=2))


if __name__ == "__main__":
    main()
