#!/usr/bin/env python3
"""Bounded offline collision search. No emulator state or ROM is modified."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import struct
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
SOURCE = PROJECT.parent.parent / "reference-sm64-decomp"
PIN = "9921382a68bb0c865e5e45eb594d9c64db59b1af"
OUT = PROJECT / "build/cog-geometry"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(["git", "-c", f"safe.directory={SOURCE}",
                                   "-C", str(SOURCE), *args])


def function(text, name):
    match = re.search(r"(?m)^[^\n;{}]*\b" + name + r"\([^;{}]*?\)\s*\{", text)
    if not match:
        raise ValueError(name)
    depth = 1
    tokens = re.compile(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[{}]', re.S)
    for token in tokens.finditer(text, match.end()):
        if token.group() == "{":
            depth += 1
        elif token.group() == "}":
            depth -= 1
            if depth == 0:
                return text[match.start():token.end()] + "\n"
    raise ValueError("unterminated " + name)


def initializer(version, unit, name, pattern):
    text = (PROJECT / f"generated/{version}_{unit}.v").read_text()
    start = text.index("Definition v_" + name + " :=")
    block = text[start:text.index("\n|}.", start)]
    return [int(a or b) for a, b in re.findall(pattern, block)]


def checked_inputs():
    integer = r"Init_int16 \(Int.repr (?:(-?\d+)|\((-?\d+)\))\)"
    floating = r"Init_float32 \(Float32.of_bits \(Int.repr (?:(-?\d+)|\((-?\d+)\))\)\)"
    per_version = []
    for version in ("us", "jp"):
        per_version.append({
            "macro": initializer(version, "ttc_area1_macro", "ttc_seg7_macro_objs", integer),
            "hexagon": initializer(version, "ttc_cog_collision", "ttc_seg7_collision_07015584", integer),
            "triangle": initializer(version, "ttc_cog_collision", "ttc_seg7_collision_07015650", integer),
            "sine": initializer(version, "math_util", "gSineTable", floating),
        })
    if per_version[0] != per_version[1]:
        raise ValueError("US/JP geometry input mismatch")
    data = per_version[0]
    cogs = [(i // 5, data["macro"][i:i+5]) for i in range(0, len(data["macro"])-4, 5)
            if data["macro"][i] & 511 in (350, 351)]
    if len(cogs) != 8:
        raise ValueError("cog inventory")
    header = "static const s16 positions[8][3]={" + ",".join(
        "{" + ",".join(map(str, v[1:4])) + "}" for _, v in cogs) + "};\n"
    for name, values in (("slots", [i for i, _ in cogs]),
                         ("initialYaws", [v[0] & 65024 for _, v in cogs]),
                         ("isTriangle", [int((v[0] & 511) == 351) for _, v in cogs])):
        header += f"static const int {name}[8]={{" + ",".join(map(str, values)) + "};\n"
    hashes = {}
    for name in ("hexagon", "triangle", "sine"):
        raw = b"".join(struct.pack("<I", n & 0xffffffff) if name == "sine"
                       else struct.pack("<H", n & 65535) for n in data[name])
        hashes[name] = sha(raw)
        h = 2166136261
        for byte in raw:
            h = ((h ^ byte) * 16777619) & 0xffffffff
        header += f"#define EXPECT_{name.upper()} {h}u\n"
        header += f"#define COUNT_{name.upper()} {len(data[name])}\n"
    (OUT / "inputs.inc.c").write_text(header)
    return hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--angle-step", type=int, default=4096)
    parser.add_argument("--edge-segments", type=int, default=32)
    parser.add_argument("--version", choices=("us", "jp"), default="us")
    args = parser.parse_args()
    if args.angle_step < 16 or args.angle_step % 16 or 65536 % args.angle_step:
        parser.error("angle step must divide 65536 and be a multiple of 16")
    if not 1 <= args.edge_segments <= 256:
        parser.error("edge segments must be 1..256")
    OUT.mkdir(parents=True, exist_ok=True)
    source = OUT / "source"
    archive = git("archive", PIN, "include", "src", "levels/ttc", "levels/level_defines.h", "data")
    if not (OUT / "source-pin").exists():
        with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
            tree.extractall(source, filter="data")
        (OUT / "source-pin").write_text(PIN + "\n")
    if (OUT / "source-pin").read_text().strip() != PIN:
        raise ValueError("source pin mismatch")
    # Authenticate the extracted source, including every compiler header.
    with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
        for member in tree:
            if member.isfile():
                target = source / member.name
                original = tree.extractfile(member).read()
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(original)
                elif target.read_bytes() != original:
                    raise ValueError("changed pinned source: " + member.name)
    selected = {
        "src/game/mario.c": ["resolve_and_return_wall_collisions", "vec3f_find_ceil",
                              "mario_get_floor_class", "mario_get_terrain_sound_addend",
                              "mario_floor_is_slippery", "update_mario_geometry_inputs"],
        "src/game/object_helpers.c": ["obj_build_transform_from_pos_and_angle", "obj_apply_scale_to_matrix", "dist_between_objects"],
    }
    snippets, hashes = [], {}
    mario_source = (source / "src/game/mario.c").read_text()
    snippets.append(re.search(r"s8 sTerrainSounds\[7\]\[6\] = \{.*?\n\};", mario_source, re.S).group())
    for path, names in selected.items():
        text = (source / path).read_text()
        for name in names:
            body = function(text, name)
            snippets.append(body)
            hashes[name] = sha(body.encode())
    (OUT / "helpers.inc.c").write_text("\n".join(snippets))
    input_hashes = checked_inputs()
    compiler = ["gcc", "-std=gnu99", "-O2", "-DNON_MATCHING", "-DAVOID_UB", "-D_LANGUAGE_C",
                "-DVERSION_" + args.version.upper(), "-ffp-contract=off", "-fno-fast-math",
                "-fexcess-precision=standard", "-ffunction-sections", "-fdata-sections",
                "-Wno-pointer-to-int-cast", "-Wno-int-to-pointer-cast",
                "-I" + str(source / "include"), "-I" + str(source / "src"),
                "-I" + str(source), "-I" + str(OUT), str(HERE / "search.c"),
                "-Wl,--gc-sections", "-lm", "-o", str(OUT / ("search-" + args.version))]
    subprocess.run(compiler, check=True)
    stem = f"{args.version}-step{args.angle_step}-edge{args.edge_segments}"
    with (OUT / (stem + ".jsonl")).open("w") as output:
        subprocess.run([str(OUT / ("search-" + args.version)), str(args.angle_step),
                        str(args.edge_segments)], stdout=output, check=True)
    records = [json.loads(line) for line in (OUT / (stem + ".jsonl")).read_text().splitlines()]
    result = {"source_pin": PIN, "version": args.version, "angle_step": args.angle_step,
              "edge_segments": args.edge_segments, "helpers_sha256": hashes,
              "search_sha256": sha((HERE / "search.c").read_bytes()),
              "generated_input_sha256": input_hashes,
              "compiler": compiler, "records": records,
              "scope": "offline necessary-condition filter; no full action, emulator, reachability or Coq proof"}
    (OUT / (stem + ".json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"path": str(OUT / (stem + ".json")), "records": records}, indent=2))


if __name__ == "__main__":
    main()
