#!/usr/bin/env python3
"""Replay a bounded set of single-Z ground-pound timing candidates.

Only controller CSVs vary. The prepared RANDOM-mode placement ROM is unchanged.
Compressed input intervals are expanded before replacing the requested frame.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] / "build/cog-placement"
spec = importlib.util.spec_from_file_location("ground_pound_report", HERE / "report-ground-pound.py")
reporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reporter)


def expand(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        first, last, x, y, buttons = line.split(",")
        for frame in range(int(first), int(last) + 1):
            if frame in rows:
                raise ValueError("overlapping base-controller intervals")
            rows[frame] = (int(x), int(y), buttons)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="fresh search/trial prefix")
    parser.add_argument("--version", choices=("us", "jp"), default="us")
    parser.add_argument("--suite", choices=("ledge", "inner"), required=True)
    parser.add_argument("--z-frames", help="comma-separated subset of base-controller frame indices")
    args = parser.parse_args()
    if not args.name.isidentifier():
        parser.error("name must contain only identifier characters")
    setup = "ledge" if args.suite == "ledge" else "inner_rim"
    base = HERE / "inputs" / ("ledge-rim-turn-133-us.csv" if setup == "ledge"
                             else "inner-rim-recorded-inward-us.csv")
    rows = expand(base)
    starts = [int(f) for f in args.z_frames.split(",")] if args.z_frames else (
        [128, 130, 132, 134, 136, 138, 140] if setup == "ledge" else [0, 1, 2])
    if len(starts) != len(set(starts)) or not starts or any(f not in rows for f in starts):
        parser.error("Z frames must be unique and present in the base replay")
    if any("Z" in row[2] for row in rows.values()):
        raise ValueError("base replay already contains Z; cannot claim a single new press")
    out = ROOT / args.name
    out.mkdir()
    receipt = {"scope": "bounded controller timing search; not a universal exclusion",
               "version": args.version, "setup": setup, "base_inputs": base.name,
               "base_sha256": hashlib.sha256(base.read_bytes()).hexdigest(), "trials": []}
    for start in starts:
        trial_name = f"{args.name}_z{start}_{args.version}"
        inputs = out / f"{trial_name}.csv"
        inputs.write_text("".join(f"{f},{f},{x},{y},{'Z' if f == start else buttons}\n"
                                  for f, (x, y, buttons) in sorted(rows.items())))
        command = [sys.executable, str(HERE / "run.py"), args.version, trial_name,
                   "--setup", setup, "--inputs", str(inputs), "--trace-ground-pound",
                   "--video-frames", "590" if setup == "ledge" else "470"]
        with (out / f"{trial_name}.log").open("w") as log:
            subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=240, check=True)
        trial = (ROOT if setup == "ledge" else ROOT / setup) / trial_name
        result = reporter.inspect(trial)
        trace = reporter.checker.events(trial)
        pressed = [int(f["rel"]) for k, f in trace if k == "CINPUT" and f["Z"] == "1"]
        if pressed != [start]:
            raise ValueError(f"observed Z inputs differ from recipe: {pressed}")
        (trial / "ground-pound-report.json").write_text(json.dumps(result, indent=2) + "\n")
        compact = {"name": trial_name, "setup": setup, "z_frame": start,
                   "inputs_sha256": hashlib.sha256(inputs.read_bytes()).hexdigest(),
                   "trace_sha256": result["trace_sha256"], "counts": result["counts"],
                   "strict_preserving_candidates": result["strict_preserving_candidates"],
                   "episodes": [{k: e[k] for k in ("first_frame", "last_frame", "startup_calls",
                                  "entry", "first_descent", "first_position_change", "impact_frames")}
                                for e in result["episodes"]],
                   "impacts": [{k: i[k] for k in ("frame", "endpoint_position_preserved",
                                 "all_observed_positions_preserved", "both_cogs_fixed", "mist_requested",
                                 "mist_initializer_calls_same_frame", "rejected_because")}
                               for i in result["impacts"]]}
        receipt["trials"].append(compact)
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps({"trial": trial_name, "episodes": len(result["episodes"]),
                          "impact_frames": [i["frame"] for i in result["impacts"]],
                          "candidates": result["strict_preserving_candidates"]}), flush=True)


if __name__ == "__main__":
    main()
