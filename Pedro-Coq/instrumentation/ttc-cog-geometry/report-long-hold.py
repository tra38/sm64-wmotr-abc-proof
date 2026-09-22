#!/usr/bin/env python3
"""Check the 1,200-update extension of the stopped-clock diagnostic."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
PLACEMENT = HERE.parent / "ttc-cog-placement"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


checker = module("long_trace", PLACEMENT / "check-trace.py")
preservation = module("long_preservation", PLACEMENT / "check-preservation.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "results-1200.json")
    args = parser.parse_args()
    base = PROJECT / "build/cog-placement/search_edge_a_stopped"
    initialization = json.loads((base / "initialization.json").read_text())
    trials, logical = {}, {}
    for version in ("us", "jp"):
        trial = base / ("geometry_a_1200_" + version)
        consistency, trace = checker.check(trial)
        logical[version] = checker.normalized(trial, trace)
        result = preservation.inspect(trial, minimum=1200)
        manifest = json.loads((trial / "manifest.json").read_text())
        summary = json.loads((trial / "summary.json").read_text())
        if manifest["initialization"] != initialization:
            raise ValueError("initialization differs: " + version)
        frames = [f for k, f in logical[version] if k == "CFRAME"]
        timers = [int(f["timer"]) for f in frames]
        if timers != list(range(timers[0], timers[0] + len(timers))):
            raise ValueError("global timer does not increase once per input snapshot")
        inputs = [f for k, f in logical[version] if k == "CINPUT"]
        if any(f["x"] != "75" or f["y"] != "28" or any(f[b] != "0" for b in "ABZRL")
               for f in inputs):
            raise ValueError("unexpected controller input")
        old = base / ("geometry_a_replay_us" if version == "us" else "geometry_a_control_jp")
        _, old_trace = checker.check(old)
        old_logical = checker.normalized(old, old_trace)
        prefix = [(k, f) for k, f in logical[version] if int(f["rel"]) < 94]
        if prefix != [(k, f) for k, f in old_logical if int(f["rel"]) < 94]:
            raise ValueError("extension differs during the original checked 94 updates")
        snapshots = {int(f["rel"]): f for f in frames}
        trials[version] = {
            "name": trial.name, "trace_sha256": consistency["trace_sha256"],
            "artifacts_sha256": {k: v for k, v in manifest.items() if k.endswith("_sha256")},
            "counts": consistency["counts"], "logical_events": len(logical[version]),
            "matching_original_prefix_events": len(prefix),
            "global_timer_range": [timers[0], timers[-1]], "global_timer_stride": 1,
            "longest_checked_run": result["longest_checked_run"],
            "runs_of_at_least_1200": [{"first_update": run[0]["frame"],
                "last_update": run[-1]["frame"], "updates": len(run),
                "position": run[0]["position"], "lower_pose": run[0]["lower_pose"],
                "upper_poses": run[0]["upper_poses"]} for run in result["witnesses"]],
            "milestone_snapshots": {str(i): snapshots[i] for i in (0, 94, 300, 600, 900, 1200)
                                    if i in snapshots},
            "first_rejected_update": next((r for r in result["candidate_updates"]
                                           if r["rejected_because"]), None),
            "cheats_disabled": summary["cheats_disabled"], "observer_errors": summary["observer_errors"],
        }
    if logical["us"] != logical["jp"]:
        raise ValueError("US/JP logical observations differ")
    result = {
        "date": "2026-09-21", "versions": ["VERSION_US", "VERSION_JP"],
        "source_pin": initialization["source_pin"], "initialization": initialization,
        "requested_updates": 1200,
        "passed_both_versions": all(t["longest_checked_run"] >= 1200 for t in trials.values()),
        "nominal_updates_per_second": 30, "nominal_seconds_for_1200_updates": 40,
        "time_basis": "Pinned game_init.c display_and_vsync waits twice for VI and increments gGlobalTimer once; observed snapshot timer stride is one. Nominal game time, not emulator wall-clock duration or 60 Hz VI count.",
        "scope": "Finite stopped-clock hold from declared near-cog initialization, with controller-only input. Not normal entry, RANDOM-mode cog stasis, RNG control, or an indefinite/formal preservation proof.",
        "original_cutoff": "The previous --testshots cutoff at rendered frame 470 ended the emulator after snapshots 0..94; 94 was an observation limit, not a failed update.",
        "new_render_cutoff": 1576, "matching_us_jp_logical_events": len(logical["us"]),
        "checks_sha256": {name: sha(PLACEMENT / name) for name in (
            "check-trace.py", "check-preservation.py")},
        "reporter_sha256": sha(Path(__file__)), "trials": trials,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "passed_both_versions": result["passed_both_versions"],
        "matching_logical_events": result["matching_us_jp_logical_events"],
        "trials": {v: {k: t[k] for k in ("longest_checked_run", "global_timer_range", "first_rejected_update")}
                   for v, t in trials.items()}}, indent=2))


if __name__ == "__main__":
    main()
