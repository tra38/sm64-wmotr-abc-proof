#!/usr/bin/env python3
"""Check the bounded search and selected emulator continuations; save a receipt."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
PLACEMENT = HERE.parent / "ttc-cog-placement"


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, PLACEMENT / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


checker = module("geometry_trace", "check-trace.py")
preservation = module("geometry_preservation", "check-preservation.py")
ground_pound = module("geometry_ground_pound", "report-ground-pound.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "results.json")
    args = parser.parse_args()
    native = {}
    for version in ("us", "jp"):
        path = PROJECT / f"build/cog-geometry/{version}-step1024-edge32.json"
        result = json.loads(path.read_text())
        if result["search_sha256"] != sha(HERE / "search.c"):
            raise ValueError("search source changed since the saved run")
        result["raw_receipt_sha256"] = sha(path)
        # Retain compiler options without publishing machine-specific paths.
        result["compiler_options"] = [s for s in result.pop("compiler")
                                      if s.startswith("-") and not s.startswith("-I") and s != "-o"]
        native[version] = result
    for key in ("source_pin", "angle_step", "edge_segments", "helpers_sha256",
                "search_sha256", "generated_input_sha256", "records"):
        if native["us"][key] != native["jp"][key]:
            raise ValueError("native US/JP mismatch: " + key)
    counts = [r for r in native["us"]["records"] if r["kind"] == "counts"]
    totals = {key: sum(r[key] for r in counts) for key in (
        "poses", "point_samples", "off_floor_samples", "pedro_samples",
        "refresh_stable_samples", "gp_first_quarter_samples")}

    base = PROJECT / "build/cog-placement/search_edge_a_stopped"
    trials, traces = {}, {}
    names = ("geometry_a_control_us", "geometry_a_replay_us", "geometry_a_control_jp",
             "geometry_a_z4_us", "geometry_a_z4_jp")
    for name in names:
        trial = base / name
        result, trace = checker.check(trial)
        logical = checker.normalized(trial, trace)
        traces[name] = logical
        manifest = json.loads((trial / "manifest.json").read_text())
        summary = json.loads((trial / "summary.json").read_text())
        entry = {"version": manifest["version"], "trace_sha256": result["trace_sha256"],
                 "counts": result["counts"], "logical_events": len(logical),
                 "observed_z_frames": [int(f["rel"]) for k, f in trace
                                       if k == "CINPUT" and f["Z"] == "1"],
                 "artifacts_sha256": {k: v for k, v in manifest.items() if k.endswith("_sha256")},
                 "cheats_disabled": summary["cheats_disabled"],
                 "observer_errors": summary["observer_errors"]}
        if manifest["initialization"] != json.loads((base / "initialization.json").read_text()):
            raise ValueError("different initialization: " + name)
        if "z4" in name:
            report = ground_pound.inspect(trial)
            (trial / "ground-pound-report.json").write_text(json.dumps(report, indent=2) + "\n")
            if entry["observed_z_frames"] != [4]:
                raise ValueError("expected exactly one Z press at frame 4")
            entry["ground_pound"] = {k: report[k] for k in (
                "episodes", "impacts", "strict_preserving_candidates")}
            entry["descent_and_successor_particles"] = [f for k, f in logical
                if k == "CPATH" and int(f["rel"]) in (19, 20)
                and f["phase"] == "exit" and f["routine"] == "execute_mario_action"]
            entry["mist_calls_frames_19_20"] = sum(k == "CPATH" and int(f["rel"]) in (19, 20)
                and f["phase"] == "enter" and f["routine"] == "bhv_pound_white_puffs_init"
                for k, f in logical)
        else:
            report = preservation.inspect(trial)
            entry["longest_checked_run"] = report["longest_checked_run"]
            entry["runs"] = [{"first_frame": run[0]["frame"], "last_frame": run[-1]["frame"],
                              "updates": len(run), "position": run[0]["position"],
                              "lower_pose": run[0]["lower_pose"],
                              "upper_poses": run[0]["upper_poses"]} for run in report["witnesses"]]
            entry["first_air_call"] = next(f for k, f in logical if k == "CAIR")
            entry["first_selected_surfaces"] = [f for k, f in logical
                if k == "CSURFACE" and f["seq"] == "0" and f["scope"].startswith("air")]
            frames = [f for k, f in logical if k == "CFRAME"]
            entry["first_snapshot"], entry["last_snapshot"] = frames[0], frames[-1]
        trials[name] = entry

    comparisons = []
    for a, b in ((names[0], names[1]), (names[1], names[2]), (names[3], names[4])):
        if traces[a] != traces[b]:
            raise ValueError("logical trace mismatch: " + a + " / " + b)
        comparisons.append({"trials": [a, b], "matching_logical_events": len(traces[a])})
    prefix = [[(k, f) for k, f in traces[name] if int(f["rel"]) < 4]
              for name in ("geometry_a_replay_us", "geometry_a_z4_us")]
    if prefix[0] != prefix[1]:
        raise ValueError("control and ground pound differ before the Z press")

    result = {
        "date": "2026-09-21", "source_pin": native["us"]["source_pin"],
        "versions": ["VERSION_US", "VERSION_JP"],
        "scope": "Finite native discovery plus one selected full-game geometry and its two controller continuations. No Coq theorem, normal-entry reachability or RANDOM-mode RNG control.",
        "native_scope": "Static TTC terrain and eight cogs, omitting other dynamic objects. Two chosen cogs vary; six retain initial yaws. Strict fixed-XYZ family. Sampled positions and displacements, not all binary32 positions, yaw table entries, velocities or histories. Host/N64 equivalence is not proved.",
        "native_totals_per_version": totals, "native": native,
        "initialization": json.loads((base / "initialization.json").read_text()),
        "checks_sha256": {name: sha(PLACEMENT / name) for name in (
            "check-trace.py", "check-preservation.py", "report-ground-pound.py")},
        "reporter_sha256": sha(Path(__file__)), "trials": trials,
        "comparisons": comparisons,
        "control_and_z4_prefix": {"frames": [0, 3], "matching_logical_events": len(prefix[0])},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "native_totals_per_version": totals,
                      "comparisons": comparisons, "matching_prefix_events": len(prefix[0]),
                      "control_updates": trials[names[1]]["longest_checked_run"],
                      "gp_impacts": len(trials[names[3]]["ground_pound"]["impacts"]),
                      "gp_preserving_candidates": trials[names[3]]["ground_pound"]["strict_preserving_candidates"]}, indent=2))


if __name__ == "__main__":
    main()
