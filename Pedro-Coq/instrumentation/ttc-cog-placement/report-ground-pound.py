#!/usr/bin/env python3
"""Report observed ground-pound impacts and their complete successor updates.

This is a finite discovery check, not a Coq theorem or a normal-entry proof.
It keeps endpoint preservation separate from motion at internal boundaries.
An empty candidate list does not exclude untested positions or controller paths.
"""
import argparse
from collections import defaultdict
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("trace_check", HERE / "check-trace.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
GROUND_POUND = "008008a9"
GROUND_POUND_LAND = "0080023c"


def position(fields, prefix=""):
    return tuple(checker.f32(fields[prefix + a.upper() if prefix else a]) for a in "xyz")


def brief(fields):
    keys = ("rel", "routine", "phase", "action", "actionState", "actionTimer", "input",
            "x", "y", "z", "speed", "vy", "floorHeight", "floorOwner",
            "ceilHeight", "ceilOwner", "platform", "particles", "active",
            "lowerYaw", "lowerSpeed", "lowerTarget", "upperYaw", "upperSpeed",
            "upperTarget", "result")
    return {key: fields[key] for key in keys if key in fields}


def inspect(trial):
    manifest = json.loads((trial / "manifest.json").read_text())
    if not manifest.get("trace_ground_pound"):
        raise ValueError("requires --trace-ground-pound, including successor/particle helpers")
    consistency, trace = checker.check(trial)
    frames = defaultdict(list)
    for kind, fields in trace:
        frames[int(fields["rel"])].append((kind, fields))

    def routine(rel, name, phase=None):
        return [f for k, f in frames[rel] if k == "CPATH" and f["routine"] == name
                and (phase is None or f["phase"] == phase)]

    def complete_update(rel):
        boundaries = routine(rel, "execute_mario_action")
        return boundaries if [f["phase"] for f in boundaries] == ["enter", "exit"] else []

    gp_entries = [f for k, f in trace if k == "CPATH" and f["routine"] == "act_ground_pound"
                  and f["phase"] == "enter"]
    episodes = []
    for entry in gp_entries:
        rel = int(entry["rel"])
        if not episodes or rel != episodes[-1][-1] + 1:
            episodes.append([])
        episodes[-1].append(rel)
    episode_reports = []
    for episode in episodes:
        start = routine(episode[0], "act_ground_pound", "enter")[0]
        anchor = position(start)
        points = [f for rel in episode for k, f in frames[rel] if k == "CPATH"]
        changed = next((brief(f) for f in points if position(f) != anchor), None)
        descent = [f for rel in episode for f in routine(rel, "act_ground_pound", "enter")
                   if f["actionState"] != "0"]
        air = [f for rel in episode for k, f in frames[rel]
               if k == "CAIR" and f["action"] == GROUND_POUND]
        episode_reports.append({
            "first_frame": episode[0], "last_frame": episode[-1], "entry": brief(start),
            "startup_calls": sum(f["actionState"] == "0" for f in gp_entries
                                 if int(f["rel"]) in episode),
            "first_descent": brief(descent[0]) if descent else None,
            "first_position_change": changed,
            "last_ground_pound_return": [brief(f) for f in routine(episode[-1], "act_ground_pound", "exit")],
            "following_update": [brief(f) for f in complete_update(episode[-1] + 1)],
            "first_descent_air_calls": [f for f in air if f["rel"] == air[0]["rel"]] if air else [],
            "impact_frames": [int(f["rel"]) for f in air if f["result"] == "1"],
        })

    pool = manifest["symbols"]["gObjectPool"]
    owners = {"floorOwner": f"{pool + 29 * 0x260:08x}",
              "ceilOwner": f"{pool + 32 * 0x260:08x}"}
    impacts = []
    for kind, impact in trace:
        if kind != "CAIR" or impact["action"] != GROUND_POUND or impact["result"] != "1":
            continue
        rel = int(impact["rel"])
        first, following = complete_update(rel), complete_update(rel + 1)
        reasons = []
        if not first or not following:
            reasons.append("missing complete impact or following Mario update")
        anchor = position(first[0]) if first else position(impact, "old")
        path = [f for frame in (rel, rel + 1) for k, f in frames[frame] if k == "CPATH"]
        air = [f for frame in (rel, rel + 1) for k, f in frames[frame] if k == "CAIR"]
        geometry = [f for frame in (rel, rel + 1)
                    for f in routine(frame, "update_mario_geometry_inputs", "exit")]
        off_floor = len(geometry) == 2 and all(
            int(f["input"], 16) & 4 and checker.f32(f["floorHeight"]) + 100 < position(f)[1]
            for f in geometry)
        if not off_floor:
            reasons.append("actual position is not off-floor at both geometry refreshes")
        if impact["pedroCandidate"] != "1" or any(impact[key] != value for key, value in owners.items()):
            reasons.append("impact does not select the target cog floor and ceiling close-gap branch")
        platform_references = sorted({f["platform"] for f in path if f["platform"] != "00000000"})
        # A remembered cog pointer is not by itself current floor support.
        # Actual geometry and position checks below decide preservation.
        if any(p not in owners.values() for p in platform_references):
            reasons.append("a platform outside the two checked cogs needs separate analysis")
        snapshots = [f for frame in (rel, rel + 1, rel + 2)
                     for k, f in frames[frame] if k == "CFRAME"]
        endpoints_fixed = bool(first and following) and len(snapshots) == 3 and all(
            position(f) == anchor for f in first + following + snapshots)
        if not endpoints_fixed:
            reasons.append("position changes across complete updates or a bracketing snapshot is missing")
        internal_fixed = all(position(f) == anchor for f in path) and all(
            position(f, "old") == anchor and position(f, "new") == anchor for f in air)
        if not internal_fixed:
            reasons.append("position changes at an observed internal boundary")
        cog_fixed = True
        for label, slot in (("lower", "29"), ("upper", "32")):
            poses = {(f.get(label + "Yaw"), f.get(label + "Speed")) for f in path}
            cog_snapshots = [f for frame in (rel, rel + 1, rel + 2)
                             for k, f in frames[frame] if k == "CCOG" and f["slot"] == slot]
            fixed = len(poses) == 1 and len(cog_snapshots) == 3
            if fixed:
                yaw, speed = next(iter(poses))
                fixed = yaw is not None and speed is not None and float(speed) == 0 and all(
                    f["yaw"] == yaw and position(f) == position(cog_snapshots[0])
                    for f in cog_snapshots) and all(float(f["speed"]) == 0 for f in cog_snapshots[1:])
            if not fixed:
                cog_fixed = False
                reasons.append(label + " cog is not fixed across the impact and following update")
        land = routine(rel + 1, "act_ground_pound_land")
        mist = routine(rel, "bhv_pound_white_puffs_init", "enter")
        requests = bool(first) and bool(int(first[-1]["particles"], 16) & 0x10000)
        if not requests:
            reasons.append("complete impact update does not return a mist-circle request")
        if not land:
            reasons.append("following update does not execute ground-pound-land")
        # Mist-helper observation is reported separately. It does not prove the
        # entire allocator, object identity, or subsequent lifetime in Clight.
        impacts.append({
            "frame": rel, "air_impact": impact, "impact_update": [brief(f) for f in first],
            "following_update": [brief(f) for f in following],
            "following_land_calls": [brief(f) for f in land],
            "geometry": [brief(f) for f in geometry],
            "endpoint_position_preserved": endpoints_fixed,
            "all_observed_positions_preserved": internal_fixed, "both_cogs_fixed": cog_fixed,
            "remembered_platform_references": platform_references,
            "mist_requested": requests, "mist_initializer_calls_same_frame": len(mist),
            "ordered_rng_draws": [f for frame in (rel, rel + 1) for k, f in frames[frame] if k == "CRNG"],
            "rejected_because": reasons,
        })
    return {
        "version": manifest["version"], "clock_mode": manifest["initialization"]["mode"],
        "trace_sha256": consistency["trace_sha256"],
        "counts": consistency["counts"], "episodes": episode_reports, "impacts": impacts,
        "strict_preserving_candidates": [f["frame"] for f in impacts if not f["rejected_because"]],
        "scope": "finite observed impact plus following update; exact position and both cog poses; "
                 "no normal-entry, whole-game Clight, or indefinitely repeatable RNG proof; "
                 "STOPPED mode is a separate geometry diagnostic, not the RANDOM-mode target",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trial", type=Path)
    args = parser.parse_args()
    result = inspect(args.trial)
    (args.trial / "ground-pound-report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("version", "trace_sha256", "strict_preserving_candidates")}
                     | {"episodes": len(result["episodes"]), "impacts": len(result["impacts"])}, indent=2))


if __name__ == "__main__":
    main()
