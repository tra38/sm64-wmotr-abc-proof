#!/usr/bin/env python3
"""Finite replay checks for input alternatives and the actual RANDOM scheduler.

This is an observation checker, outside the Coq trusted base. It neither
enumerates all controller sequences nor establishes normal-entry reachability.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
PLACEMENT = HERE.parent / "ttc-cog-placement"


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


checker = module("control_trace", PLACEMENT / "check-trace.py")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def xyz(f, prefix=""):
    return tuple(checker.f32(f[prefix + c.upper() if prefix else c]) for c in "xyz")


def fixed_anchor_prefix(trace):
    """Allow a ceiling-rejected rising quarter, but require a close-gap return
    in every complete update and unchanged XYZ at every observed boundary.
    This is deliberately distinct from the ordinary-air-only checker.
    """
    frames = defaultdict(list)
    snapshots = {}
    for k, f in trace:
        frames[int(f["rel"])].append((k, f))
        if k == "CFRAME":
            snapshots[int(f["rel"])] = f
    anchor = xyz(snapshots[0])
    accepted, failures = [], []
    for rel in range(max(snapshots)):
        events = frames[rel]
        path = [f for k, f in events if k == "CPATH"]
        air = [f for k, f in events if k == "CAIR"]
        actions = [f for f in path if f["routine"] == "execute_mario_action"]
        geometry = [f for f in path if f["routine"] == "update_mario_geometry_inputs"
                    and f["phase"] == "exit"]
        reasons = []
        if len(actions) != 2 or [f["phase"] for f in actions] != ["enter", "exit"]:
            reasons.append("missing complete Mario update")
        else:
            start, end = (events.index(("CPATH", f)) for f in actions)
            if any(not start < i < end for i, (k, _) in enumerate(events) if k == "CAIR"):
                reasons.append("air call outside the complete Mario update")
        if len(geometry) != 1 or any(not int(f["input"], 16) & 4
                or checker.f32(f["floorHeight"]) + 100 >= anchor[1] for f in geometry):
            reasons.append("missing off-floor geometry refresh")
        if any(xyz(snapshots[r]) != anchor for r in (rel, rel + 1)):
            reasons.append("position changes between snapshots")
        if any(xyz(f) != anchor for f in path) or any(
                xyz(f, "old") != anchor or xyz(f, "new") != anchor for f in air):
            reasons.append("position changes at an internal observed boundary")
        if any(f["platform"] != -1 for f in path):
            reasons.append("platform reference is non-null")
        close = [f for f in air if f["pedroCandidate"] == "1"]
        if not close or any(f["floorOwner"] != 29 or f["ceilOwner"] != 32
                or checker.f32(f["oldFloorHeight"]) + 100 >= anchor[1]
                or (checker.f32(f["qx"]), checker.f32(f["qz"])) == (anchor[0], anchor[2])
                for f in close):
            reasons.append("missing off-floor close-gap return between the selected cogs")
        for slot, label in ((29, "lower"), (32, "upper")):
            cog = [f for k, f in events + frames[rel + 1] if k == "CCOG" and int(f["slot"]) == slot]
            if len(cog) != 2 or any(xyz(f) != xyz(cog[0]) or f["yaw"] != cog[0]["yaw"]
                    or float(f["speed"]) != 0 for f in cog):
                reasons.append(label + " cog changes between snapshots")
            if not cog or any(f.get(label + "Yaw") != cog[0]["yaw"]
                    or float(f.get(label + "Speed", "nan")) != 0 for f in path):
                reasons.append(label + " cog changes at a path boundary")
        if any(int(snapshots[r]["timeStop"], 16) != 0 for r in (rel, rel + 1)):
            reasons.append("global Time Stop is enabled")
        if reasons:
            failures.append({"update": rel, "reasons": reasons})
            break
        accepted.append(rel)
    return {"complete_preserving_prefix": len(accepted), "position": anchor,
            "first_failure": failures[0] if failures else None,
            "bracketed_updates": max(snapshots)}


def check_cog_updates(trace):
    """Check each observed stock update and its exact ordered RNG boundary.
    Arithmetic here validates logs; it is not a new formal semantics theorem.
    """
    expected_seed, next_rng, sequence = None, 0, 0
    pending, draws, updates = None, [], []
    for kind, f in trace:
        if kind == "CFRAME":
            expected_seed = int(f["seed"])
        elif kind == "CRNG":
            if int(f["seq"]) != next_rng or int(f["before"]) != expected_seed:
                raise ValueError("RNG boundary mismatch")
            next_rng += 1
            expected_seed = int(f["after"])
            if pending:
                if f["object"] != pending["object"] or f["rel"] != pending["rel"]:
                    raise ValueError("foreign RNG call inside cog update")
                draws.append(int(f["result"]))
        elif kind == "CGSTEP":
            if int(f["seq"]) != sequence or int(f["rngNext"]) != next_rng \
                    or int(f["seed"]) != expected_seed:
                raise ValueError("cog observation index/seed mismatch")
            sequence += 1
            if f["phase"] == "enter":
                if pending:
                    raise ValueError("nested cog update")
                pending, draws = f, []
                continue
            if f["phase"] != "exit" or pending is None or any(f[k] != pending[k]
                    for k in ("object", "slot", "mode", "dir", "rel", "timer")):
                raise ValueError("unbalanced cog update")
            speed, target = (checker.f32(pending[k]) for k in ("speed", "target"))
            if not all(math.isfinite(n) for n in (speed, target, checker.f32(f["dir"]))):
                raise ValueError("non-finite cog state")
            mode = int(f["mode"])
            reaches = False
            if mode == 2:
                delta = -50 if speed > target else 50
                speed = checker.f32(speed + delta)
                reaches = checker.f32(checker.f32(speed - target) * delta) >= 0
                if reaches:
                    speed = target
                    if len(draws) != 2:
                        raise ValueError("RANDOM cog did not take its two target draws")
                    target = checker.f32(200 * (draws[0] % 7) * (1 if draws[1] >= 32767 else -1))
            elif mode in (0, 1):
                speed = (200, 400)[mode]
            elif mode != 3:
                raise ValueError("unknown clock mode")
            if not reaches and draws:
                raise ValueError("unexpected cog RNG draw")
            yaw = (int(pending["yaw"]) + int(checker.f32(speed * checker.f32(f["dir"])))) & 0xffffffff
            if yaw >= 0x80000000:
                yaw -= 0x100000000
            if speed != checker.f32(f["speed"]) or target != checker.f32(f["target"]) or yaw != int(f["yaw"]):
                raise ValueError("stock cog update differs from observations")
            updates.append({"frame": int(f["rel"]), "slot": int(f["slot"]),
                "mode": mode, "yaw_before": int(pending["yaw"]), "yaw_after": yaw,
                "speed_before": checker.f32(pending["speed"]), "speed_after": speed,
                "target_before": checker.f32(pending["target"]), "target_after": target,
                "rng_first": int(pending["rngNext"]), "rng_end": next_rng, "draws": draws,
                "seed_before": int(pending["seed"]), "seed_after": expected_seed})
            pending, draws = None, []
    if pending:
        raise ValueError("unfinished cog update")
    return updates


def scheduler_receipt(trace, updates):
    if not updates:
        return None
    frames = defaultdict(list)
    by_frame = defaultdict(list)
    for k, f in trace:
        frames[int(f["rel"])].append((k, f))
    for u in updates:
        by_frame[u["frame"]].append(u)
    gaps = Counter()
    windows, run = [], []
    for rel, group in sorted(by_frame.items()):
        if [u["slot"] for u in group] != [29, 30, 31, 32, 33, 34, 35, 94]:
            raise ValueError("unexpected cog update order or missing update")
        events = frames[rel]
        mario = [i for i, (k, f) in enumerate(events) if k == "CPATH"
                 and f["routine"] == "execute_mario_action" and f["phase"] == "enter"]
        if len(mario) != 1 or any(i >= mario[0] for i, (k, _) in enumerate(events) if k == "CGSTEP"):
            raise ValueError("cog update is not before this frame's Mario action")
        for u in group:
            snapshots = [f for k, f in events if k == "CCOG" and int(f["slot"]) == u["slot"]]
            following = [f for k, f in frames[rel + 1] if k == "CCOG" and int(f["slot"]) == u["slot"]]
            if len(snapshots) != 1:
                raise ValueError("missing incoming cog snapshot")
            for f, side in [(snapshots[0], "before")] + [(f, "after") for f in following]:
                if any(float(f[key]) != u[key + "_" + side] for key in ("yaw", "speed", "target")):
                    raise ValueError("cog update disagrees with bracketing snapshot")
        lower, upper = group[0], group[3]
        gap = upper["rng_first"] - lower["rng_end"]
        if gap != sum(u["rng_end"] - u["rng_first"] for u in group[1:3]):
            raise ValueError("unaccounted RNG between the relevant cog updates")
        gaps[gap] += 1
        if all(u["yaw_before"] == u["yaw_after"] and u["speed_after"] == 0 for u in (lower, upper)):
            if run and run[-1] + 1 != rel:
                windows.append(run)
                run = []
            run.append(rel)
        elif run:
            windows.append(run)
            run = []
    if run:
        windows.append(run)
    return {"checked_frames": len(by_frame), "slot_order": [29, 30, 31, 32, 33, 34, 35, 94],
        "all_cog_updates_precede_mario": True,
        "rng_calls_between_lower_exit_and_upper_entry": dict(sorted(gaps.items())),
        "between_pair_consumers": "Only slots 30 and 31 in these observations; this is not a universal schedule.",
        "longest_stationary_cog_window_without_mario_preservation_requirement": max(map(len, windows), default=0)}


def inspect(trial, baseline):
    consistency, raw = checker.check(trial)
    trace = checker.normalized(trial, raw)
    manifest = json.loads((trial / "manifest.json").read_text())
    anchor = fixed_anchor_prefix(trace)
    updates = check_cog_updates(trace)
    if manifest.get("trace_cogs") and not updates:
        raise ValueError("requested cog observations absent")
    limit = anchor["complete_preserving_prefix"]
    # Raw identities matter within one run even though they are omitted by
    # the cross-version normalizer. Do not certify a changed retained floor.
    first_snapshot = next(f for k, f in raw if k == "CFRAME")
    for k, f in raw:
        if int(f["rel"]) >= limit and not (k == "CFRAME" and int(f["rel"]) == limit):
            continue
        if not limit:
            break
        if k in ("CFRAME", "CPATH") and (f["floor"] != first_snapshot["floor"]
                or checker.f32(f["floorHeight"]) != checker.f32(first_snapshot["floorHeight"])):
            raise ValueError("retained floor changes inside the proposed preserving prefix")
        if k == "CAIR" and (f["oldFloor"] != first_snapshot["floor"]
                or f["newFloor"] != first_snapshot["floor"]
                or checker.f32(f["oldFloorHeight"]) != checker.f32(first_snapshot["floorHeight"])):
            raise ValueError("air call changes the retained floor in the preserving prefix")
    own_rng = [f for k, f in trace if k == "CRNG" and int(f["rel"]) < limit]
    base_rng = [f for k, f in baseline if k == "CRNG" and int(f["rel"]) < limit]
    particles = [f for k, f in trace if k == "CPATH" and f["routine"] == "execute_mario_action"
                 and f["phase"] == "exit" and int(f["particles"], 16)]
    snapshots = [f for k, f in trace if k == "CFRAME"]
    deviations = [(k, f) for k, f in trace if
        (k == "CPATH" and xyz(f) != xyz(snapshots[0])) or
        (k == "CAIR" and (xyz(f, "old") != xyz(snapshots[0]) or xyz(f, "new") != xyz(snapshots[0])))]
    result = {"trial": trial.name, "version": manifest["version"], "initialization": manifest["initialization"],
        "trace_sha256": consistency["trace_sha256"],
        "artifacts_sha256": {k: v for k, v in manifest.items() if k.endswith("_sha256")},
        "counts": consistency["counts"], **anchor,
        "retained_floor_preserved_in_prefix": True if limit else None,
        "preserving_prefix_rng_calls": len(own_rng),
        "preserving_prefix_ordered_rng_equals_control": own_rng == base_rng if limit else None,
        "particles_in_preserving_prefix": [f for f in particles if int(f["rel"]) < limit],
        "first_particle_request": particles[0] if particles else None,
        "first_position_deviation": deviations[0] if deviations else None,
        "last_snapshot": snapshots[-1],
        "checked_cog_updates": len(updates),
        "scheduler": scheduler_receipt(trace, updates),
        "cog_updates_first_two_frames": [u for u in updates if u["frame"] < 2],
        "first_cog_motion": next((u for u in updates if u["slot"] in (29, 32)
                                  and u["yaw_before"] != u["yaw_after"]), None),
        "air_result_counts": dict(Counter(f["result"] for k, f in trace if k == "CAIR")),
    }
    return result, trace


def negative_controls(trace):
    """Corrupt copies of host log records, never game state, and require the
    new checks to reject them. These exercise failures beyond a happy replay.
    """
    passed = []
    exit_index = next(i for i, (k, f) in enumerate(trace)
                      if k == "CGSTEP" and f["phase"] == "exit")
    for field in ("yaw", "seed", "rngNext"):
        altered = list(trace)
        k, f = trace[exit_index]
        altered[exit_index] = k, dict(f, **{field: str(int(f[field]) + 1)})
        try:
            check_cog_updates(altered)
        except ValueError:
            passed.append("reject wrong cog " + field)
        else:
            raise ValueError("negative control accepted wrong cog " + field)
    cog_index = next(i for i, (k, _) in enumerate(trace) if k == "CGSTEP")
    try:
        check_cog_updates(trace[:cog_index] + trace[cog_index + 1:])
    except ValueError:
        passed.append("reject missing cog entry")
    else:
        raise ValueError("negative control accepted a missing entry")
    snapshot_index = next(i for i, (k, f) in enumerate(trace) if k == "CFRAME" and f["rel"] == "1")
    altered = list(trace)
    k, f = trace[snapshot_index]
    altered[snapshot_index] = k, dict(f, x=str(float(f["x"]) + 1))
    if fixed_anchor_prefix(altered)["complete_preserving_prefix"] != 0:
        raise ValueError("negative control accepted a moved endpoint")
    passed.append("reject moved following snapshot")
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "results-random-control.json")
    parser.add_argument("--trial", action="append", help="relative build/cog-placement trial path")
    args = parser.parse_args()
    base = PROJECT / "build/cog-placement"
    baseline = base / "search_edge_a_stopped/geometry_a_1200_us"
    _, raw = checker.check(baseline)
    baseline_trace = checker.normalized(baseline, raw)
    names = args.trial or ["search_edge_a_stopped/" + name for name in (
        "geometry_a_tickcontrol_us", "geometry_a_analog1200_us", "geometry_a_b4_us",
        "geometry_a_b4a5_us", "geometry_a_b4a5_jp", "geometry_a_r4_us")] + [
            "search_edge_a/geometry_a_random_us", "search_edge_a/geometry_a_random_jp"]
    results, traces = [], {}
    for name in names:
        result, trace = inspect(base / name, baseline_trace)
        if result["trial"] == "geometry_a_tickcontrol_us":
            _, old = checker.check(base / "search_edge_a_stopped/geometry_a_replay_us")
            old = checker.normalized(base / "search_edge_a_stopped/geometry_a_replay_us", old)
            stripped = [(k, f) for k, f in trace if k != "CGSTEP"]
            if stripped != old:
                raise ValueError("adding cog observation changed the original control")
            result["unchanged_control_events"] = len(old)
        results.append(result)
        traces[result["trial"]] = trace
    comparisons = {}
    for name in ("geometry_a_b4a5", "geometry_a_random"):
        if name + "_us" in traces and name + "_jp" in traces:
            if traces[name + "_us"] != traces[name + "_jp"]:
                raise ValueError("US/JP observations disagree: " + name)
            comparisons[name] = len(traces[name + "_us"])
    controls = negative_controls(traces["geometry_a_tickcontrol_us"]) \
        if "geometry_a_tickcontrol_us" in traces else []
    output = {"date": "2026-09-21", "scope": "Finite controller replays from declared near-cog initialization; not an exhaustive strategy search, stock-entry witness, formal preservation proof, or 1,200-update RANDOM-mode solution.",
        "reporter_sha256": sha(Path(__file__)),
        "checker_sha256": sha(PLACEMENT / "check-trace.py"),
        "matching_us_jp_events": comparisons, "negative_controls": controls, "trials": results}
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "trials": [{k: r[k] for k in (
        "trial", "complete_preserving_prefix", "preserving_prefix_rng_calls",
        "preserving_prefix_ordered_rng_equals_control", "first_failure", "checked_cog_updates")}
        for r in results]}, indent=2))


if __name__ == "__main__":
    main()
