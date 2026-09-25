"""Controller-only positive/negative controls for the late landing window.

The A control deliberately presses A once; it is never a no-A witness.
Every branch starts at a state reached by the already checked JP input prefix.
No pose, action, timer, depth, actor, surface, or RNG field is written.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "instrumentation/wafel-jp-pilot"))
from replay import create_game, load_capture, Observer, set_input

def sample(g):
    floor = g.read("gMarioState.floor")
    return dict(action=g.read("gMarioState.action"),
                timer=g.read("gMarioState.actionTimer"),
                depth=g.read("gMarioState.quicksandDepth"),
                pos=g.read("gMarioState.pos"),
                floorType=None if floor.is_null() else g.read("gMarioState.floor.type"))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("capture", type=Path)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    rows = load_capture(args.capture)
    header = (ROOT / "build/pinned-sm64/include/sm64.h").read_text()
    names = ("JUMP", "FREEFALL", "SIDE_FLIP", "HOLD_JUMP", "HOLD_FREEFALL",
             "LONG_JUMP", "DOUBLE_JUMP", "TRIPLE_JUMP", "BACKFLIP")
    landing_actions = {int(re.search(r"^#define ACT_" + name + r"_LAND\s+(0x[0-9A-Fa-f]+)",
                       header, re.M).group(1), 16) for name in names}
    assert all(not r["buttons"] & 0x8000 for r in rows)
    g, cases = create_game(), []
    observer = Observer(g)
    last = -1000
    checked = 0
    for row in rows:
        seen = observer.snapshot()
        if "positions" in row:
            checked += 1
            assert seen["timer"] == row["timer"] + 1
            assert all(seen.get(k) == v for k, v in row.items()
                       if k not in ("poll", "timer", "buttons", "stick"))
            state = sample(g)
            # ACT_WALKING, ordinary speed, no already prepared long-jump state.
            if (state["action"] == 0x04000440 and
                g.read("gMarioState.forwardVel") > 10 and
                row["poll"] - last >= 90 and len(cases) < 12):
                last = row["poll"]
                saved = g.save_state()
                trials = []
                for with_a in (False, True):
                    g.load_state(saved)
                    records, samples = [], []
                    for i in range(90):
                        # Enter crouch slide first: walking checks A before Z.
                        buttons = 0x2000 | (0x8000 if with_a and i == 1 else 0)
                        command = dict(poll=row["poll"] + i, buttons=buttons,
                                       stick=list(row["stick"]) if i < 2 else [0, 0])
                        records.append(command)
                        set_input(g, command)
                        g.advance()
                        samples.append(sample(g))
                    text = "".join("%d %d %d %d\n" % (r["poll"], r["buttons"], *r["stick"])
                                   for r in rows[:row["poll"]-1] + records)
                    target = args.output.parent / ("poll-%d-%s.inputs" %
                              (row["poll"], "one-a" if with_a else "no-a"))
                    target.write_bytes(text.encode("ascii"))
                    late = [dict(update=i+1, **s) for i, s in enumerate(samples)
                            if s["action"] == 1145 and s["timer"] in (4, 5)]
                    negative = [dict(update=i+1, **s) for i, s in enumerate(samples)
                                if s["depth"] < 0]
                    any_late = [dict(update=i+1, **s) for i, s in enumerate(samples)
                                if s["action"] in landing_actions and s["timer"] >= 4]
                    trials.append(dict(aPresses=int(with_a), lateLongJumpSamples=late,
                                       anyLateCommonLandingSamples=any_late,
                                       negativeDepthSamples=negative,
                                       actions=sorted({s["action"] for s in samples}),
                                       inputFile=target.name,
                                       inputSha256=hashlib.sha256(text.encode("ascii")).hexdigest()))
                g.load_state(saved)
                cases.append(dict(firstPoll=row["poll"], initial=state, trials=trials))
        set_input(g, row)
        g.advance()
    report = dict(scope="Finite Wafel JP controller controls, after-update samples; not a proof or an exact write observer.",
                  captureSha256=hashlib.sha256(args.capture.read_bytes()).hexdigest(),
                  baselineSnapshotsChecked=checked, branchUpdates=90, cases=cases)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(dict(cases=len(cases), baselineSnapshotsChecked=checked,
                         lateNoA=sum(bool(t["anyLateCommonLandingSamples"]) for c in cases for t in c["trials"] if not t["aPresses"]),
                         lateOneA=sum(bool(t["lateLongJumpSamples"]) for c in cases for t in c["trials"] if t["aPresses"]),
                         negativeNoA=sum(bool(t["negativeDepthSamples"]) for c in cases for t in c["trials"] if not t["aPresses"]),
                         negativeOneA=sum(bool(t["negativeDepthSamples"]) for c in cases for t in c["trials"] if t["aPresses"]))))
if __name__ == "__main__":
    main()
