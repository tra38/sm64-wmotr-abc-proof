#!/usr/bin/env python3
"""Check the exact acceptance checkpoint and its clean replay provenance.

This validates a finite debugger receipt, not all controller histories or
a MIPS-to-Clight simulation. A split is reported, never silently rejected.
"""
import pathlib
import re
import sys

STAGES = ("handler-entry", "nonfading-branch", "accepted-return",
          "disappeared-entry", "disappeared-return", "copy-return",
          "final-platform-return")


def fields(line):
    parts = line.strip().split(",")
    pairs = [part.split("=", 1) for part in parts[1:]]
    if any(len(pair) != 2 for pair in pairs):
        raise ValueError("malformed record")
    result = dict(pairs)
    if len(result) != len(pairs):
        raise ValueError("duplicate field")
    return parts[0], result


def validate(receipt, raw):
    records = [fields(line) for line in receipt.splitlines() if line.strip()]
    if len(records) != 8:
        raise ValueError("expected seven snapshots and one result")
    samples = []
    for (tag, sample), stage in zip(records[:7], STAGES):
        if tag != "WARP_ACCEPT_SAMPLE" or sample["stage"] != stage:
            raise ValueError("wrong phase order")
        if sample["area"] != "1" or sample["timer"] != "2807":
            raise ValueError("not the chosen Area-1 update")
        for vector in ("state", "collision", "display"):
            if not re.fullmatch(r"[0-9a-f]{8}(:[0-9a-f]{8}){2}", sample[vector]):
                raise ValueError("missing complete position vector")
        if sample["originalTopSlot"] != "803451f8":
            raise ValueError("missing original top identity")
        for cell in ("floor", "height", "owner", "platform", "liveTop",
                     "originalSlotBehavior"):
            if not re.fullmatch(r"[0-9a-f]{8}", sample[cell]):
                raise ValueError("missing support/identity cell")
        count = int(sample["liveTopCount"])
        if not 0 <= count <= 240 or (count == 0) != (sample["liveTop"] == "00000000"):
            raise ValueError("inconsistent live top census")
        samples.append(sample)
    accepted = samples[2]
    if (accepted["result"], accepted["action"], accepted["arg"],
            accepted["used"], accepted["upper"]) != (
            "1", "00001300", "00040002", "80345918", "80345918"):
        raise ValueError("not a successful upper-warp return before disappeared")
    if samples[3]["arg"] != "00040002" or samples[4]["arg"] != "00040001":
        raise ValueError("disappeared checkpoint misplaced")
    tag, result = records[-1]
    if tag != "WARP_ACCEPT_RESULT" or result != dict(
            armed="1", accepted="1", pending="0", snapshots="7",
            disappeared="1", copied="1", final="1", topIdentified="1", failures="0"):
        raise ValueError("missing or failed observation")
    if not re.search(r"^SEARCH,.*postEntryInput=controller-only,"
                     r"inputPluginMemoryWrites=zero,allowSetupA=0,searchMode=12$", raw, re.M):
        raise ValueError("missing controller-only provenance")
    if not re.search(r"^RESULT,.*mode12PillarsComplete=1,.*warpDisappeared=1,"
                     r"warpUsedObj=1,platformTop=0,.*aPressedFrames=0,"
                     r"aDownFrames=0,controllerAFrames=0$", raw, re.M):
        raise ValueError("missing zero-A route result")
    for timer, count in ((848, 1), (1065, 2), (2390, 3), (2548, 4)):
        if not re.search(rf"^TOP,timer={timer},pillars={count},", raw, re.M):
            raise ValueError("missing pillar milestone")
    for name in ("RANK5_STATE_SPLIT_RESULT", "RANK13_RESULT"):
        if not re.search(rf"^{name},.*invariant=1$", raw, re.M):
            raise ValueError("existing live identity/order audit failed")
    return samples


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: check.py receipt.txt raw.log")
    samples = validate(pathlib.Path(sys.argv[1]).read_text(),
                       pathlib.Path(sys.argv[2]).read_text(errors="replace"))
    accepted, final = samples[2], samples[-1]
    split = len({accepted[key] for key in ("state", "collision", "display")}) > 1
    print(f"PASS: accepted-return split={split}; final platform={final['platform']}; "
          f"live tops at acceptance={accepted['liveTopCount']}")
    print(f"  State:     {accepted['state']}\n"
          f"  Collision: {accepted['collision']}\n"
          f"  Display:   {accepted['display']}")


if __name__ == "__main__":
    main()
