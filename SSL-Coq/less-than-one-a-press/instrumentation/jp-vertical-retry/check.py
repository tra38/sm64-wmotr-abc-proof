"""Validate this finite conditional receipt; never infer gameplay reachability."""
import argparse
import json
import re
import struct
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def records(path):
    out = []
    for line in path.read_text().splitlines():
        tag, _, rest = line.partition(",")
        fields = dict(part.split("=", 1) for part in
                      re.split(r",(?=[A-Za-z][A-Za-z0-9_]*=)", rest) if "=" in part)
        out.append((tag, fields))
    return out


def triplet(value):
    return tuple(int(x, 16) for x in value.strip("()").split(","))


def f32(value):
    return struct.unpack(">f", struct.pack(">f", value))[0]


def from_bits(value):
    return struct.unpack(">f", struct.pack(">I", value))[0]


def to_bits(value):
    return struct.unpack(">I", struct.pack(">f", value))[0]


def signed32(value):
    return (value + 2**31) % 2**32 - 2**31


def surface(row):
    raw = bytes.fromhex(row["words"])
    require(len(raw) == 48, "incomplete surface")
    return {
        "pointer": int(row["surface"], 16),
        "type": struct.unpack_from(">h", raw)[0], "flags": raw[4],
        "vertices": [list(struct.unpack_from(">hhh", raw, i)) for i in (10, 16, 22)],
        "plane": list(struct.unpack_from(">IIII", raw, 28)),
        "owner": struct.unpack_from(">I", raw, 44)[0],
    }


def coq_data(lists):
    """Deterministic literal data, not generated game code or a proof script."""
    def tuple_text(values):
        return "(" + ", ".join(map(str, values)) + ")"
    blocks = []
    for kind in ("dynamic", "static"):
        rows = []
        for s in lists[kind]:
            rows.append(f"  ivl_row {s['pointer']} {s['type']} {s['flags']}\n"
                        + "    " + " ".join(map(tuple_text, s['vertices'])) + "\n"
                        + f"    {tuple_text(s['plane'])} {s['owner']}")
        blocks.append(f"Definition ivl_{kind} : list IVLSurface := [\n"
                      + ";\n".join(rows) + "\n].")
    return "\n\n".join(blocks) + "\n"


def select_floor(rows, y):
    """Source-order finite diagnostic. Coq separately checks binary32 results."""
    x, z = -2200, -1024
    for s in rows:
        vs = s["vertices"]
        if any(signed32((a[2]-z)*(b[0]-a[0]) - (a[0]-x)*(b[2]-a[2])) < 0
               for a, b in zip(vs, vs[1:]+vs[:1])):
            continue
        if s["type"] == 0x72:
            continue
        nx, ny, nz, oo = map(from_bits, s["plane"])
        if ny == 0:
            continue
        height = f32(-f32(f32(f32(x*nx) + f32(nz*z)) + oo) / ny)
        if f32(y - f32(height + -78.0)) < 0:
            continue
        return s["pointer"], to_bits(height), s["owner"]
    return 0, to_bits(-11000), 0


def check(path, snapshot_path=None):
    data = records(path)
    tagged = lambda tag: [row for name, row in data if name == tag]
    one = lambda tag: tagged(tag)[0] if len(tagged(tag)) == 1 else None
    require(not tagged("VERTICAL_ERROR"), "probe reported an error")
    setup = one("VERTICAL_SETUP")
    require(setup is not None, "need exactly one supplied setup")
    low = (0xc5098000, 0x44400000, 0xc4800000)
    high = (0xc5098000, 0x44f25bad, 0xc4800000)
    require(triplet(setup["marioBits"]) == triplet(setup["objectBits"]) == low,
            "low actual/collision pose mismatch")
    require(triplet(setup["graphicsBits"]) == high, "wrong raised display")
    require(setup["marioAction"] == "0c400201" and setup["objTimer"] == "131",
            "setup action/timer changed")
    depth = one("VERTICAL_SETUP_DEPTH")
    require(depth is not None and depth["bits"] == "00000000", "setup depth changed")
    top = setup["top"]
    queries = tagged("VERTICAL_QUERY")
    require(len(queries) >= 3, "query instrumentation did not run")
    require([q["kind"] for q in queries[:3]] == ["geometry", "geometry", "platform"],
            "wrong initial query order")
    require([q["caller"] for q in queries[:3]] == ["802538a0", "802538e4", "802c7f88"],
            "wrong primary/retry/platform call sites")
    require(triplet(queries[0]["xyzBits"]) == low and queries[0]["floor"] == "00000000",
            "first live floor query did not miss")
    require(triplet(queries[1]["xyzBits"]) == high and queries[1]["owner"] == top,
            "retry did not select the top at the exact display")
    require(triplet(queries[2]["xyzBits"]) == high and queries[2]["owner"] == top,
            "final capture query did not select the top")
    require(all(q["owner"] == top for q in queries[1:]), "support query lost the top")
    snapshots = {}
    for query in ("1", "2"):
        snapshots[query] = {}
        for kind in ("dynamic", "static"):
            select = lambda tag: [r for r in tagged(tag) if r["query"] == query and r["kind"] == kind]
            heads, nodes, ends = select("VERTICAL_LIST"), select("VERTICAL_NODE"), select("VERTICAL_LIST_END")
            require(len(heads) == len(ends) == 1 and ends[0]["terminated"] == "1",
                    "incomplete/cyclic floor list")
            require(int(ends[0]["count"]) == len(nodes), "list count mismatch")
            cursor = heads[0]["next"]
            for index, node in enumerate(nodes):
                require(node["node"] == cursor and int(node["index"]) == index,
                        "list order/links mismatch")
                cursor = node["next"]
            require(cursor == "00000000", "unterminated list")
            snapshots[query][kind] = [surface(n) for n in nodes]
    require(snapshots["1"] == snapshots["2"], "lists changed between initial queries")
    lists = snapshots["1"]
    require(select_floor(lists["dynamic"], 768)[0] == select_floor(lists["static"], 768)[0] == 0,
            "snapshot calculation contradicts live miss")
    dynamic, static = select_floor(lists["dynamic"], 1938), select_floor(lists["static"], 1938)
    require(dynamic == (int(queries[1]["floor"], 16), 0x44f25bad, int(top, 16)),
            "snapshot top result mismatch")
    require(static[1] == to_bits(1280) and dynamic[1] > static[1], "wrong static competitor")
    require(all(s["type"] != 18 and (s["flags"] & 2) == 0
                for s in lists["dynamic"] + lists["static"]),
            "receipt requires a camera/intangible branch not covered by its certificate")
    a1 = [r for r in tagged("TRACE_A1") if 493 <= int(r["timer"]) <= 513]
    require([int(r["timer"]) for r in a1] == list(range(493, 514)), "missing retention frames")
    require(all(r["platform"] == r["floorOwner"] == top for r in a1), "retention failed")
    require(a1[-1]["active"] == "0" and a1[-1]["freeDepth"] == "0", "no retired-top capture")
    entry, returned = one("FIRST_APPLY_ENTRY"), one("FIRST_APPLY_RETURN")
    require(entry is not None and returned is not None, "missing actual first apply")
    require(entry["platform"] == returned["platform"] == top, "wrong first-apply platform")
    require(all(r["active"] == "0" and r["behavior"] == setup["behavior"]
                and r["action"] == "2" and r["objTimer"] == "1"
                and r["freeDepth"] == "47" for r in (entry, returned)),
            "first apply did not retain the retired top payload")
    require(triplet(entry["marioBits"]) == (0, 0x45abe000, 0x43800000), "wrong upper spawn")
    require(triplet(returned["marioBits"]) == (0x43b6cbe0, 0x45abe000, 0xc48919af),
            "wrong first displacement")
    result = one("RESULT")
    require(result is not None and all(result[k] == "1" for k in
            ("boundaryInstalled", "explosionFree", "area2", "firstApplyEntry", "firstApplyReturn")),
            "incomplete continuation")
    inputs = tagged("VERTICAL_INPUTS")
    require(inputs and all(r[k] == "0" for r in inputs for k in ("pressed", "down", "controller")),
            "A observed after supplied setup")
    if snapshot_path is not None:
        snapshot_path.write_text(json.dumps(lists, indent=2) + "\n")
    proof = Path(__file__).resolve().parents[2] / "proofs/InkVerticalLiveSelection.v"
    block = proof.read_text().split("(* BEGIN CHECKED SNAPSHOT DATA *)\n", 1)[1].split(
        "(* END CHECKED SNAPSHOT DATA *)", 1)[0]
    require(block == coq_data(lists), "Coq snapshot data does not match the live ordered lists")
    print(f"PASS: live miss/retry/capture, {len(a1)} retained frames, retired top, actual JP first apply, no A")
    print(f"PASS: ordered snapshots: {len(lists['dynamic'])} dynamic and {len(lists['static'])} static floors")
    if snapshot_path is not None:
        print(f"Snapshot: {snapshot_path}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path)
    parser.add_argument("--snapshot-output", type=Path)
    args = parser.parse_args()
    check(args.trace, args.snapshot_output)
