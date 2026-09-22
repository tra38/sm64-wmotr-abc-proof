# Bounded native geometry discovery

This offline tool constructs hypothetical terrain-and-cog states and calls
unchanged pinned SM64 collision routines. It does not edit a ROM, emulator
state, or the generated Clight files. Its finite results are **not a proof**.
See [the detailed report](../../docs/notes/ttc-cog-geometry-search.md) for the
exact sample family, omitted dynamic objects, and host/N64 limitations.

The recorded run tests 64 orientations for each cog in four selected pairs,
33 parameters per lower-cog top edge, eleven signed edge offsets and five
inward displacements. It deduplicates binary32 X/Z within each pair-pose,
retaining the first sampled edge direction. Both US and JP yield 35,684,352
samples, 987,984 candidates after geometry refresh and the ordinary-air check,
and zero preserving first-quarter ground-pound candidates. A full-game check
of **one** selected new position gives 94 successive ordinary-air updates,
but ground pound leaves it on first descent without an impact.

The [long-hold follow-up](../../docs/notes/ttc-cog-1200-frame-hold.md) extends
that same ordinary-air control to 1,200 checked frames in US/JP. The original
94-frame duration was the recording cutoff, not an observed failure. Its
input and checks are `control-a-1200.csv` and `report-long-hold.py`, with
receipts in `results-1200.json`. The STOPPED/RANDOM-mode distinction remains.

## Native search

Run from the proof repository in Ubuntu-24.04 with Python 3.12, Git and GCC.
The sibling `reference-sm64-decomp` must contain the pinned commit. Generated
US/JP Clight units must already be present. No ROM is required for this stage.

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-geometry/run.py --version us --angle-step 1024 --edge-segments 32
python3 Pedro-Coq/instrumentation/ttc-cog-geometry/run.py --version jp --angle-step 1024 --edge-segments 32
```

Results and authenticated source extracts go to `Pedro-Coq/build/cog-geometry/`.
The runner checks mesh/sine bits against generated initializers and known
N64 observations before scanning. `--angle-step` must divide 65,536 and be a
multiple of 16; `--edge-segments` is bounded to 1–256. A smaller angle step
increases pair counts quadratically. The defaults are a smaller pilot, not the
recorded 1,024-step scan.

## Selected complete-game replay

This stage needs the existing authenticated matching-build cache and the
emulator dependencies documented in [placement instrumentation](../ttc-cog-placement/README.md).
The `search_edge_a` preset declares the near-cog spawn, rather than supplying
a normal-entry route. The stock STOPPED setting is a geometry diagnostic,
separate from RANDOM-mode reachability. All subsequent control uses ordinary
inputs. The existing observer is unchanged and only reads guest state.

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-placement/prepare.py --setup search_edge_a --clock-mode stopped
make -C Pedro-Coq/build/cog-placement/search_edge_a_stopped/source VERSION=us COMPARE=0 -j2
make -C Pedro-Coq/build/cog-placement/search_edge_a_stopped/source VERSION=jp COMPARE=0 -j2
```

Use fresh trial directories. The following names reproduce those consumed by
`report.py`; if they already exist, preserve them and choose new names, then
adjust the report's explicit inventory.

```sh
P=Pedro-Coq/instrumentation/ttc-cog-placement
G=Pedro-Coq/instrumentation/ttc-cog-geometry
python3 "$P/run.py" us geometry_a_control_us --setup search_edge_a --clock-mode stopped --waypoints "$G/inward-a.csv" --trace-ground-pound --video-frames 470
python3 "$P/run.py" us geometry_a_replay_us --setup search_edge_a --clock-mode stopped --inputs "$G/control-a.csv" --trace-ground-pound --video-frames 470
python3 "$P/run.py" jp geometry_a_control_jp --setup search_edge_a --clock-mode stopped --inputs "$G/control-a.csv" --trace-ground-pound --video-frames 470
python3 "$P/run.py" us geometry_a_z4_us --setup search_edge_a --clock-mode stopped --inputs "$G/ground-pound-a-z4.csv" --trace-ground-pound --video-frames 470
python3 "$P/run.py" jp geometry_a_z4_jp --setup search_edge_a --clock-mode stopped --inputs "$G/ground-pound-a-z4.csv" --trace-ground-pound --video-frames 470
python3 "$G/report.py"
```

`control-a.csv` is the observed steering input, compressed to a constant stick
interval. `ground-pound-a-z4.csv` reproduces it with exactly one Z press at
frame 4. `report.py` reruns the existing trace, successive-update and
ground-pound checks, compares full normalized traces and the pre-Z prefix,
and writes [results.json](results.json). It does not infer a successful impact
from stationary startup frames. The finite negative result leaves broader
state families and complete semantic proofs open.
