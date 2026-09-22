# A 1,200-frame stopped-clock Pedro hold

Checked on 2026-09-21 in `VERSION_US` and `VERSION_JP`, using pinned source
`9921382a68bb0c865e5e45eb594d9c64db59b1af` and the existing `search_edge_a`
near-cog initialization.

**The earlier 94 successive updates were 94 game-logic frames. The same
control now passes 1,200 successive frames in both versions.** Mario remains
at `(1308, -2088, -1088)` while both relevant cog poses stay fixed. His
forward-speed field increases from zero to approximately **205.567291**.
The two versions agree on all **38,132 normalized observations**.

This uses TTC's stock **STOPPED clock setting**. It does not demonstrate
1,200 frames of RNG-controlled stasis in RANDOM mode, a route from ordinary
level entry, or a preserving RNG-producing action. No Coq theorem changes.

## What the frame count means

The previous trial ended the emulator at the chosen rendered-frame cutoff
470. Its TTC snapshots ran from relative frame 0 through 94, with global
timer values 377 through 471. Those 95 snapshots bracket 94 complete checked
Mario updates. There was no observed loss of the spot at that cutoff; 94 was
the recorded duration, not a maximum hold time.

The extension changes only the controller recipe's duration and the recording
cutoff. It holds the same raw stick `(75, 28)`, with no button presses, through
relative frame 1200. The new cutoff is rendered frame 1576. There are 1,201
TTC snapshots, relative frames 0–1200 and global timer values 377–1577, with
an increment of exactly one between snapshots. Updates **0–1199** therefore
have complete beginning/following brackets and pass the strict preservation
check.

The final observed update, numbered 1200, has no following snapshot because
recording ends. The checker reports that missing bracket; it does not report
Mario moving. The receipt retains this qualification instead of silently
counting an extra frame.

In the pinned `src/game/game_init.c`, `display_and_vsync` waits for two video
interrupts and increments `gGlobalTimer` once per game-loop iteration. US/JP
normally run these updates at **30 per second**. Thus 94 updates correspond
to about **3.13 seconds**, and 1,200 to about **40 seconds** at normal speed.
These are game-logic frames, not 60 Hz video interrupts or the emulator's
elapsed wall-clock time. Lag can make a fixed update count take longer to
display; this discovery replay disables emulator speed limiting.

## Preservation and comparison checks

The unchanged `check-preservation.py` requires more than equal endpoints:

- Every accepted update has a complete `execute_mario_action` entry/return,
  one geometry refresh, and a following input-poll snapshot.
- Mario's XYZ is unchanged at all recorded helper and air-quarter boundaries;
  there is no platform reference.
- The actual-position floor remains more than 100 units below Mario. Each
  nonzero inward air query selects the slot-29 floor and slot-32 ceiling and
  takes the close-gap landed return while retaining the distant floor.
- Both cog poses remain fixed across helper boundaries and the bracketing
  snapshots.

The actual-position floor is at -8191, while attempted movement finds the cog
floor at -2088 and ceiling at -1934, a 154-unit gap. Rejected movement can
leave Mario stationary while his stored forward speed grows. This is a
finite ordinary-air hold, not ground-pound startup or an impact on an already
supporting floor.

Both extensions reproduce all **2,975 normalized observations** in the
original checked updates 0–93. The consistency checker verifies balanced
action calls, selected-surface records, consecutive inputs and the ordered
RNG recurrence. US/JP normalization removes version-specific addresses and
compares object slots.

## Relation to the active RNG target

STOPPED is the normal clock setting that already leaves freshly initialized
cogs at zero speed. It is distinct from global Time Stop and from RANDOM
mode choosing zero targets through RNG. No in-spot RNG manipulation was
needed to keep these diagnostic cogs stationary.

The [earlier ground-pound continuation](ttc-cog-geometry-search.md) still fails
on first descent. Extending the ordinary-air control does not repair it. A
1,200-frame RANDOM-mode result separately needs the correct reachable cog
state and a verified RNG schedule or preserving input choice. The STOPPED
hold supplies neither missing fact.

## Receipts and reproduction

The [input](../../instrumentation/ttc-cog-geometry/control-a-1200.csv),
[receipt builder](../../instrumentation/ttc-cog-geometry/report-long-hold.py),
and [checked receipt](../../instrumentation/ttc-cog-geometry/results-1200.json)
record the prefix comparison, complete runs, timer ranges, milestone snapshots,
and checks/source/build/input/observer/trace hashes. The initialization patch
and game binaries are unchanged from the preceding geometry investigation.
Cheats remain disabled; the unchanged observer only reads guest state. Raw
logs remain in the ignored build tree.

From the proof repository in Ubuntu-24.04, using the prepared builds and fresh
trial directories:

```sh
P=Pedro-Coq/instrumentation/ttc-cog-placement
G=Pedro-Coq/instrumentation/ttc-cog-geometry
python3 "$P/run.py" us geometry_a_1200_us --setup search_edge_a --clock-mode stopped --inputs "$G/control-a-1200.csv" --trace-ground-pound --video-frames 1576
python3 "$P/run.py" jp geometry_a_1200_jp --setup search_edge_a --clock-mode stopped --inputs "$G/control-a-1200.csv" --trace-ground-pound --video-frames 1576
python3 "$G/report-long-hold.py"
```

Publication follow-up, 2026-09-21: the official Sites bundle was recovered
through the connected resource catalog. Version 3 of the owner-only
[private site](https://pedro-proof-notes.tra38.chatgpt.site) now reports this
1,200-update result and carries an exact copy of its receipt. Its verdict
agrees: the STOPPED hold does not establish preserving RANDOM-mode RNG
control. See the [publication record](ttc-cog-site-publication.md).
