# Bounded cog geometry search and complete selected continuation

Investigation on 2026-09-21, for `VERSION_US` and `VERSION_JP`, at pinned source
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

**The search finds many ordinary-air geometry candidates, but no candidate
that passes its ground-pound preservation filter.** In each version,
35,684,352 sampled position/pair-pose combinations produce 987,984 candidates
that admit a close-gap air return and survive the actual geometry refresh.
None preserves ground pound's first quarter-step under the specific conditions
below. These are finite native checks, not a Coq exclusion theorem.

One newly selected position, `(1308, -2088, -1088)`, was then checked in the
complete game. It preserves an ordinary-air Pedro hold for **94 successive
updates**, with both cogs stationary and increasing forward speed. A Z press
after four matched updates enters ground pound, but its first descent leaves
the spot and becomes knockback without an impact. The following full update
moves Mario farther out. Independent US/JP replays agree.

The [1,200-frame follow-up](ttc-cog-1200-frame-hold.md) extends that same
ordinary-air control successfully in both versions. The original 94 updates
were a recording cutoff, not an observed maximum. This report retains the
original short-run counts and ground-pound comparison.

The emulator uses the stock **STOPPED clock setting** and the previously
authorized near-cog initialization method. It does not establish normal entry,
a naturally occurring RANDOM-mode still interval, or preserving RNG control.

## What was searched

The native harness executes the unchanged pinned surface loading, collision
search, wall resolution, `update_mario_geometry_inputs`, and
`perform_air_quarter_step` routines. It constructs hypothetical states only in
an offline host process. It is never linked into a ROM or emulator.

The scene contains TTC's static terrain and all eight cog collision models,
including their ordinary 400-unit collision-loading gate. **Other dynamic
objects are omitted.** Two selected cog yaws vary; the other six remain at
their macro initial yaws. Thus the counts concern this declared scene, not
complete reachable game states.

The four nearby pairs with positive candidate vertical gaps are:

| Lower / upper macro slot | Nominal top-to-underside gap | Pair-pose assignments | Unique sampled X/Z per assignment, summed | Survive refresh and ordinary-air filter | Preserve GP first quarter |
| --- | ---: | ---: | ---: | ---: | ---: |
| 29 / 32 | 154 | 4,096 | 8,921,088 | 987,984 | 0 |
| 29 / 33 | 1 | 4,096 | 8,921,088 | 0 | 0 |
| 33 / 31 | 154 | 4,096 | 8,921,088 | 0 | 0 |
| 32 / 31 | 1 | 4,096 | 8,921,088 | 0 | 0 |
| **Total per version** | | **16,384** | **35,684,352** | **987,984** | **0** |

The table's gaps describe the pair's mesh heights; the actual collision
search still has to select that pair. The pair selection and positive-gap
restriction are part of the experiment's scope, not an all-surface coverage
theorem. Slot 29 is centered at `(1490, -2088, -873)` and slot 32 at
`(1215, -1781, -1215)`.

Sampling rules are explicit and reproducible:

- Each selected cog uses yaws `0, 1024, ..., 64512`: **64 orientations each**,
  or 4,096 pairs. The sine lookup uses `angle >> 4`; this scan covers only
  64 of its 4,096 lookup orientations per cog, not all 65,536 angle values.
- At each pose, the mesh's top perimeter is derived from triangle edges.
  Each of its six edges is sampled at 33 equally spaced parameters. Signed
  outward offsets are `-0.5, -0.125, 0.125, 0.5, 1, 2, 4, 8, 16, 32, 48` units.
  Y equals the lower cog's top. Equal binary32 X/Z values are counted once per
  pair-pose, retaining the first encountered edge's inward direction.
- The actual-position floor must exist and be more than 100 units below Mario.
  Tested inward quarter-step displacements have lengths `1, 4, 16, 32, 64`,
  with Y displacement -1. A candidate needs at least one actual landed return
  selecting the chosen cog floor/ceiling with `0 < gap <= 160`, unchanged XYZ,
  and unchanged retained floor pointer and height. These displacement choices
  are not a proof of controller reachability.
- A separate actual geometry refresh must leave XYZ unchanged, report
  `INPUT_OFF_FLOOR`, and not report `INPUT_SQUISHED`. An isolated air return
  whose next refresh pushes Mario away does not survive this filter.
- Finally, the surviving geometry is tested with `ACT_GROUND_POUND`, zero
  horizontal velocity, vertical velocity -50, and a first-quarter displacement
  `(0, -12.5, 0)`. It must select the same close-gap pair and retain XYZ/floor.

Before the geometry-refresh filter, 1,331,088 samples produce the ordinary-air
return; 987,984 survive refresh. All 4,096 sampled poses of pair 29/32 contain
ordinary-air candidates. None of those 987,984 samples passes the ground-pound
quarter-step filter. An early pilot without the refresh check had misleading
apparent candidates: wall resolution moved Mario before the tested descent.
Those are excluded from the final counts.

This is a **strict fixed-XYZ family**, including internal quarter-step
boundaries. The ground-pound filter is a necessary condition only for a direct
descent from that unchanged anchor with these velocity/scene conditions. It
does not exclude entering during an earlier descent, changing height or moving
within a larger viable region, external object interactions, different surface
histories, or geometry between the samples. No complete native action/particle
scheduler was run for all 987,984 samples; they fail this earlier condition.

## Source authentication and native-execution limits

The runner extracts and byte-authenticates the pinned source and headers.
Macro placements, cog collision arrays and sine-table bits are read from the
generated Clight initializers and compared between US/JP. The compiled native
meshes and sine table are checked against those generated values. Collision
transforms use the game's terrain-coordinate conversion, not a separate
floating-point polygon approximation.

GCC uses `-ffp-contract=off -fno-fast-math -fexcess-precision=standard`, with
the host `AVOID_UB`/`NON_MATCHING` build definitions. A narrow host-pointer
adapter handles the irrelevant DDD room comparison; it is not an N64 address
refinement. A fail-stop warp stub must remain unreachable. Both builds also
reproduce the previously observed close-gap return and first descent at
`(1313, -2088, -1098)`.

These checks reduce transcription and implementation errors. They do **not**
prove universal equivalence between host execution, N64 arithmetic and Clight
semantics. No Coq theorem was changed and no capstone execution premise was
discharged. The proof-discipline audit passed separately.

## Full-game validation of one selected position

The earlier shortlist selected `(1308, -2088, -1088)` with facing yaw 60 degrees.
The final search additionally emits six rounded, nearby discovery suggestions;
those suggestions are not six further full-game witnesses. The selected
position has its own complete emulator receipts.

Only the three declared initialization files change in the isolated build:
`levels/menu/script.c`, `levels/ttc/script.c`, and `src/game/level_update.c`.
The initialization patch hash is
`ce9a584d7d71f198e79bd9f7cffed7fa4c7cc55c5ec2abf8443f08cf4cccd725`.
All subsequent control is controller input, with read-only observation and
cheats disabled. Cog, collision, action, particle and RNG routines are stock.

The exported control is raw stick `(75, 28)` for frames 0–94. The strict
ordinary-air checker accepts **updates 0–93**: bracketing snapshots, all observed
internal boundaries, both cog poses, far-below floor selection, and nonzero
rejected horizontal queries agree. Mario stays at `(1308, -2088, -1088)` and
his forward speed rises from 0 to approximately **41.31048** at snapshot 94.
There is no platform reference. Both relevant cog yaws and speeds stay zero.

For example, frame 0 attempts approximately
`(1308.2666, -2089, -1087.71277)`. The actual air query selects the slot-29 floor
at -2088 and slot-32 ceiling at -1934, gap 154. It returns landed while
retaining the actual-position floor at -8191 and Mario's original XYZ.

The second continuation changes only frame 4 to press Z. Its 124 normalized
observations through frame 3 match the control. The complete path is:

| Frames | Observation |
| --- | --- |
| 0–3 | Four confirmed ordinary-air Pedro updates at the anchor. |
| 4–18 | Fifteen ground-pound startup calls; forward speed becomes zero. Startup alone is not a Pedro-return witness. |
| 19 | First descent loses the cog floor query. Four quarters end at `(1264.79797, -2138, -1112.94312)`; the wall return selects backward air knockback, speed -16 and vertical velocity -54. |
| 20 | The following complete update ends at `(1250.94983, -2192, -1120.95728)`, still in backward air knockback, vertical velocity -58. |

The first two descent quarters change Y to -2100.5 and -2113 while keeping X/Z;
both select the far-below -8191 floor and return 0. The third changes X/Z to
approximately `(1264.79797, -1112.94312)` through wall resolution and returns 2.
The fourth ends at Y=-2138 and also returns 2. None takes the close-gap branch.

The complete frame-19 action returns particle mask 2 (vertical stars), not a
mist-circle request. Frame 20 returns mask 0. No mist initializer runs in these
two frames. Across the full recorded attempt there is **one ground-pound
episode, zero ground-pound impacts, and zero preserving impacts/successors**.
The requested impact stage is absent because this candidate fails before it.
Both cogs remain still through the failure.

The original steering control and its US recorded-input replay have identical
raw traces. US/JP compare equal after version-specific address normalization:

| Comparison | Matching normalized observations |
| --- | ---: |
| US steering / US recorded control | 3,007 |
| US / JP recorded control | 3,007 |
| US / JP Z4 continuation | 2,970 |

Normalization removes surface/code addresses and compares object slots. The
existing consistency checker also verifies balanced action calls, selected
surface records, consecutive input snapshots and the ordered RNG recurrence.
Checking that recurrence is not evidence of a preserving RNG choice: the
ground-pound continuation already fails preservation.

## Artifacts and remaining work

The [runner and reproduction instructions](../../instrumentation/ttc-cog-geometry/README.md)
and [machine-readable receipt](../../instrumentation/ttc-cog-geometry/results.json)
retain the bounds, source/input/observer/build/trace hashes, surface details,
descent and following-update observations, and comparisons. Raw logs and native
build products remain under the ignored `Pedro-Coq/build/` tree. No ROM or
extracted asset is included in the commit.

The result gives one more verified stationary diagnostic and a reproducible
candidate filter. A successful ground-pound route still needs a different
preserving continuation, with impact and successor checked in the complete
game, followed by normal-entry/RANDOM-mode reachability and particle/RNG
execution. Expanding the angle/position samples alone would not prove those
remaining obligations or universal impossibility.

Private-site publication is pending: the Sites skill/helper bundle is absent
from the available skill locations. The private site still carries the earlier
ground-pound result; its broad verdict agrees that preserving ground-pound RNG
control is unestablished, but it does not yet contain these new counts. No
site source or access setting was changed by this investigation.
