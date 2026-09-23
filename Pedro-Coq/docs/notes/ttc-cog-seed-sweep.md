# Bounded seed sweep over three cog snapshots

Investigated 2026-09-22. Scope: `VERSION_US` and `VERSION_JP`, source pin
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

**Scope correction, 2026-09-23:** this historical experiment used STOPPED-derived
states and did not satisfy the request for actual RANDOM preparations. The
[corrected RANDOM-phase experiment](ttc-cog-random-seed-sweep.md) preserves the
captured clock mode, cog angles and timers, varies only the seed, and reports
its separate ledge-context scheduling and geometry results.

**Implemented and ran the bounded sweep: all 393,216 cases were rejected;
the longest preserving prefix was three complete updates.** Every rejection
was an observed cog yaw change. No case in this sweep exhausted its budget or
encountered unsupported execution. This is a finite result of the documented
offline execution model, not a Coq impossibility theorem or an exclusion of
other RANDOM preparations.

The [machine-readable receipt](ttc-cog-seed-sweep-results.json) records coverage,
histograms, longest seeds, source/build/snapshot hashes, calibration differences
and timings. The [implementation and reproduction instructions](../../instrumentation/ttc-cog-seed-sweep/README.md)
describe the exact boundary model and acceptance predicate.

## What was enumerated?

Three read-only snapshots were taken at entry to `level_script_execute` during
the already authorized `search_edge_a` STOPPED replay. They share Mario's
position `(1308, -2088, -1088)` and zero yaw, speed and target for cog slots
29 and 32. The complete recorded RAM image, including all object/list state,
is retained separately for each case.

| Snapshot relative update | Global timer | Mario forward speed | Versions | Initial seeds per version |
| --- | --- | --- | --- | --- |
| 0 | 377 | 0 | US, JP | 65,536 |
| 30 | 407 | about 31.80537 | US, JP | 65,536 |
| 100 | 477 | about 42.20158 | US, JP | 65,536 |

In an offline copy of each snapshot, the candidate constructor changes only
the clock setting to RANDOM and the initial 16-bit RNG seed. It then retains
the fixed raw stick `(75, 28)` and no buttons. These are **hypothetical
STOPPED-derived RANDOM initializations**, not recorded RANDOM entry states.
No permitted gameplay path producing these combinations of clock mode, timers,
poses and seed has been established. They are three times at one geometry,
not three different cog configurations.

Each candidate executes its own compiled `level_script_execute`, including
the actual object scheduler, behavior command loops, Mario, camera and rendering.
RNG consumers and the timers they change are executed afresh for that seed.
The implementation does not replay one seed's draw indices for other seeds.
It makes no independent-uniform RNG assumption.

## Exhaustive results within that family

Each of the six version/snapshot combinations produced the same distribution:

| Complete preserving updates before rejection | Seeds per case |
| --- | --- |
| 1 | 64,207 |
| 2 | 1,292 |
| 3 | 37 |
| 4 through 1,200 | 0 |
| Unknown or resource-limited executions | 0 |

All 65,536 seed identifiers appear exactly once in each CSV. After removing
the version-specific instruction address, all six CSVs are identical, including
their per-seed ordered-RNG fingerprints. Thus the different elapsed times and
Mario speeds did **not** supply different short scheduling results in this
experiment. This observed agreement is not a theorem permitting arbitrary
states or later trajectories to be merged.

The bound was 1,200 complete updates, with early rejection when a relevant cog
actually changed yaw. Selecting a nonzero target on the final accepted update
is allowed: the cog has not necessarily moved yet. A separate check accepts
seed 0 for a one-update horizon and rejects its second update. This avoids
silently substituting 1,200 zero selections for 1,200 stationary updates.

The predicate also requires Mario's position at each observed action return
and complete frame return to stay fixed, his retained floor and lack of an
actual supporting platform to persist at the frame boundary, and an actual
close-gap return using the two relevant cog surfaces in every accepted frame.
Both relevant cog updates must occur exactly once. These are checked program
boundaries, not a proof that every intermediate instruction preserves every
field or that all possible Pedro holds satisfy this predicate.

Enumeration took about **520 seconds (8 minutes 40 seconds)** with six concurrent
jobs on this host. That measurement excludes capture, building, calibration
and subsequent independent replays. It is not a worst-case elapsed-time
guarantee. There were 66,902 complete preserving updates per case, followed
by 65,536 rejected partial updates; early rejection made the 1,200-update cap
irrelevant for these particular seeds. No symbolic constraint solver was needed.

## Calibration and the remaining semantic boundary

The offline engine is Unicorn 2.1.4 in MIPS64 big-endian R4000 mode. The initial
RAM and GPR/FPR/CP0 receipts are read-only observations from the existing emulator.
The observer checks loaded routine bytes against the declared ELF. The new
capture option leaves the prior US control's 94-update prefix unchanged across
4,479 normalized observations after removing only the new frame-boundary records
and sequence numbers.

For each version, seven baseline comparisons cover one and two updates from
each snapshot plus 102 successive updates from snapshot 0. Mario, the complete
object pool, camera, controller data, graphics pools/matrices and the other
listed gameplay regions agree byte for byte with the emulator. All ordered
gameplay RNG draws and the final seed agree. The positive preservation check
accepts all 102 STOPPED updates. Every one of the 37 longest seeds in each of
the six cases was also replayed in isolation and matched its batch result.

The model between game-thread calls increments the global timer, advances
framebuffer indices, toggles the game profiler index and executes the actual
`select_gfx_pool`. It retains fixed controller data. It does **not** execute
audio/OS/device threads, display/vsync or controller polling. Function-entry
restoration assumes no live HI/LO values and default floating-point control.
Audio, OS and profiler memory therefore differs from the full emulator; the
receipt retains the full difference inventory rather than claiming full RAM
identity. The two un-sized ELF gaps in that inventory are adjacent to the VI
contexts and OS task/stack storage. Noninterference of every omitted system
for every searched trajectory has not been proved.

Additional unedited RANDOM-mode reference snapshots check the first complete
frame in each version: 39 ordered RNG draws agree, and only five profiler
timestamp bytes differ in the entire RAM image. The following two reference
frames in each version reach the MI interrupt-mask register at physical address
`0x0430000c` while `__osEnqueueAndYield` runs. Those four calibration cases are
**unknown**, because this executor does not emulate that device. They are
separate from the six exhaustive sweep cases and cannot be counted as failures.
Eight hypothetical seed samples per version also agree between the Python
reference driver and native batch driver on their first complete frame.

Every invocation has a translated-block budget. A deliberately insufficient
budget returns `unknown`; API/CPU/device errors and unexpected boundaries do
likewise. A supervisory timeout aborts coverage instead of manufacturing
rejections. During development, an optional memory-write tracing hook caused
an emulator exception in a normal MIPS branch-delay path. Removing that optional
hook restored agreement; the final evaluator resets the complete RAM copy
between seeds and does not contain that optimization.

## What follows, and what does not

This implements the narrow experiment proposed by the
[tractability investigation](ttc-cog-scheduler-tractability.md). It demonstrates
that per-seed scheduling can be evaluated and exhaustively checked for this
small declared family in minutes. It supplies **no successful 1,200-update
RANDOM witness**, no preserving input choice that changes RNG and no guarantee
for searching all preparations.

The next useful family should vary actual RANDOM-mode object preparation and
timers, with naturally stationary cog phases and explicit gameplay provenance;
the three STOPPED-derived cases supplied no additional short scheduling diversity.
Any newly unsupported execution must remain unknown or receive a validated
external-system implementation. A gameplay exclusion additionally needs the
execution/refinement and reachability arguments, not merely these counts.

No generated Clight, Coq statement or proof assumption changed. No capstone
obligation was discharged. The work supplies experimental search infrastructure
and a precisely scoped negative result. It remains separate from the SSL proof.

Published in owner-only [site version 6](https://pedro-proof-notes.tra38.chatgpt.site/#seed-sweep).
The [publication record](ttc-cog-site-publication.md) identifies the exact source
commits, successful deployment and unchanged private audience.
