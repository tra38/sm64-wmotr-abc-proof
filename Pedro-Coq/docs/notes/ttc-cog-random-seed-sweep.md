# Corrected seed sweep: a captured RANDOM phase

Investigated 2026-09-23. Scope: `VERSION_US` and `VERSION_JP`, source pin
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

**The earlier experiment answered the wrong preparation question:** it changed
STOPPED snapshots to RANDOM offline. This experiment captures an already
RANDOM phase and varies only its initial seed. The clock mode, cog angles,
speeds, targets, object timers and Mario state are retained exactly from that
snapshot. The historical [STOPPED-derived result](ttc-cog-seed-sweep.md)
remains valid within its stated hypothetical family, but does not answer the
user's request for actual RANDOM starting states.

**Result: 131,072 seed cases, all rejected by cog movement, maximum three
complete stationary updates, zero unknown cases.** This is one RANDOM phase
per version with Mario on the ledge. It is not a Pedro-preserving run, a Coq
theorem, or an exclusion of other RANDOM preparations. The
[metadata receipt](ttc-cog-random-seed-sweep-results.json) and
[reproduction instructions](../../instrumentation/ttc-cog-random-seed-sweep/README.md)
record the exact family and execution boundary.

## How the RANDOM state was obtained

The existing authorized near-cog `ledge` initialization places Mario at
`(1742,-2088,-125)` and initializes TTC to RANDOM before gameplay. It changes
only the three previously declared initialization source files; subsequent
behavior functions are stock pinned source. From there, neutral controller
input advances the game naturally. No runtime memory editing, cheats, ACE or
collision corruption is used. This is still a test placement, not ordinary
level-entry provenance.

A read-only survey recorded **11,625 input boundaries** in US, all with clock
mode 2 (RANDOM), no time stop, and Mario on the same ledge. For the original
cog pair, slots 29/32, only relative frame **836** had both target speeds zero
and absolute angular speeds at most 50. The next approach-to-target step can
therefore leave both yaws unchanged. The three other previously studied pairs
had no such simultaneous opportunity in this particular survey.

The frame-836 starting state has global timer 1213 and seed 13197:

| Cog | Raw yaw | Yaw modulo 65,536 | Angular speed | Target speed |
| --- | --- | --- | --- | --- |
| 29, lower | 45,000 | 45,000 | -0 | -0 |
| 32, upper | -21,800 | 43,736 | 50 | -0 |

The upper cog is approaching its stop in the entry snapshot; it is not
already speed zero. Its next update reduces speed to zero before adding it to
yaw. The original-seed reference completes that first still update. This is
a pause opportunity, not evidence of a long pause.

Independent US and JP replays capture RAM/register receipts at entry and exit
of updates 836–838. Their 845-frame logical input/Mario/cog prefixes agree
after removing version-specific pointer addresses. The US capture's complete
input/Mario/cog prefix matches the earlier survey exactly. Both have cheats
disabled, zero observer errors and normal emulator exit.

Only the original seed is actually observed with this non-seed state.
Enumerating alternative seeds in an offline copy does not establish that
every combination is reachable by permitted gameplay.

## What was checked for every seed

For each version, a fresh copy of the frame-836 state executes its own
compiled game-thread continuation from each seed in 0..65535. No clock, cog,
timer or Mario field is changed during candidate initialization. Inputs remain
neutral. Each accepted complete update requires exactly one update of each
relevant cog and unchanged cog yaw at its update return and the complete
frame return. A new nonzero target is allowed until it actually moves the cog.

The 1,200-update cap uses early rejection. **Mario is not required to be in a
Pedro spot in this scheduling experiment.** The recorded ledge context is
retained, and Mario's ordinary action, object, camera and rendering paths
execute. Bringing Mario into the candidate geometry would change object
activity and requires a new initial-state capture and seed sweep; this result
cannot be transferred merely because the cog angles are the same.

Each version gives the following distribution:

| Complete stationary updates before a cog moved | Seeds |
| --- | --- |
| 1 | 64,185 |
| 2 | 1,326 |
| 3 | 25 |
| 4 through 1,200 | 0 |
| Unknown or resource-limited | 0 |

The normalized US/JP CSVs are identical after removing the instruction
address. Each includes all 65,536 seeds exactly once. All 25 longest cases
were replayed independently in each version and matched their batch results.
Those longest cases consumed 19, 21 or 23 RNG draws before rejection,
depending on the seed: the actual per-seed object schedule is being executed,
not a prescribed fixed sequence of draw indices. Enumeration took about
**4 minutes 48 seconds** with two concurrent jobs on this host, excluding
setup, capture, validation and independent replays. This is a measurement,
not a worst-case guarantee.

## Geometry at these captured angles

The separate pinned-source collision filter uses all eight recorded cog angles
and the static TTC mesh. It samples 2,178 lower-cog perimeter positions,
using 33 edge fractions, 11 offsets and up to five inward strides. In both
versions, **319 samples produce the close-gap air return** while retaining
position and floor; **257 also survive the immediate geometry refresh** with
the off-floor flag and without the squished flag.

For example, `(1455.87915,-2088,-1136.49268)` passes with inward quarter-step
stride 1. These are local host-execution candidates, not 257 reachable setups
or full preserving action continuations. Other dynamic objects are not
reconstructed by this geometry filter. Mario was not moved from the ledge in
the emulator to obtain these samples. Unsampled positions are not excluded.

## Calibration and external execution limits

The original offline engine failed on this phase's first animation load:
OS yielding tried to read the unsupported MI interrupt-mask register. That
was recorded as **unknown**, never as a bad seed. The corrected engine adds an
explicit animation-DMA external contract, restricted to the authenticated ROM
animation segment and Mario's allocated 16 KiB buffer. It performs the
16-byte-aligned copy specified by pinned `memory.c:dma_read`; actual table
selection and gameplay/animation code continue to execute. Other requests
remain unknown. All 131,072 candidates used exactly one such transfer.

For each version, the original-seed one-, two- and three-update continuations
match the independent emulator in the complete object pool, Mario, camera,
controller, graphics pools/matrices, animation buffer and other listed
gameplay regions. Their ordered RNG counts are 7, 12 and 14, and their final
seeds match. Validation also checks a positive still update, explicit fuel
exhaustion as unknown and batch-state isolation.

The shared engine's default configuration was also regression-checked against
the earlier 102-update STOPPED replay in both versions: the full preserving
predicate succeeds, listed gameplay regions match, and no DMA adapter is used.

The adapter does not simulate cache, OS message queues or thread scheduling.
Audio/display/device work between game-thread calls remains omitted, and
the original function-boundary CPU assumptions remain. The report retains
whole-RAM differences by symbol, including OS/audio/profiler differences.
Calibration does not prove those differences irrelevant to every trajectory;
there is no full N64/Clight refinement or new CompCert execution theorem.

## What remains open

The corrected experiment supplies a reproducible RANDOM phase with candidate
geometry and a measured seed-only scheduling exclusion in its ledge context.
It does not establish normal-entry reachability, preserving in-spot RNG
control or a 1,200-frame RANDOM hold. More RANDOM preparations, controller
policies and complete in-spot states remain unsearched. The next useful step
is a full RANDOM capture after a permitted entry into valid cog geometry,
followed by this same per-seed continuation check with Mario preservation
restored to the predicate.

The repository proof-discipline audit passed; no proof statement, generated
AST, assumption or capstone obligation was changed or discharged. This is
experimental evidence, kept separate from the local Coq results.
