# Reviewing the video's 1,200-value RNG argument

Reviewed 2026-09-22 for `VERSION_US` and `VERSION_JP`, using decomp source
`9921382a68bb0c865e5e45eb594d9c64db59b1af` and its generated Clight.

**The video correctly identifies the scheduling problem. It does not prove
that no legal 1,200-frame setup exists.** An exact check of a fully specified
candidate is practical; finding a reachable successful candidate remains
open. Searching only the raw 65,114-value RNG cycle cannot settle it.

## What the video actually argues

The supplied copy of [TTC Pedro Spot on Cogs Update](https://www.youtube.com/watch?v=X4k5NGUjTWs)
was reviewed through its on-screen captions, diagrams, gameplay and concluding
pages, including the state table at 4:00 and the still-frame graph around
6:27. Its SHA-256 remains
`5e2673ec71721d3c1bea0df8391b2b93b136ec11c016c8a5229d672a1990e302`.
The source ROM version and the footage's setup provenance are unverified.
This review does not claim an audio transcription or a rerun of the author's
original simulator. Earlier footage observations remain in the
[video review](ttc-cog-video-review.md).

The argument is more careful than “there are 65,114 seeds, so just try them”:

1. The proposed route needs roughly 40 seconds / 1,200 game updates with a
   relevant cog still. It assumes Mario cannot influence RNG from that spot.
2. Each still cog update needs another favorable magnitude selection to
   continue stillness, approximated as a one-in-seven chance.
3. The video explicitly rejects treating the RNG seed as the whole state.
   Other objects consume the same stream, and their timers determine which
   values reach the cog. It already compresses equivalent spinner histories
   to the time remaining until the next draw.
4. Its object-state product is about `1.0492 × 10^155`. It combines a rounded
   `7^-1200` success estimate with that state count, then describes a simulator
   reportedly checked against 50 hours of game behavior.
5. The reported forward search finds short streaks; the graph reaches 12
   still frames after about 52 simulated years. Extrapolation gives an
   astronomical wait for 1,200. The conclusion is practical infeasibility and
   doubt that any successful state exists, not an exhaustive exclusion.

The graph measures game time advanced while searching for a streak, not the
CPU time needed to verify one specified 1,200-update candidate. We have not
independently certified its 69-object inventory, full state quotient or
waiting-time samples against the US/JP scheduler.

The video discusses one relevant cog. Our current preservation checker keeps
both selected cog poses fixed. That stronger diagnostic must not silently
replace the video's geometry or turn its probability into a two-cog theorem.

## The actual cog rule

The generated `f_bhv_ttc_cog_update` first approaches the existing target by
50. If that target is reached, it selects the next target as:

```c
200.0f * (random_u16() % 7) * random_sign()
```

`random_sign` consumes another `random_u16` value even when the magnitude is
zero. Its sign cannot turn a zero magnitude into a nonzero target. Thus two
draws do **not** make the zero-target condition a one-in-49 event: only the
first value's remainder matters for this one cog.

For an already zero-speed/zero-target cog, the approach returns true each
update. Repeated zero magnitudes keep selecting zero targets. A selected
nonzero target causes motion on the following update; a bad draw need not
move the cog on the same update. Consequently, starting with zero speed and
target, a window of 1,200 stationary updates needs the first 1,199 new targets
to be zero; the last selection may be nonzero if motion after the window is
allowed. Requiring 1,200 zero selections is a convenient stronger condition,
not an exact accounting of every possible endpoint convention.

These statements are source analysis of the generated function. The existing
local zero-target execution proof and departure proof cover concrete cases;
this review adds no whole-schedule Coq theorem. The previously failed RANDOM
initialization already had targets 800/200 and therefore says nothing
exhaustive about a properly prepared zero-target phase.

## The finite checks now performed

The [analyzer](../../instrumentation/ttc-cog-rng-sequence/analyze.py) evaluates
the generated scalar RNG body on **all 65,536 inputs**, independently comparing
every output with the unchanged pinned C function compiled in a host harness.
US/JP RNG and sign functions agree exactly; the cog function agrees after
normalizing only compiler-generated anonymous union identifiers.

The complete functional graph has one cycle of length **65,114**, containing
seed zero. Of its values, **9,320** are divisible by 7. Even the cycle-wide
marginal frequency is therefore `9320/65114`, not exactly `1/7`; that marginal
does not imply independence of successive cog selections.

| Precisely scoped sequence | Maximum consecutive zero-magnitude selections |
| --- | ---: |
| Every raw RNG output | 6 |
| Every other output: one isolated cog, including its sign draws | 6 |
| Any one fixed stride from 2 through 64 draws | At most 7 |

The maxima hold over both all 16-bit inputs and the normal seed-zero cycle.
Each fixed stride was also checked independently by filtering every initial
seed against 1,200 prescribed selections; the candidate set becomes empty
at the expected first failing selection. “Selections” in this table is not
the same count as stationary game updates, because of the target delay above.

These results **do not bound variable-gap TTC runs**. The earlier read-only
cog trace already records changing consumption by intervening objects. The
video's 12-frame example is therefore compatible with these small fixed-gap
maxima, rather than refuted by them.

For an explicit illustration, the receipt includes 1,200 suitable magnitude
draws as a subsequence of the real RNG stream starting at seed zero, with a
sign draw after each. It reaches the final sign at global draw **9,731**;
successive magnitude gaps range from **2 to 68**. This is constructed by
assigning skipped values to unspecified other consumers. It is deliberately
an arithmetic relaxation: **no TTC object schedule, controller sequence or
preserving game state is supplied by that example**. It demonstrates why
absence of a long raw run is insufficient, not why the gameplay strategy works.

The machine-readable [receipt](../../instrumentation/ttc-cog-rng-sequence/results.json)
contains hashes, exact witnesses, all 64 fixed-stride results, and the relaxed
example's full draw-index list. The host AST evaluator and C compiler are
cross-checks, not formally proved Clight/N64 refinements. No game state,
emulator state, cog target or RNG seed is modified by this analysis.

## What is accurate, and what is only an estimate

The video's distinction between RNG state and the other objects' scheduling
state is supported by the code and our recorded object order. Its assumption
of no usable in-spot influence is still unproved for all actions and objects;
our tested preserving input recipes have not contradicted it.

The probabilities are a heuristic. The game is deterministic, candidate
states are correlated, and a product of possible per-object states does not
establish joint gameplay reachability. Independent uniform success at each
selection is an additional model assumption. Treating candidate successes
as independent in `1 - (1-p)^N` is another assumption.

The numerical expression itself is easy to approximate stably:

```text
p = 7^-1200                       ≈ 7.626969 × 10^-1015
N = 10^155
N p                               ≈ 7.626969 × 10^-860
1 - (1-p)^N                       ≈ N p  (under that probability model)
```

This avoids subtracting two rounded numbers near one. A union bound of `Np`
would not need independence between candidate successes if each candidate's
success probability were bounded by `p`. The unresolved premise is applying
that probability model to the actual deterministic scheduler. Neither this
calculation nor the short-streak extrapolation proves absence of a rare
structured orbit or establishes a required exhaustive-search cost.

## A more direct decision procedure

For an **externally fixed call schedule**, the new checker accepts the global
indices of the cog's magnitude draws. It precomputes powers of the actual RNG
transition, tests every initial seed and rejects it at the first nonzero
remainder. This answers the exact sequence question without waiting through
the intervening game frames. The supplied schedule remains a hypothesis.

For **one fixed complete non-RNG state**, a valid seed sweep instead has to
execute each seed's own object continuation. Reusing the observed call counts
from one seed for all seeds would be wrong: seeds change target choices,
timers and the future draw schedule. A surviving candidate then needs Mario's
complete preserving path and actual entry provenance checked.

For **many possible preparations**, a useful next search is a bounded
constraint problem over the real RNG-relevant object transitions and their
update order, retaining any relevant global, camera, interaction and object-pool
state as well. Constrain the cog's magnitude draws to zero remainders,
eliminate failing prefixes, and merge states only when their future RNG
behavior is proved equivalent. The video already performs some such state
reduction; further reduction and symbolic solving may help, but have no
guaranteed tractability. A satisfying assignment would still need replay and
reachability checks. An unsatisfiable result would apply only to the modeled
initial-state family and proven coverage.

The subsequent [tractability investigation](ttc-cog-scheduler-tractability.md)
gives a conditional `65,536 * 1,200` frame-evaluation bound when only the seed
varies and every other initial component and input is fixed. It does not give
a wall-clock bound or a practical guarantee for searching all preparations.
Future RNG-dependent scheduling creates one continuation per seed, not a new
independent choice at every draw.

**Implemented in this video review:** generated-scalar/C cross-checks,
fixed-stride exhaustive analysis and a prescribed-schedule seed filter. The
subsequent [bounded sweep](ttc-cog-seed-sweep.md) executes the compiled game-thread
continuation for each seed under an explicit external-system model: all 393,216
cases in three STOPPED-derived US/JP snapshot pairs fail within four updates.
This is not a full N64/Clight refinement, all-preparation coverage or a legal
1,200-frame RANDOM-mode witness. The active gameplay result remains open.

The repository proof-discipline audit passes with the installed
`SM64_PROOF_SWITCH=sm64-item-proof`. The default absent `sm64-proof` switch
initially prevented its build phase; rerunning with the existing documented
switch resolved that environment issue. No proof statements or assumptions
were changed in this investigation.

This review and its receipt are published in owner-only site version 4,
in the [video argument section](https://pedro-proof-notes.tra38.chatgpt.site/#video-argument).
See the [publication record](ttc-cog-site-publication.md) for source provenance
and access verification.
