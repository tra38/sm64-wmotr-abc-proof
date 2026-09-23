# How many preparations are there?

Investigated 2026-09-23 for `VERSION_US` and `VERSION_JP`, source pin
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. This is existing-trace analysis and
conditional arithmetic. No new game execution, Coq theorem or capstone
discharge is claimed. The [analyzer](../../instrumentation/ttc-cog-preparation-count/README.md)
and [metadata receipt](ttc-cog-preparation-count-results.json) make the counts
reproducible.

**A completely fixed initial state, seed, controller continuation and external
inputs give one execution per version.** There are no additional hidden
preparations to enumerate. Object timers, positions, activation, allocation,
Mario and camera fields are already parts of that complete state. A previous
history cannot change the deterministic future if it leaves exactly the same
complete state and future inputs.

In the earlier timing table, a *preparation* meant a complete **non-seed**
starting state plus a fixed continuation. A seed sweep then tries all 65,536
seeds within that preparation. Each execution is fixed separately; the
starting state is allowed to differ across preparations. If the seed is also
fixed globally, there is no seed sweep, and the 4-minute-48-second whole-sweep
timing is not the cost of that single continuation.

## The video's product, with the seed factored out

The local supplied video's 4:00 table has an explicit RNG row of **65,114**.
Its displayed total, about `1.0492 * 10^155`, already includes that factor.
We transcribed each row and recomputed its product with integer arithmetic.
Combining equal factors, the non-seed product is:

```text
K_video = 165^6 * 170^2 * 100^4 * 135 * 264^12 * 259^8
          * 197 * 13821^8 * 121^14 * 181^2 * 139 * 16^2 * 2
        = approximately 1.611385936416 * 10^150
K_video * 65,114 = approximately 1.049237838638 * 10^155
K_video * 65,536 = approximately 1.056037887289 * 10^155
```

The last line uses our all-16-bit-seed domain rather than only the normal RNG
cycle. No additional `7^1200` factor belongs in this enumeration. The row
multiplicities sum to 63 before the dust and RNG rows; this is the table's
representation, not a certified physical-object inventory. The previous
review's unsupported phrase "69-object inventory" has been corrected.

Applying the existing conditional **US/JP pair** timing gives:

```text
K_video * 288.433219426 seconds
    approximately 4.647772333781 * 10^152 seconds
    approximately 1.472790178525 * 10^145 years
```

This assumes the same mean early-rejection cost, hardware and two concurrent
version jobs, excludes preparation and validation overhead, and is not a
runtime guarantee. If only one seed were tested per preparation, applying the
same amortized mean candidate cost would divide that figure by 65,536; even
that conditional arithmetic remains enormous. A long-lived single candidate
need not cost the measured mean of quickly rejected candidates.

**The video product is not the number we have proved necessary to search.**
Shared RNG and gameplay histories correlate object states, so a product can
include jointly unreachable combinations. Conversely, the displayed reduced
domains have not been proved to retain all relevant futures or all allowed
preparations. For example, the table gives each Bob-omb only 16 blink states,
but the generated `f_bhv_bobomb_loop` also checks the 4,000-unit Mario radius,
held state, lit fuse and fuse timer; its smoke initializer consumes RNG.
Those paths appear in [US](../../generated/us_obj_behaviors.v) and
[JP](../../generated/jp_obj_behaviors.v). The prior
[alternative-RNG investigation](ttc-cog-alternative-rng.md) discusses their
preservation limits. A blink-only count therefore needs explicit conditions
to serve as a complete scheduler abstraction. This observation does not
establish a usable Bob-omb setup at the cog.

Likewise, the selected cog angle, Mario's action and remembered surfaces,
camera, other particles and object order need either inclusion or a proof of
irrelevance. We have neither a complete reachable-state census nor a proved
equivalence relation merging all states with the same relevant future. The
video product is therefore neither a certified lower bound nor a certified
upper bound for the full preserving-gameplay search. Its magnitude shows why
literal enumeration of that particular Cartesian product is impractical;
it does not prove that every algorithm, or every search for one witness,
must do that much work.

## A concrete bounded family that we can count

The existing RANDOM survey is one fixed neutral-input trajectory from the
authorized near-cog ledge initialization. Its US log covers relative boundaries
0 through 11,624. The US and JP capture logs both cover 0 through 844, with
matching logical Mario/input/cog rows after pointer normalization. We checked
their hashes against the existing committed receipt before counting.

Select a boundary when the relevant cog has **target zero and absolute speed
at most 50**, the same incoming pause filter used in the corrected sweep.
The source's approach step can then bring its speed to zero. This is not a
collision, entry or complete-preservation predicate, and does not purport to
count every one-frame zero crossing with a nonzero target.

| Pause filter | Matching 845-boundary US/JP prefixes | Full 11,625-boundary US survey |
| --- | ---: | ---: |
| Lower cog (slot 29) | 10 | 107 |
| Upper cog (slot 32) | 17 | 90 |
| Both | 1 | 1 |
| Either, counting each boundary once | **26** | **196** |

The simultaneous boundary is 836 in every column, explaining why the prior
two-cog family contained just one preparation per version. Changing the
criterion to one cog exposes additional pause opportunities; it does not
establish that the other cog may move while Mario preserves the spot.

A concrete warning against merging solely by seed appears in the US trace:
boundaries 779 and 780 both have seed **65007** and neutral input. The upper
cog's target is zero in both, but its incoming speed is respectively 100 and
50, so only the latter passes this filter. Other state, including global timer
and cog yaw, differs. Fixed seed and input therefore do not mean fixed complete
state. The log contains 11,625 distinct global timers but only 11,550 distinct
seed values. This is a trace fact, not a proof of independent future schedules.

At the old two-job sweep rate, **26 complete preparation pairs would cost
about 2.08 hours** of seed enumeration (3,407,872 US/JP seed cases). Expanding
to **196 pairs would project to about 15.70 hours** (25,690,112 cases).
The 196-boundary count is US only: corresponding JP phases have not been
captured or validated beyond boundary 844, so the second figure is a proposed
family-size calculation, not a completed two-version inventory.

Neither count is currently a list of valid in-spot preparations. Mario remains
on the ledge, the new pause angles have not been filtered for valid geometry,
and complete checkpoints were captured only at 836-838. The other boundaries
need recapture, geometry and action checks; entering the spot changes Mario
and potentially other objects. Only each boundary's observed seed has known
provenance along this test replay. Alternative seeds with that non-seed state
remain hypothetical until reachability is established. These costs are absent
from the sweep projection, and longer successful prefixes may take much more
time than the prior two-cog failures.

## Feasibility conclusion

The literal fully fixed case has one execution. The video's reduced product
gives about `1.61 * 10^150` non-seed combinations under its unproved model;
enumerating that product is impractical at the measured rate. An explicit
26-phase pilot, or a later 196-phase extension, is a much smaller candidate
discovery project with countable coverage. The pilots would not exhaust all
preparations or answer the full gameplay question if they fail.

To count a complete search, we still need the actual preservation predicate,
a complete preparation domain (or a bounded entry-history family) and a
validated state reduction or reachability enumeration. One fully checked,
reachable preserving witness would suffice for the positive claim; it does
not require exhausting that domain. The required number of trials before
finding such a witness is not known. The preserving 1,200-update RANDOM
target remains open.

Published in owner-only [site version 10](https://pedro-proof-notes.tra38.chatgpt.site/#preparation-count).
The [publication record](ttc-cog-site-publication.md) identifies the exact source
and access check; the guide and site retain the same coverage limits.
