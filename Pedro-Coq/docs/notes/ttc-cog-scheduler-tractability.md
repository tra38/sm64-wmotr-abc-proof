# What can be guaranteed about a TTC schedule search?

Investigated 2026-09-22. Game scope: `VERSION_US` and `VERSION_JP`, pinned
source `9921382a68bb0c865e5e45eb594d9c64db59b1af` and its generated Clight.

**A restricted search has an explicit operation bound. A general search over
preparations has no established practical or polynomial-time guarantee.**
The earlier [video review](ttc-cog-video-rng-sequence.md) correctly withheld a
guarantee for the proposed constraint solver, but its wording can be sharpened:
seed-dependent schedules do not themselves cause exponential branching when
the seed is the only unknown. Each complete initial state and fixed input
continuation determines one execution.

This is a source-grounded algorithmic analysis, not a new Coq theorem, an
implemented full-game scheduler, a runtime benchmark or a successful gameplay
witness. The preserving 1,200-update RANDOM target remains open.

## The useful bound: only the seed varies

Fix one version, every non-RNG component of the initial state, and a complete
1,200-update input sequence (or a fixed deterministic policy). Fix any external
inputs used by the execution model too. This means object timers, actions,
positions, allocation/list state, Mario, camera and globals, not just a cog
angle and Mario's position. Let:

- `R = 65,536`, covering every 16-bit initial seed, including transients;
- `H = 1,200`, the number of complete game updates to check;
- `C`, a bound on evaluating one faithful update and its preservation predicate;
- `I`, a bound on constructing one candidate's initial state.

Enumerate the seeds. For each, run its own actual object continuation, stopping
at the first failed preservation condition. There are at most `R * H` frame
evaluations, and the time bound is `O(R * (I + H*C))`. The arithmetic is:

```text
65,536 * 1,200 = 78,643,200 frame evaluations for one version and one setup
2 * 78,643,200 = 157,286,400 if US and JP are checked separately
```

No `7^1200` or branching over future random draws appears in this bound. Those
draws, and the timers they change, are determined by the initial seed. This
does not reuse one seed's draw schedule for another. It also does not assert
that all seed/snapshot combinations are reachable by gameplay. A survivor is
only a candidate until entry, preservation and reachability are established.

The bound is conditional on a terminating, faithful update evaluator. No
validated worst-case `C` or elapsed-time bound for that evaluator is available
here. The existing replay observer is not such a seed-sweep implementation.
A frame-count bound is not an instruction-count or wall-clock guarantee.
An execution-fuel cutoff can bound runtime, but an exhausted case must be
reported as **unknown**, not as a rejected seed, unless the fuel bound has
been proved sufficient. Initialization cost also cannot be omitted from a
wall-clock estimate.

This is a bound an enumerating solver can enforce. An arbitrary SAT solver
does not automatically inherit it; it would need the concrete enumeration as
its algorithm or as a fallback with a guaranteed share of execution time.

## What changes when more choices are allowed?

| Search family | Complete enumeration bound, excluding setup cost | Qualification |
| --- | --- | --- |
| One fixed non-RNG state, fixed inputs | `R * H * C` | Each seed gets its own schedule. |
| `K` explicitly listed non-RNG states, fixed inputs | `K * R * H * C` | Completeness is only for the supplied list. |
| Another `b` freely chosen initial bits, fixed inputs | `2^(16+b) * H * C` | Many assignments may be invalid or unreachable. |
| `A` possible inputs at each of `H` updates | At most `K * R * A^H * H * C` by enumerating sequences | A safe loose bound; sharing prefixes can reduce repeated work. |

The seed-only case is linear in the horizon. With a polynomial-cost transition
evaluator, enumeration is fixed-parameter tractable in the number of free
initial bits. That classification is not
helpful if hundreds of independent preparation bits remain free. Adding a
bounded entry history also adds its input choices and simulation cost.

Dynamic programming can instead retain at most `Q` distinct complete states
at each depth, costing `O(H * Q * A * C)` with state-key operations included
in `C`. A verified equivalent-state projection could reduce `Q`. But the
generic bound is `Q <= 2^B` for `B` state bits; calling the machine finite
does not make that number small. For a time-dependent fixed replay, the depth
or replay position must also be part of any cross-depth equivalence check.

## Source checks: why timers and update order matter

The following generated bodies were compared between US and JP. They agree
after normalizing only generated anonymous-union identifiers:

- [`f_bhv_ttc_cog_update`](../../generated/us_obj_behaviors_2.v): future call
  times depend on current speed and the previously selected target, through
  `approach_f32_ptr`. The zero-target case selects again every update.
- [`f_bhv_ttc_spinner_update` and `f_random_mod_offset`](../../generated/us_obj_behaviors_2.v):
  in RANDOM mode, the spinner draws when `oTimer > oTTCChangeDirTimer`, chooses
  a sign and a new threshold, and resets the timer. The threshold is itself
  chosen by `random_mod_offset(30, 30, 4)`.
- [`f_update_objects_starting_at`](../../generated/us_object_list_processor.v):
  objects are visited in linked-list order and each `cur_obj_update` completes
  before advancing to the next object. Calls to the shared RNG are ordered.
- [`f_cur_obj_update`](../../generated/us_behavior_script.v):
  behavior commands execute in a loop until a command yields; timer and
  distance-related processing are part of the update. A frame bound alone
  does not supply this loop's instruction bound.

For a concrete distinction, at entry to the RANDOM spinner body, threshold
30 and timer 31 take the random-selection branch; the same threshold and
timer 30 do not. Equal RNG seeds therefore do not justify merging those two
states. This is a branch-level source example, not a claim that both states
are reachable at the desired cog entry.

The generated object pool has capacity 240 (`v_gObjectPool` in the object-list
unit). That bounds storage, not the number of possible combinations of object
fields, list contents, behaviors and external state. It is not evidence that
there are exactly 240 RNG events per frame or that frame execution is bounded
by 240 constant-cost operations. The existing actual cog trace also has
different intervening draw counts on different frames; see the
[RANDOM schedule receipt](ttc-cog-random-1200.md).

Shared RNG consumption prevents treating object choices as independent. It
does **not**, on its own, prove that the constraint graph has large treewidth
or that this specific game instance is computationally hard.

## What SAT/SMT does and does not guarantee

A finite, fully bounded bit-level transition encoding can be decided by
exhaustive search. Bounded model checking encodes the initial condition,
successive transitions and the desired property as a satisfiability query;
the encoding can be polynomial in the explicit transition description and
horizon. This is an encoding-size result, not a polynomial solving-time
result. See [Biere, Cimatti, Clarke and Zhu (1999)](https://fmv.jku.at/papers/BiereCimattiClarkeZhu-TACAS99.pdf).

For general Boolean transition systems, even a one-step existential query
can encode SAT: allow initial Boolean values to vary, compute an arbitrary
formula on them in that step, and require its result to be true. Verifying a
supplied path is polynomial in the explicitly unrolled circuit, so this
general bounded decision problem is NP-complete. A universal polynomial
solver for that class would imply `P = NP`; see
[Cook's original complexity result](https://www.cs.cmu.edu/~15455/resources/Cook1971-complx-thm-proof.pdf).
This argument does **not** prove NP-hardness for SM64, for the actual TTC
transition family, or for the one fixed 1,200-frame query. No such reduction
has been established here. Fixed hardware and a fixed horizon are one finite
instance; a complexity classification must say which parameters can grow.

There are useful structural guarantees. For a constraint graph with a supplied
tree decomposition of small width `w` and domains of size at most `d`, table
dynamic programming has a bound of the form `poly(n) * d^(w+1)`. For fixed
width and domain size this is polynomial. Freuder's original k-tree result
gives `O(n*d^(k+1))` for its stated class:
[Complexity of K-Tree Structured Constraint Satisfaction Problems (1990)](https://www.aiinternational.org/Papers/AAAI/1990/AAAI90-001.pdf).
We have no proved small-width decomposition of a faithful TTC encoding.
Putting the entire frame state in one variable makes a chain-shaped graph,
but gives that variable a domain as large as `2^B`; it hides the same cost.

Event-driven execution can accelerate a known trajectory by skipping periods
whose effects are proved predictable. It is not a bound on how many different
initial states must be considered. Prefix pruning and learned constraints
may be effective, but the rough one-in-seven probability does not guarantee
that a fixed fraction of candidates disappears at each step. Merging requires
equal relevant future behavior, not merely equal seeds or cog targets.

## Concrete consequence for this project

The next solver should first fix a small explicit family of complete initial
states and deterministic continuations. Establish a faithful frame evaluator
(including all RNG consumers and relevant external inputs), then enumerate
seeds with actual per-seed scheduling and early rejection. This has a clear
coverage count and does not need a symbolic solver to obtain its seed bound.
Measure throughput and record any unknown executions before projecting time
for larger families. Broaden preparation domains only with an explicit count
or a verified state reduction; small-width constraints are a possibility to
investigate, not an established property of TTC.

Rejection must follow the requested whole-update predicate. In particular, a
new nonzero cog target need not move the cog until the next update; rejecting
the last selection of a window would silently strengthen the goal. Likewise,
a cog-only schedule success does not establish Mario's complete preservation.

**Outcome:** a conditional seed-sweep operation bound is justified; no practical
bound for the unrestricted preparation search, and no complete scheduler
implementation, is supplied. No game or emulator state was changed. The
repository discipline audit passed in Ubuntu's configured login environment
with `SM64_PROOF_SWITCH=sm64-item-proof`; no proof statements or assumptions
were changed, and no capstone obligation was discharged.

Published in owner-only [site version 5](https://pedro-proof-notes.tra38.chatgpt.site/#scheduler-tractability);
the [publication record](ttc-cog-site-publication.md) identifies the exact
source snapshots and private-access check.
