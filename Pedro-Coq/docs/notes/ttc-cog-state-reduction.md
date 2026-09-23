# Which state reductions actually work?

Investigated 2026-09-23 for `VERSION_US` and `VERSION_JP`, source pin
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. **Useful local reductions work,
but preserving RNG scheduling alone does not preserve a Pedro spot.**
This update implements and exhaustively checks two families of local
scheduling reductions. It does not establish a full-game state reduction,
a reachable preparation count or the 1,200-update RANDOM target.

The [checker](../../instrumentation/ttc-cog-state-reduction/README.md) evaluates
the mechanically generated bodies in
[US](../../generated/us_obj_behaviors_2.v) and
[JP](../../generated/jp_obj_behaviors_2.v), including their actual approach
helper and the generated `random_sign` from `behavior_script`. Every tested
output is independently compared with unchanged pinned C in an isolated host
harness. The [receipt](ttc-cog-state-reduction-results.json) records hashes,
counts, partition checks and counterexamples. **This is finite host evidence,
not a Coq execution proof.** The capstone is unchanged and no premise has been
discharged. The discipline audit and the Pedro capstone's `Print Assumptions`
pass; that hygiene does not upgrade these checks into a formal result.

## What the equivalence observes

We observe how many RNG words a native object invocation consumes, in order,
and the reduced state after that invocation. Two concrete states can merge
only if, for each RNG input class, they consume the same number of words and
their successors also merge. The finite check verifies closure and this
condition on every row. Repeated application then preserves the local draw
schedule for arbitrarily many invocations within this transition contract;
this is stronger than just comparing a short sampled trace.

For composition with a shared RNG, the initial seed, invocation order,
enable/skip decisions and any intervening external draws must agree. Equal
draw counts then keep the seed streams aligned by induction. The dropped
fields must not change other objects, Mario, collision, activation or later
invocation order. **That whole-game noninterference obligation is not proved.**
The local test assumes valid object memory and defined angle arithmetic;
angles start at zero for each checked native call.

## Spinner: a countdown replaces timer history and direction

Write `T` for `oTTCChangeDirTimer` and `t` for the timer at native entry.
The generated RANDOM branch draws only when `t > T`. It then selects a new
direction and `T` in `{30,60,90,120}`, and sets the timer to zero.
Our boundary contract performs exactly one generic timer increment after
the native body, with stable action and no other reset or write. This models
the relevant boundary explicitly; it is not execution of the full
`cur_obj_update` command loop.

The reduced key is `q = max(0, T - t + 1)`:

- `q = 0`: draw twice now; the new key is the newly chosen threshold.
- `q > 0`: draw nothing; decrement `q` by one.

Direction affects platform motion but not this draw schedule. The finite
domains make the count and its boundary dependence explicit:

| Local spinner domain at native entry | Concrete states | Scheduling classes |
| --- | ---: | ---: |
| `T` in `{30,60,90,120}`, `1 <= t <= T+1`, direction `+/-1` | 608 | **121** |
| `T` additionally may be `0`, `0 <= t <= T+1`, direction additionally may be `0` | 930 | **122** |

The first is a closed recurrent domain under the stated update boundary.
Its 608 states are `2 * (31 + 61 + 91 + 121)`. The video already lists 121
spinner states, so this validates a local interpretation of that count;
it is not another factor to divide out of the video's product.

The broader checked domain includes the all-zero native initialization
fields and timer-zero boundaries. It adds countdown 121 (`t=0,T=120`).
The 121-state claim therefore must not silently include every startup or
timer-reset boundary. Neither enumeration proves normal-gameplay reachability
of every member or coverage of arbitrary timers, thresholds, action resets,
deactivation or skipped behavior calls. Those are separate boundary proofs.

## Cog: retain signed target and time until the next draw

For this local domain, cog speed is a multiple of 50 in `[-1200,1200]`, and
target is a multiple of 200 in that interval. There are `49 * 13 = 637`
numeric speed/target pairs for a fixed object direction. The check also covers
both object directions and both binary32 representations of zero. The
generated approach helper moves speed by 50 toward the target, clamps when
it reaches it, and then the native body draws a new target.

A sufficient RNG-scheduling key is:

```text
(signed target, max(1, abs(target - speed) / 50))
```

The second component counts invocations inclusively: a speed already at
target, or one step away, draws on the current invocation. There are **480**
keys. For target zero there are 24 countdowns; the positive and negative
targets of magnitude 200,400,...,1200 each have 28,32,...,48:

```text
24 + 2 * (28 + 32 + 36 + 40 + 44 + 48) = 480.
```

Until the next draw only that countdown matters. On the draw invocation,
the old signed target becomes the actual speed and the new target comes
from the two RNG words, so both parts of the successor key are determined.
The sign of zero may be merged for this observation, but positive and
negative nonzero targets cannot generally be merged with identical RNG input.

**Concrete counterexample:** start A at speed/target `(+200,+200)` and B at
`(-200,-200)`, with the same seed **38** and fixed cog direction `+1`.
Both have the same absolute target and distance to target. The generated RNG
produces `62273,49388,38542,42998` as its next four words.

| Invocation | A | B |
| --- | --- | --- |
| First | Draws twice; speed `+200`, new target `+200`, seed `49388` | Draws twice; speed `-200`, new target `+200`, seed `49388` |
| Second | Draws twice; speed `+200`, new target `0`, seed `42998` | Draws nothing; speed `-150`, target `+200`, seed `49388` |

The video table's 259-state cog entry mentions absolute-value symmetry. The
table does not specify its complete simulator or equivalence rule; this
counterexample does not establish what that simulator did. It does rule out
using the natural absolute-target/distance merge as an exact deterministic
reduction with unchanged future RNG words. A symmetry argument that changes
future sign choices would need an additional coupling to the real shared RNG.
These two scalar starts are local counterexamples, not two certified reachable
complete TTC preparations.

## Exhaustiveness and minimality within the stated local domains

Per version the checker covers **27,040** local state/outcome cases, including
the expanded spinner domain, both cog directions and signed-zero variants.
It also checks every 16-bit word as a cog magnitude input, a sign input and
a spinner timer input: **196,608** selector cases per version. Across US/JP
there are **447,296** generated-AST/native-C output comparisons, with zero
mismatches. Generated function bodies agree between versions after normalizing
anonymous-union identifiers.

The checker verifies that the raw RNG temporaries have only the generated
modulo/sign uses. Thus all word pairs factor through 14 cog or 8 spinner
outcome classes; it checks every such pair in every local state. The test
does not claim to enumerate all `2^32` raw word pairs at every state.

A separate partition-refinement pass starts with all domain states together
and repeatedly splits classes whose draw counts or labelled successor classes
differ. It reaches exactly the proposed **480**, **121** and **122** classes.
They are therefore minimal for this finite table's observation and arbitrary
input-class sequences. This is not a lower bound for the real seed-aware
game: the arbitrary input alphabet permits sequences the shared RNG may
never supply, and only a subset of the scalar states may be reachable.

## Why this does not yet reduce the full Pedro search

There are explicit counterexamples to treating these keys as physical state:

- Cogs at `(speed,target)=(100,200)` and `(300,200)` have the same key
  `(200,2)`. Both draw nothing, but their next yaw increments are **150** and
  **250** for direction `+1`.
- Spinners at `t=6,T=30` with opposite directions have the same countdown
  25. Both draw nothing, but their pitch increments are **-200** and **+200**.

Thus applying a scheduling key to the cog supporting Mario can erase exactly
the motion that decides whether the spot survives. Even another platform's
motion cannot be dropped globally until its effect on collision, object
activation and other RNG consumers has been excluded.

These reductions are usable components of a local scheduler and can support
sound rejection filters after the remaining scheduler paths and composition
contracts are established. They do **not** justify changing the whole-game
seed sweep to restore only these fields, nor multiplying the reduced counts
into a certified preparation census. The other TTC object families, Bob-omb
activation/fuse/held state, particles, camera and reachability remain to be
handled. No new brute-force runtime or global count follows from these checks.

The next integration step is to keep complete geometry/Mario state for the
selected cog interaction, derive activation and invocation order from the
actual command loop, and prove which other objects can use scheduling-only
keys without feeding back into preservation. A kernel-checked version also
needs actual Clight execution/refinement for this finite transition table.
No new Coq lemma has been added merely to repackage the host result.
