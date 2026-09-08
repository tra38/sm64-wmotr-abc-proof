# Rank 9A — Extra Goomba airtime and movement before the star chooses its home

## Result

**No clean installation was found. One stronger candidate is now negative in
the checked vertical projection:** grant the earlier Spindel raising setup,
let the Goomba take one final ordinary hop before the finishing attack, then
start a ground pound in the update that collects the 100th coin. Even with
generous bounds favoring the route, Mario's resulting height is at most 3495;
the existing pole-side star placement needs at least 3505.

This is about installing the star **before crossing the gate**, not the parked
Rank-9 continuation beyond the elevator. The proof does not claim that the
Spindel setup, the coin contact, or a complete controller trajectory exists.
Granting them makes this a stronger negative test. Higher supports, a renewed
airborne jump at a higher position, other position changes, and a genuinely
delayed first star update remain separate possibilities.

## Why the whole ground-pound rise cannot be credited

The relevant ordinary update order is coin contact, Mario's action, Mario's
position copy, then the newly spawned LEVEL-list star. That star chooses its
home from Mario's **current raw Object position**, not from a future apex.
Its script reaches the first native loop without an intervening delay; the
`BEGIN_LOOP` command continues interpretation rather than yielding a frame.
In the ordinary unfrozen schedule, Mario therefore gets the current action
update before the home sample, not all ten startup lifts. Starting ground
pound on this update supplies 20 units, not its eventual 110 units. If startup
was already underway, its individual lift is smaller; failed headroom adds
nothing. Movement after the home sample does not relocate that home.

The new generated US/JP receipts check the exact star script, list-update
order, and action-before-position-copy call order. They are **not** a complete
execution proof of the live scheduler. Reaching the new star in the intact
list, its normal dispatch, the raw-Object/State relationship and outside-call
effects still need their live evidence. An already active selective time stop
is not ruled out by a script with no delay command: a proposed delay must show
both why the star waits and why Mario can still make useful movement.

## The stronger producer and its bound

The older flight audit treated 2517 as a generous ceiling at the finishing
attack. This test instead allows another ordinary hop **before** that attack.
The generated `goomba_begin_jump` computes `50.0f / 3.0f * scale`; the regular
initialized scale 1.5 gives exactly Float32 velocity 25. One isolated hop rises
66 at these integer heights. The proof deliberately permits velocity up to 28
and therefore an 84-unit envelope, so it does not depend on the exact apex or
translation-invariant rounding.

| Stage | Conservative Coq ceiling |
| --- | ---: |
| Granted final raising-station position | 2517 |
| After the extra released-hop episode | 2601 |
| After the finishing attack | 2913 |
| Coin spawn, granting a favorable floor up to 78 higher | 2991 |
| Coin flight | 3411 |
| Mario's base at ordinary coin contact | 3475 |
| One subsequent ground-pound startup lift | 3495 |
| Required home-sampling position for the checked pole-side catch | at least 3505 |

The attack bound allows upward speed 52 rather than the real maximum 50 and
grants the full apex even when the death timer could stop it sooner. Coin
launches cover every ordinary random result, with the endpoint 1 also granted.
The existing Float32 induction permits arbitrarily many pauses and checked
resets on supports no higher than that episode's starting ceiling. A reset
onto a higher support or a renewed airborne jump is **not** one of those cases.
The loot-floor allowance and non-water movement remain explicit premises.

The bound does not assume that all these favorable maxima can coexist in one
run. Even their over-approximation misses. Conversely, this does not impose
the particular 3505 threshold on every possible Rank-9A wall or star placement;
it belongs to the already checked pole-side candidate.

## Numerical cross-check

The diagnostic reads the generated US/JP data and tests all 65,536 coin-launch
return words for each of 125 distinct granted coin seeds. It considers 126
attack cases: both ordinary finishing-attack velocities, release movement
counts 0 through 20, and three starting heights. It favorably counts even
intangible coin heights and ignores horizontal/controller restrictions.

| Granted start | Best attack height after the hop | Highest post-contact first lift | Shortfall to 3505 |
| --- | ---: | ---: | ---: |
| Low-tier floor, 640 | 706 | 1575.998291015625 | 1929.001708984375 |
| Lower Grindel top, 1145 | 1211 | 2080.998291015625 | 1424.001708984375 |
| Conditional Spindel station, 2517 | 2583 | 3452.99658203125 | 52.00341796875 |

The sharper diagnostic and looser Coq ceiling are compatible: the proof grants
extra hop and attack height. A deliberately **incorrect** timing control adds
all future startup lifts and reaches 3542.99658203125. That apparent success is
why the home-sampling instant matters; it is not a route witness. The finite
diagnostic is not an exhaustive controller or live-surface search.

## What the proof executes

[`Area2Rank9APreHomeMovement.v`](../../proofs/Area2Rank9APreHomeMovement.v)
connects the existing Float32 flight envelopes across the released hop,
finishing attack and normal coin launch. It proves the contact ceiling, then
executes the actual selected US/JP ground-pound post-headroom Y load/store
and derives that its stored result is below 3505. It also bounds the actual
home-height addition to 3745 and reuses Rank 9's selected-Clight home-Y
execution theorem. A blocked lift already stays below the contact ceiling.

This is **not one uninterrupted game execution**. In particular, the
ground-pound memory theorem requires its incoming MarioState Y to obey the
coin-contact bound. It does not assume away an intervening platform move,
ledge snap, pole correction, raw-Object/State mismatch or other position
writer. The copy into the raw Mario object and the first star dispatch remain
to be connected. No new claim is made about delayed initialization, horizontal
placement, tangibility timing, contact-list capacity, or the target suffix.

The strengthened `current_rank9a_coin_star_gate_boundary` in Main consumes
this package. The ultimate theorem still has its lower/upper reachability and
whole-frame refinement premises; this tranche closes a named projected
candidate, not those global obligations. No game memory or executable was
modified, and no controller movie was generated.

## What to investigate next

Do not repeat a normal final hop plus the same-update ground-pound lift, or
search merely for a better coin-toss random value. A surviving setup must
provide a concrete additional event: a higher reachable support for the
enemy or coin, another earned airborne jump, an actual position change outside
the one-lift case, or a delay in first star initialization during which Mario
really moves far enough. Each must have the right X/Z and occur before the
home sample. An ordinary pole climb or the full handstand elevation cannot
simply be added as a single-update gain.

Keep the reward history explicit: the known lower itinerary already uses the
100-coin star at the big steps. A new attempt must reach the gate with the
needed coin count and without spending that same star earlier, or demonstrate
a separate legitimate resource history. Nothing here supplies that missing
climb. The upper-elevator placement is also a separate geometric target.

## Reproduction

From the repository root:

```sh
SM64_PROOF_SWITCH=sm64-item-proof bash pipeline/build.sh \
  -C SSL-Coq/less-than-one-a-press check-rank9a-prehome
```

From the SSL project:

```sh
node instrumentation/rank9a-coin-producers/check_prehome.js
node instrumentation/rank9a-coin-producers/check_flight.js
```

The source authority is pinned revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, through the generated US/JP files.
The older root discipline audit still fails its legacy build because the
`sm64-proof` switch is absent; the active SSL checks use `sm64-item-proof`.

Validation on 2026-09-07: the focused leaf compilation and integrated
`check-rank9a-prehome` target passed, including all six assumption audits,
the no-holes check and link hygiene. The new pre-home diagnostic and the
existing coin-flight and producer diagnostics passed. No project-local axiom
was added; the integrated boundary retains the documented CompCert external
semantics and the ultimate theorem's explicit reachability/refinement premises.
Atlas anchors, local note links and patch whitespace were also checked.

[Back to Rank 9A](../no-a-route-atlas.md#route-rank-9a)
