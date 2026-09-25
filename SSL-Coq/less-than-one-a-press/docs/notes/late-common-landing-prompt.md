# Can no-A gameplay reach the late common-landing write?

The [first investigation pass](late-common-landing-investigation.md) has now been carried out. It adds an actual caller connection and finite controller controls, while the complete no-A exclusion remains open. Reaching a late timer, subtracting from depth, and leaving a useful negative seed are separate claims. The original prompt is retained below.

## Prompt

Determine whether ordinary gameplay can reach the late quicksand-depth write in `common_landing_action` without ever pressing physical A. Start from the project's accepted normally initialized state with nonnegative depth. Do not grant a negative seed, a long-jump action, a late timer, or an unexplained saved state.

Work from the pinned C and actual generated US/JP Clight. Reuse the existing writer census, landing-gate/timer proofs, first-long-jump argument, `InkStockSeedConditional.v` and `InkJumpClamp.v`. Do not repeat their arithmetic as new progress.

1. **Define the event precisely.** The target is executing the final quicksand-depth write with a timer that makes its adjustment negative, on a floor that passes the actual quicksand-type guard. Under the already checked stock landing conditions, the candidates are long-jump landing at timer 4 or 5. These are timers at the write, after preceding calls, not time spent falling. Briefly establish what the source permits when A is allowed, so that we do not confuse an ordinary late landing with a no-A route.

2. **Work backward from that write.** Identify every stock caller and the actual ways to enter its action. Follow the cancellation gate, timer increment, ground-step result and intervening action changes. Check re-entry and whether timers reset or survive. Determine whether a no-A action transition can reach the late write; do not assume that every reached execution satisfies the conditional theorem's stock gates or legitimate-entry premises. Name the first missing connection and resolve one concrete connection before widening the search.

3. **If a no-A late write survives, check whether it makes a seed.** Track the real incoming depth, including earlier landing and quicksand updates. Timer 4 subtracts 0.5 and timer 5 subtracts 4; subtracting does not necessarily make the result negative. Check the game's binary32 calculation and any subsequent clamp or reset before another part of gameplay can use the value. A late write with a nonnegative result does not supply the seed.

4. **Separate location from mechanism.** Start with SSL Area 1, and identify any concrete additional opportunities in other stock courses. A seed made elsewhere still needs to survive the already proved course-entry reset to help in SSL. Do not restart the initialization proof or investigate the later Ink warp route before establishing the producer.

5. **Give a scoped verdict.** Report separately whether the late write is source-permitted with A, reachable without A, and capable of leaving a useful no-A negative seed. Supply a legitimate controller trace or a checked obstruction. Wafel may test candidates, but injected states are only conditional tests and a failed finite search is not an impossibility proof. If a conclusion is conditional, list its exact remaining gameplay premises.

Stay within defined, in-bounds gameplay; do not use memory corruption, arbitrary state modification, new axioms, `Admitted`, or an unproved coverage predicate as a closure. Update the atlas, checklist and private Fine Print site with the actual result. Stop at this producer question; do not expand into a complete Ink route.

## Current boundary

The [conditional seed-to-A implication](conditional-stock-negative-seed.md) and early quicksand-jump clamp checkpoint retain their scopes. The new caller proof excludes an unguarded direct-wrapper continuation; its remaining timer/history connections and finite controller results are recorded in the [investigation](late-common-landing-investigation.md). No complete no-A seed exclusion or route estimate change is claimed.
