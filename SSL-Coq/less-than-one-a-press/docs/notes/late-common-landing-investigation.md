# Can the late landing happen without A?

Late long-jump landing is real. A controller-only JP control reaches timers 4 and 5, including on quicksand, after one deliberate A press. No no-A path was found. The ordinary source chain points back to that A press, but the complete all-game no-A exclusion is still conditional. This investigation does not grant a long-jump state or a negative seed.

## The backward chain

The final write in `common_landing_action` uses the timer **after** acceleration, the ground step, the ground-result switch, animation and sound. It runs only when the current floor type passes the quicksand guard. Timer 4 subtracts 0.5 and timer 5 subtracts 4. A subtracting write is not necessarily a negative result, and a timer observed when the action started is not necessarily the timer at this write.

The generated US/JP caller census checks exactly these nine direct callers across the selected 38-unit source corpus. Each passes its own named descriptor to `common_landing_cancels` and returns immediately when that call reports cancellation.

| Caller | Stock duration | Values admitted by the duration gate | Extra wrapper checks |
| --- | --- | --- | --- |
| `act_jump_land` | 4 | Below 4 | None before cancellation. |
| `act_freefall_land` | 4 | Below 4 | None before cancellation. |
| `act_side_flip_land` | 4 | Below 4 | Adjusts display yaw after the landing call. |
| `act_hold_jump_land` | 4 | Below 4 | May drop the held object and leave first. |
| `act_hold_freefall_land` | 4 | Below 4 | May drop the held object and leave first. |
| `act_long_jump_land` | 6 | Below 6 | Can clear the A input bit; may request a sound before the landing call. |
| `act_double_jump_land` | 4 | Below 4 | Uses the triple-jump callback for its A branch. |
| `act_triple_jump_land` | 4 | Below 4 | Clears the A input bit; may request a sound. |
| `act_backflip_land` | 4 | Below 4 | Can clear the A input bit; may request a sound. |

With the ordinary zero-timer entry, these windows are 1–3 and 1–5. The existing gate proof also handles the unsigned increment itself; wrapping a large timer to zero does not create a late negative adjustment. The table describes the value at that gate. Carrying its bound to the later depth write is a separate execution connection.

The existing generated-source inventory identifies `act_long_jump` as the only expression site supplying `ACT_LONG_JUMP_LAND` to `common_air_action_step`. That helper installs the supplied landing action after landing, unless the damage/stuck check overrides it. The direct first `ACT_LONG_JUMP` constructor is the crouch-slide A-pressed branch, with speed greater than 10 and its timer window open. The long-jump landing descriptor can request another long jump through an A-pressed callback, but this already requires being in long-jump landing. It does not explain the first one.

The action-setting initializers were also reviewed. Airborne initialization can replace double jump or twirling with ordinary jump; moving initialization selects butt/stomach slides; submerged and cutscene initialization retain the supplied action. They provide no newly identified conversion into the long-jump cycle. The existing completed `set_mario_action` proof resets the original action timer after its initializer. Re-entering a landing through that setter therefore does not retain the old late timer. Extra time in the air is not extra time in the landing action.

## The new proof connection

[InkLandingCallerSource.v](../../proofs/InkLandingCallerSource.v) checks all nine direct caller names, their exact guard/descriptor/callback structure, and their resolution in the actual selected US/JP programs. [InkLandingCallerGate.v](../../proofs/InkLandingCallerGate.v) follows each complete wrapper invocation: it either stops in its earlier checks, stops at the cancellation guard, or continues after the real internal `common_landing_cancels` call returned zero. That callee's actual argument evaluation, trace and memory effects are retained, together with the rest of the wrapper. No stock timer bound, harmless-helper premise or no-A action-history assumption is used to establish this caller connection.

The next connection is now checked too. [InkLandingCancellationCaller.v](../../proofs/InkLandingCancellationCaller.v) follows the stock guard through its actual Mario pointer, named descriptor address and jump callback. [InkLandingCancellationGate.v](../../proofs/InkLandingCancellationGate.v) follows the completed real cancellation call returning zero through the duration gate and back to the caller. [InkLandingDurationRead.v](../../proofs/InkLandingDurationRead.v) extracts the integer timer from the executed increment and the duration from the actual signed-16 read. The returned memory contains that incremented timer, strictly below the duration it read. The later A/off-floor checks leave memory unchanged on this successful path. No supplied timer, supplied descriptor value, clear-input-mask premise or harmless-helper assumption is used for this connection. The steep-floor and two jump helpers are resolved and proved to return one on completed calls, with their full memory effects retained.

This is a bound against the live duration, not yet a proof that the duration still equals its stock four or six. Those descriptor globals are writable in the generated program. Their initial values are checked, but preserving those values up to every reached read still needs proof. The nine-wrapper census also does not cover every indirect dispatch or every execution history.

## Controller controls

The [reproducible Wafel controls](../../instrumentation/late-common-landing/README.md) replay the previously checked JP prefix and branch at twelve reached walking states. Each branch lasts 90 updates. One choice uses Z without A; the other uses Z first and one A press on the next update. Walking checks A before Z, so simply pressing them together is not the same control sequence.

Six of the twelve one-A choices reach long-jump landing timers 4 and 5. At the quicksand control starting at poll 907, the recorded depths at those timers are about 21.10 and 17.35: positive. None of the twelve no-A choices records a late timer in any of the nine common-landing actions. None of the 24 choices records negative depth at an update boundary. These are finite after-update observations, not an instruction-level write trace or a universal exclusion. They establish neither an unseen transient's absence nor a no-A seed.

## What remains, exactly

The stopping rule is the user's necessary-condition chain: a useful negative seed requires the late landing write, and that write requires an earlier physical A press. Once both links are proved for the allowed executions, this producer is insufficient for gameplay with A never pressed. We do not also need to find the most negative A-using landing, show that every late landing is negative, or follow a seed into the later Ink route. The whole negative-depth family additionally needs the completed-writer coverage already stated in the conditional seed theorem; the chain must concern a usable negative value, not a temporary value erased by a clamp.

The complete cancellation call and its actual duration read are now connected. Three substantive obligations remain before the no-A producer can be closed:

1. Preserve the stock descriptor values up to the real read: four for eight landing kinds, six for long-jump landing. The new theorem derives a bound against what was read; it does not silently replace that value with an initializer.
2. Carry the returned bound through the wrapper's optional sound and the landing body's acceleration, movement, animation and sound to the depth write. Existing post-ground proofs cover reset on leaving the floor and bounded preservation under explicit storage and call conditions. In particular, `InkAnimationTransferTimerEffect` and `InkAudioRequestTimerEffect` remain premises. The selected C model leaves `play_sound` and the low-level DMA/message operations external; a matching prototype does not prove their writable-memory effects.
3. Refine every reached action write and controller update into the existing first-long-jump and physical-A argument. The source census and first-occurrence induction do not themselves establish that coverage.

These are missing proof connections, not observed ways for ordinary gameplay to forge a timer or an action. No new no-A constructor was found. This batch completes the cancellation/read connection, but does not complete all the remaining connections requested by the user. It adds no axiom or blanket preservation assumption to hide them.

The source review found no separate landing mechanism in another course. TTM and THI use the same action code for their shallow quicksand. Any useful negative depth made elsewhere would additionally face the proved initialization reset on ordinary course entry. This pass did not search controller histories in those courses and did not reopen initialization or the later Ink route.

The verdict remains: late landing is possible with A; no ordinary no-A witness found; the checked caller/cancellation obstruction and existing conditional seed-to-A theorem do not yet give an unconditional all-game no-A proof. The atlas's below-1% complete-route estimate is unchanged and is not a probability inferred from these controls.

## Validation

Selected audit `build/audit/20260925-173000-nw3s079t` passed on 25 September 2026 with the established memory cap: 604 registered sources, successful compilation, proof-hole and source-link checks, and 434 of 528 proof modules in the main import closure with 94 standalone modules. The main backward boundary uses nine allowed foundations; the stock-guard, completed-cancellation and live-duration theorems use seven each; the existing conditional seed theorem uses seven. No project axiom was added. The new results are connected through `InkBackwardHistory.v` to `MainTheorem.current_ink_backward_execution_boundary`.

The earlier Wafel receipt was reproduced exactly. All 24 written full controller schedules match their recorded SHA256 hashes, and a separate count confirms zero physical A edges in each no-A schedule and exactly one in each one-A schedule. Those branches were not independently replayed in the emulator; the cancellation follow-up adds no new runtime trials. The selected proof audit and finite controls do not close the remaining gameplay premises.
