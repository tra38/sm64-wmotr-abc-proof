# Negative depth: landing timer history

One possible shortcut is now excluded: **leaving the ground cannot simply
carry the old landing timer into the final depth calculation.** The actual
action change resets the original Mario record's timer to zero. The following
dust update keeps it zero. If the final calculation nevertheless makes depth
negative for the first time, the timer must have changed during the later
animation or landing-sound call. No such change has been demonstrated; proving
those two calls preserve the timer is the next small closure task. This does
not yet exclude every landing branch or prove that a physical A press is
universally necessary.

The landing-duration bound is now attached to the real US/JP Clight gate,
not just the stock descriptor census. The new files are
[`InkLandingHistorySource.v`](../../proofs/InkLandingHistorySource.v),
[`InkLandingHistoryGate.v`](../../proofs/InkLandingHistoryGate.v),
[`InkLandingHistoryReturn.v`](../../proofs/InkLandingHistoryReturn.v), and
[`InkLandingHistory.v`](../../proofs/InkLandingHistory.v).

## What this connects

`ilh_actual_increment_stores_compared_timer` follows the actual timer read,
addition, conversion to unsigned 16 bits, and store. The duration comparison
then uses that same converted value, with `LandingAction.numFrames` read from
the actual descriptor allocation. `ilh_actual_duration_gate_bounds_its_stored_timer`
proves that normal continuation leaves the stored timer strictly below the
descriptor's signed frame count. A 16-bit wrap does not bypass the comparison:
the comparison bounds the value actually stored, including a wrapped zero.
No lower bound of one is asserted without a history excluding wrap.

The duration-rejection branch resolves `set_mario_action` to its selected real
body. `ilh_completed_set_action_call_returns_one` proves its completed call
returns one even though its nested calls and stores retain their full actual
memory effects. Consequently a rejected duration gate cannot look like the
zero result which permits the wrapper to continue.

`ilh_actual_gate_to_zero_return_keeps_bounded_timer` covers one continuous
execution of the complete suffix beginning at the duration gate: increment,
descriptor comparison, A-pressed check, off-floor check, and zero return.
It requires both input bits to be clear at that suffix's entry. The timer
store is proved disjoint from the input word; both later input tests therefore
skip their calls, and all memory after the timer store is preserved through
the return. The final timer remains the exact incremented, bounded word.

The ordinary storage premises are explicit: the Mario and landing-descriptor
allocations are different, the Mario field offsets do not wrap, and the
stated timer, input, and descriptor loads succeed. For the stock-duration
corollary, the live descriptor cell must actually contain the stock count
(four or six). This tranche does not independently construct that live value
from initialization and preserve it across the preceding history.

## Leaving the ground: one continuous later interval

[`InkActionTimerReset.v`](../../proofs/InkActionTimerReset.v) proves that every
completed selected US/JP `set_mario_action` call leaves `actionTimer = 0` in
the Mario record originally passed to it, and returns one. Its real
initializer may have effects: the proof does not assume those effects are
harmless. It follows the original argument through them to the final timer
store. There are no local allocations to release after that store.

[`InkLandingDispatch.v`](../../proofs/InkLandingDispatch.v) then starts from a
completed real `common_landing_action` invocation. Its acceleration choice
and `perform_ground_step` retain their actual effects. The reached ground
result and the original Mario argument belong to that same execution, not
separately supplied snapshots. When this result is `GROUND_STEP_LEFT_GROUND`,
the actual switch resolves and calls the real action setter on that argument.

[`InkLandingPostStep.v`](../../proofs/InkLandingPostStep.v) proves the dust
update cannot change the timer: the checked particle field and timer field
are disjoint within the ordinary Mario record. The floor-type tests and
return cannot change memory. If they execute the final depth calculation,
the existing Float32 proof still requires timer four or later for a first
finite negative result from finite nonnegative depth.

[`InkLandingTimerFrontier.v`](../../proofs/InkLandingTimerFrontier.v) connects
these facts in one completed landing call. It retains every actual memory
state and trace between the ground result and return, including the two
remaining calls: `set_mario_animation` and `play_mario_landing_sound_once`.
The timer is derived to be zero on entry to the first. If depth is still
finite and nonnegative after the second, but finite and negative on return,
one of those two calls must have changed the timer reading. This is an exact
remaining effect to check, **not a claim that either call can do so**.

The offset-fit condition for the ordinary Mario record is explicit. Its
identity here is the function's original argument; connecting that argument
to the live game's Mario record is still part of whole-run coverage. A first
negative value created earlier, rather than by this final expression, is
also a separate depth-writer obligation. Other ground results are not covered
by the leave-ground reset branch.

## What is still not connected

This endpoint is the end of `common_landing_cancels`, not the later depth
write. It does not yet establish that every complete cancellation call
reaches this suffix: the steep-floor, sliding and first-person checks precede
it. Nor does it establish all required input and descriptor facts at that
reached point.

The subsequent wrapper and `common_landing_action` execute genuine helpers:
an optional wrapper sound, landing acceleration or slope deceleration,
ground movement, animation, and landing sound. The leave-ground action
change is now checked to install zero regardless of earlier effects, and its
continuation is narrowed to the two named late calls above. For the other
ground results, effects must still be connected in that same run before
identifying the timer read by the depth expression with the bounded
cancellation timer. No generic safe-call premise closes those intervals.

The existing actual depth-write theorem says a finite first negative value
from finite nonnegative depth needs timer at least four. Combining that with
the *same* unchanged stock-duration endpoint would restrict the producer to
long-jump landing at four or five. The unchanged endpoint-to-write connection
remains an obligation, not a theorem obtained by placing two executions next
to one another.

The physical-A argument is also still open. The
[consecutive controller stores](../../proofs/InkControllerRemembered.v)
describe sampled words; a physical press additionally requires ordinary,
non-demo device samples, coherent remembered input at the accepted start,
the correct live controller record, and preservation until Mario consumes
it. Later input processing and all reached long-jump/action transitions must
preserve the relevant provenance. The A-pressed flag being clear at this
landing suffix is a premise, not a newly proved whole-history consequence.
Every reached depth writer, correct live Mario identity, and genuine external
effect must still be classified before claiming universal negative-depth or
zero-physical-A impossibility. A negative value reset before sinking is not
a surviving Ink seed.

## Verification and scope

The focused `check-ink-negative-timer` target builds the integrated
`MainTheorem` and audits twelve theorem assumption reports, including the
new action reset, complete landing-call cut and two-call frontier. These
results strengthen `InkBackwardHistoryCheckedBoundary`; the whole-run
impossibility theorem's three coverage requirements remain open. The full
`check-ink-backward` target also includes these nine new reports alongside
its previous fifty-four. The focused target, not that full sixty-three-report
suite, is the verification run for this tranche. It passed with all twelve
reports and only the existing Coq/CompCert foundations. The separate legacy
discipline audit remains blocked by its missing `sm64-proof` toolchain; it is
not counted as a successful build or assumption audit. The active SSL run
uses `sm64-item-proof`.

All claims concern successful defined in-bounds Clight execution and ordinary
gameplay, including glitches within that model. No method for ACE, arbitrary
memory/code modification or out-of-bounds corruption is developed. Emulator,
operating-system and network vulnerabilities are outside this work.

[Return to the negative-depth approach in the atlas](../no-a-route-atlas.md#route-rank-19)
