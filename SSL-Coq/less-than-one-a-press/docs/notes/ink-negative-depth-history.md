# Negative depth: the executed landing-duration endpoint

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

## What is still not connected

This endpoint is the end of `common_landing_cancels`, not the later depth
write. It does not yet establish that every complete cancellation call
reaches this suffix: the steep-floor, sliding and first-person checks precede
it. Nor does it establish all required input and descriptor facts at that
reached point.

The subsequent wrapper and `common_landing_action` execute genuine helpers:
an optional wrapper sound, landing acceleration or slope deceleration,
ground movement, a possible action change after leaving the ground,
animation, and landing sound. Their effects must be connected in that same
run before identifying the timer read by the depth expression with this
bounded timer (or proving any intervening reset only installs zero). No
generic safe-call premise closes that interval here.

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

All claims here concern successful defined in-bounds Clight execution.
Arbitrary memory/code modification and execution after undefined behavior
are not methods supplied by this argument.

[Return to the negative-depth approach in the atlas](../no-a-route-atlas.md#route-rank-19)
