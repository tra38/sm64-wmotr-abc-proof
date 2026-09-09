# Negative depth: landing timer history

The target is a surviving negative seed without a new physical A press, not
negative depth in all gameplay: the ordinary long-jump case is already known.

**Current status: whole-history connection missing; route not closed.**
The [shared closure argument](negative-depth-shared-closure.md) now controls
work selection and reporting for this branch. The local results below are
reusable evidence, not a continuous execution from the accepted boundary.
The next priority is surviving-producer coverage in that execution, not
another independent controller or timer lemma.

One possible shortcut is now excluded: **leaving the ground cannot simply
carry the old landing timer into the final depth calculation.** The actual
action change resets the original Mario record's timer to zero. The following
dust update keeps it zero. If the final calculation nevertheless makes depth
negative for the first time, the timer must have changed during the later
animation or landing-sound call. Their actual game-code writes are now checked:
the sound helpers update flags, and the animation helper updates the object
and animation buffer. With the actual entry destinations separate from
MarioState, only the audio-request and animation-transfer effects still need
timer frames. The additional results below check initialization writes,
eliminate the audio request when its once-only flag is already set, and
eliminate animation-transfer effects when the actual loader returns zero.
They also cover all three choices in the post-ground switch and extend the
final-calculation exclusion to any timer below four. The live history that
delivers these conditions is not yet proved; a physical A press has not been
shown universally necessary.

The landing-duration bound is now attached to the real US/JP Clight gate,
not just the stock descriptor census. The duration-proof files are
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

## Late helper effects and their remaining conditions

### The late helpers are no longer black boxes

[`InkLandingSoundFrame.v`](../../proofs/InkLandingSoundFrame.v) executes the
selected US/JP landing-sound wrapper, action-sound helper, and particle/sound
helper. It resolves their real internal calls and follows the original Mario
argument. Their only ordinary writes are to the flags and particle-flags
words, at offsets 4 and 8, away from the two-byte timer at offset 26. Even the
helper named `play_sound_and_spawn_particles` only sets particle flags here;
it does not allocate a particle object in this call. The remaining sound
premise is the timer effect of the actual final `play_sound` request.

[`InkAnimationTimerFrame.v`](../../proofs/InkAnimationTimerFrame.v) follows
the real animation call's first reads: Mario's object, animation descriptor,
and descriptor's buffer. The remembered object and buffer references remain
the destinations even after the loader returns. Every later scalar animation
write is proved to stay in one of those two blocks. The proof explicitly
requires the three entry blocks (object, descriptor, buffer) to differ from
the protected MarioState block; it does not derive their live provenance.
[`InkAnimationLoaderFrame.v`](../../proofs/InkAnimationLoaderFrame.v) also
executes the real loader: its own bookkeeping write stays in the descriptor
block. The remaining animation premise is the effect of `dma_read` at this
particular callsite, with its destination derived from that buffer read and
proved separate from MarioState. It does not require arbitrary transfers to
arbitrary destinations to preserve the timer.

[`InkLandingLateClosure.v`](../../proofs/InkLandingLateClosure.v) applies
these results to the actual consecutive animation call, landing-sound call,
and final depth calculation. The same memories and original Mario reference
connect all three. Given the earlier derived zero timer, ordinary entry
destinations, and the two named runtime frames, the timer stays zero. A first
finite negative final calculation would require at least four, so that case
is impossible. These are conditional execution theorems, not assumptions
that the entire helpers preserve the timer.

The two remaining effect premises are **not discharged or silently accepted**.
The selected programs leave `play_sound` abstract; ordinary audio source
queues a request, but that source observation is not yet its Clight effect
specification. The animation-transfer wrapper reaches abstract cache,
transfer, and message-service calls. Their ordinary specified effects must
be connected to the protected timer, or the transfer must be shown absent
on the relevant execution. This work does not change a running game's memory
or investigate defects in those services.

### Initialization facts now derived from execution

[`InkAnimationStorageSetup.v`](../../proofs/InkAnimationStorageSetup.v)
proves two actual US/JP initialization results. At the reached animation-list
assignment in `init_mario_from_save_file`, the code reads `gMarioState` and
stores the fixed address of `gMarioAnimsBuf` into that Mario record. If the
read names the real `gMarioStates` allocation, the descriptor is necessarily
in a different CompCert block: the two distinct global symbols cannot name
the same allocation. This is a checked reached assignment, not a proof of
the entire preceding initialization or its later persistence.

The second result covers a **complete** `setup_dma_table_list` call. Whatever
the earlier table-loading call does, the final descriptor-buffer store uses
the original list and buffer arguments. A successful return therefore leaves
`bufTarget` pointing to that exact original buffer. No harmless-effect premise
is needed for the earlier loading call to prove this endpoint. This does not
prove where the original buffer came from, whether the allocator supplied
separate storage, or whether later execution preserves that pointer. Those
are still required for the live animation-entry separation result; the
ordinary object-pool identity must also be carried to that entry.

### Two branches need no outside-call effect

[`InkLandingQuietSound.v`](../../proofs/InkLandingQuietSound.v) proves that
when the actual entry flags already contain the action-sound bit (`0x10000`),
the complete landing-sound wrapper and its real action-sound callee leave
**all memory unchanged** and produce no events. The flag check skips the
particle/sound helper, so no `play_sound` request executes. This removes the
audio-effect premise for that branch; it does not assume the flag is set on
every landing, or rule out the first request. The flag is checked in the
memory reached **after** the animation call, not in an unrelated snapshot.

[`InkAnimationNoTransfer.v`](../../proofs/InkAnimationNoTransfer.v) proves
that a completed real `load_patchable_table` call returning zero also leaves
all memory unchanged and produces no events. This covers its cached-asset
and rejected-index branches. The transfer branch must set the return value
to one after its real call and bookkeeping write, so it cannot inhabit this
zero-return result. The theorem is also connected to the actual loader
callsite and returned temporary inside `set_mario_animation`. A zero result
is not automatically a cache hit or a reachable valid animation: that still
requires the actual table/index history. A transfer that really executes
still needs its precise runtime effect.

### Every post-ground switch outcome

[`InkLandingOutcomeFrames.v`](../../proofs/InkLandingOutcomeFrames.v)
exhausts the actual switch without assuming a particular movement result.
Leaving the ground calls the real action setter and resets the timer. Hitting
a wall performs exactly the real pushing-animation call. Any other returned
value takes an empty branch and cannot change memory. Under the existing
animation storage and transfer conditions, the wall call preserves the
timer. Thus this switch has no fourth, unchecked timer-changing branch.

[`InkLandingBoundedClosure.v`](../../proofs/InkLandingBoundedClosure.v)
carries any timer below four through that switch and the following dust
update. It separately follows the consecutive final animation, sound and
depth-calculation interval: with the checked animation conditions and either
the audio frame or the actual already-played flag, the timer stays below
four, so finite nonnegative depth cannot become finite negative depth in
the final calculation. Unlike the earlier result, this is not limited to
timer zero. It still needs the earlier movement interval to deliver that
small timer, live storage conditions at each animation entry, and
nonnegative depth immediately before the final calculation. It is not a
proof that earlier helpers cannot create negative depth.

### What the controller/action history would buy us

This history would close the ordinary long-jump seed **without a new physical
A press**, not prove negative depth impossible in all gameplay. Working
backward, the useful chain is: first negative landing calculation, landing
timer four or five, long-jump landing, earlier long jump, the input that
started it, then the controller sample that supplied that input. The first
two links still require the same-run timer preservation described above.
The source census identifies the ordinary crouch-slide constructor and the
long-jump landing's repeat-jump callback. A repeat jump already presupposes
the long-jump cycle, so it cannot explain how that cycle first began. An
exhaustive live classification would let us reason about that **first** entry
instead of enumerating every possible later jump sequence.

The bounded next connection is
[`InkCrouchSlideHistory.v`](../../proofs/InkCrouchSlideHistory.v). It follows
the real US/JP crouch-slide timer window, including its actual timer write.
That write cannot overlap the input field in the ordinary Mario record.
If the A-pressed flag was clear before the timer window, it remains clear
at the long-jump test, which skips the constructor. This works for every
starting timer that completes this code, not just a chosen sample. A second
theorem starts at the complete crouch-slide body, with its earlier
sliding-cancellation flag also clear, and derives the same input and Mario
reference at the actual continuation after this window. It retains all later
calls as real, unchecked continuation; it does not claim the rest of the
action is harmless. The selected body is the one already resolved by
`imb_selected_bodies_resolve`.

What remains is to deliver that clear flag from the controller in the same
run, through the remaining input processing and action dispatch, and to
classify every other possible first entry into the long-jump cycle. Held A
must not be confused with a new press: the initial remembered sample must
agree with the accepted starting history, and later samples must be ordinary
controller input rather than demo input. Completing those links would remove
the normal long-jump explanation for a no-new-A seed. Other earlier depth
changes, actual audio/animation effects, storage persistence and survival of
the negative seed would still need their own checks. There is no claim yet
that a physical A press is universally necessary.

### The larger no-A history

The earlier duration endpoint is the end of `common_landing_cancels`, not
the later depth write. It does not yet establish that every complete cancellation call
reaches this suffix: the steep-floor, sliding and first-person checks precede
it. Nor does it establish all required input and descriptor facts at that
reached point.

The subsequent wrapper and `common_landing_action` execute genuine helpers:
an optional wrapper sound, landing acceleration or slope deceleration,
ground movement, animation, and landing sound. The leave-ground action
change is now checked to install zero regardless of earlier effects. The
other post-ground switch branches and dust update are covered above, with
the wall-animation conditions explicit. For the other ground results, the
earlier wrapper, acceleration and ground-movement effects must still be
connected in that same run before identifying the timer at this switch with
the bounded cancellation timer. No generic safe-call premise closes those
earlier intervals.

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

The focused `check-ink-late-helpers` target builds the integrated
`MainTheorem` and audits twenty-one theorem assumption reports: the twelve
earlier timer reports plus nine helper-resolution, actual-write, animation,
sound and final-calculation reports. The connected late-call result extends
`InkBackwardHistoryCheckedBoundary`; the whole-run impossibility theorem's
three coverage requirements remain open. This focused target, not the full
sixty-three-report `check-ink-backward` suite, is the verification run for
this tranche. It passed all twenty-one reports, using only the existing
Coq/CompCert foundations. The separate legacy discipline audit remains blocked
by its missing `sm64-proof` toolchain; it is not counted as a successful build
or assumption audit. The active SSL run
uses `sm64-item-proof`.

For subsequent SSL work, the [active proof audit](../proof-audit.md) now
provides the legacy audit's mechanical checks using that installed toolchain.
The legacy failure above is retained as the record of this proof tranche,
not a requirement to install a second toolchain.

The initialization/no-request/all-outcome extension is included in
`InkBackwardHistoryCheckedBoundary`, exposed by
`MainTheorem.current_ink_backward_execution_boundary`. It adds no accepted
runtime specification and does not discharge the whole-run impossibility
theorem's three coverage requirements. The active SSL audit is the
verification mechanism for this extension, including its new theorem
assumption reports and integrated Main build.

That extension passed the active audit on 2026-09-09: the integrated build,
nine focused assumption reports, source checks and import-closure checks
all succeeded, using only the existing Coq/CompCert foundations. The report
is retained locally at `build/audit/20260909-134536-t58a1sw3/`. All five new
modules are in Main's import closure. The audit's 26 regression tests also
passed. This was a Main-and-requested-dependencies build, not a rebuild of
every standalone proof.

The crouch-slide history extension also passed on 2026-09-09, with its
single-file check, integrated Main build, four focused assumption reports,
and source/integration checks. Its report is
`build/audit/20260909-152327-qihswnbm/`. Both new theorems are consumed by
`InkBackwardHistoryCheckedBoundary`; no new foundational axiom or accepted
runtime effect was added. This is a checked local action-history connection,
not a completed controller-to-landing history or a discharge of the whole-run
theorem's three coverage requirements. No full standalone rebuild was run.

All claims concern successful defined in-bounds Clight execution and ordinary
gameplay, including glitches within that model. No method for ACE, arbitrary
memory/code modification or out-of-bounds corruption is developed. Emulator,
operating-system and network vulnerabilities are outside this work.

[Return to the negative-depth approach in the atlas](../no-a-route-atlas.md#route-rank-19)
