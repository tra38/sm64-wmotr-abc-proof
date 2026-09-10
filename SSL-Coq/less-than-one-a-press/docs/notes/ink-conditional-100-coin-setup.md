# Ink with a granted 100-coin reward setup

## Agreed scope

The user selected a **fresh, normally initialized level-select entry into
SSL Area 1** on 2026-09-10. Earlier gameplay carrying a prepared action,
timer, negative depth, or height gap into SSL is not part of this starting
case. A normal saved star total may vary. We still have to derive the live
storage references and first scheduled update from that initialization;
the user's choice does not prove those implementation facts.

For this conditional investigation, we may skip proving how the earlier
coins were collected or brought into position. We grant a valid coin and
100-coin-star arrangement that Mario can collect from a position reached by
the preceding gameplay. This removes the **placement-provenance** task,
not the ordinary contact, star behavior, collection, action, and dialog
rules. The existing failed placement at one quicksand boundary therefore
does not disprove this enlarged search.

The allowance supplies one granted reward opportunity during the visit,
not an unlimited supply of new stars. Any further reward must follow the
actual game's collection and bookkeeping, not another free setup grant.
The allowance does not move Mario, supply
a long jump, alter his depth or heights, create a new A press, or directly
start a dialog. Do not assume immediate tangibility, skip the spawn time
stop, or choose independently compatible snapshots. An older star may be
collected later, but its waiting interval and the surviving Mario state
must remain in the same history. A proposed solution must name its actual
collection frame and show that both ordinary contacts are possible.

This is a declared proof-model allowance, **not a method for modifying a
running game**. Ordinary gameplay and defined, in-bounds glitches remain
the implementation scope. No memory-corruption or code-modification method
is being developed.

## Both star-count cases remain available

The game checks whether the new total **crossed** a threshold that the
remembered total had not reached. Its thresholds are 1, 3, 8, 30, 50, and 70.
Normal initialization sets the remembered total equal to the current total,
so entering with exactly 30 stars does not by itself leave the 30-star
message pending.

For exactly one newly earned star, the popup-producing starting totals are
therefore **0, 2, 7, 29, 49, and 69**. Other starting totals give the
non-milestone case. This is the user's clarified allowance: for example,
**enter at 29, then earn the star to reach 30**, not enter at 30 and treat
the 30-star milestone as pending. Collecting a previously saved reward need
not increase the total; that case must not be silently treated as a new star. The normal
100-coin save prompt and the later milestone message are different dialogs:
absence of a milestone does not remove the ordinary save prompt.

These counts come from the generated milestone table and the existing
one-star crossing theorem in
[NoExitStarDialogBridge.v](../../proofs/NoExitStarDialogBridge.v).
Initialization and the actual comparisons are in
[US Mario](../../generated/us_mario.v) and the
[US cutscene code](../../generated/us_mario_actions_cutscene.v), with matching
JP bodies. The arithmetic result is not itself a proof that a live star
award updated the save file and both count readings correctly.

## What the popup does, and what it does not supply

The known conditional mechanism starts with **already-negative quicksand
depth**. Repeated sinking while the automatic dialog waits can then raise
the displayed Mario position without repeatedly resetting it. What
accumulates is the display/position gap, not a newly generated negative
depth. Thus a helpful star arrangement and a milestone are worth retaining,
but neither is permission to assume the missing negative seed.

The grounded star-dance action also calls the ordinary floor/position reset.
Consequently the common star dance and its save prompt cannot simply be
replaced by the later unreanchored automatic-dialog wait. Both the milestone
and non-milestone continuations must be executed in their actual order.
The [older mechanism audit](negative-quicksand-unreanchored-dialog.md) retains
the conditional accumulation and transport results.

## A complete helper is now classified

[InkStarDialogFrame.v](../../proofs/InkStarDialogFrame.v) opens the complete
US/JP `get_star_collection_dialog` execution, including its loop, function
entry, and return. Every successful completed call makes exactly one
two-byte memory store, at MarioState's remembered-star-count field. It calls
no outside helper. Its memory effect is derived from the actual statements,
not supplied as a safety assumption.

The resulting theorem preserves quicksand depth and the 24 shared Ink
readings, including movement, displayed and collision positions, action and
timer, and cached floor information. It applies regardless of which star
count branch succeeds. The depth equality also retains unsuccessful or
non-finite readings; it does not make them disappear by assuming a finite
incoming value. The shared object readings require the established
MarioState/object-pool separation.

[InkStarDialogCall.v](../../proofs/InkStarDialogCall.v) resolves the named
function in both selected linked programs and applies this frame to its
actual call instruction with the live Mario argument. Both results are
consumed by the checked Ink backward boundary. This removes the milestone
check itself as a possible first negative-depth writer. It does **not**
frame the surrounding animation, sound, save, action-setting, or scheduler
calls, or prove that a run from the fresh entry reaches the call.

## Remaining proof and interpretation

Keep the [shared invariant ledger](ink-shared-history-invariants.md), adding
the reward-specific requirements listed there. In particular, connect the
last depth writer, the reward contact, the full star dance, and the first
useful automatic-dialog sink in one history. Floor alignment remains a
separate possible gap producer and must also be tracked during this
allowance. No clean seed or complete Ink continuation has been found here.

The existing `ImportedClightRun` still denotes ordinary steps of the selected
program. It has **not** been redefined to disguise a granted setup as a game
step. The placement allowance is now an explicit investigation boundary;
constructing its formal start-to-setup interface and connecting the later
history remain work to do. The new helper theorems apply to either branch
without requiring that allowance as an axiom. The main impossibility theorem
has not acquired a new assumption that the reward setup is clean-reachable.

A successful conditional route would establish sufficiency **with the
allowance**, after which its coin and star preparation must be recovered in
ordinary gameplay. An exhaustive impossibility result for an enlarged model
would exclude the stock cases it demonstrably contains. Merely failing to
find a route, checking one placement, or proving this one helper harmless
does not do that. Current status: **local milestone-check case closed;
whole-history connection missing; neither Ink producer closed**.

## Verification

Both new Coq modules and the integrated Main/dependency audit passed. The
five checked assumption reports contained only existing allowed foundations;
no project-specific axiom was added. The local report is
`build/audit/20260910-111113-mrtooyyg/`. This verifies the recorded local
theorems and their integration, not the remaining gameplay history.

[Back to the Ink route](../no-a-route-atlas.md#route-rank-2)
