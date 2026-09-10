# Ink: one-history invariants for both height producers

The objective is still to reach the conditional Ink installation from the
accepted SSL Area-1 start. We must follow both ways of creating a gap: raising
the displayed position, and lowering the movement position while the display
stays behind. The known installation uses a 960-unit gap; that is not a
universal threshold for every possible installation point.

These are **proof requirements, not newly accepted assumptions**. “Invariant”
here means a rule preserved at its specified program checkpoints. Several
rules need different cases at different instructions. Defining the list does
not prove that all reachable executions satisfy it. If a case fails, retain
the actual instruction and readings as an unresolved case; do not discard it.

## Shared rules

| ID | Precise rule to carry | Where it must be established |
| --- | --- | --- |
| H1 — One execution | Every checkpoint has an actual Clight state. Its preceding and following steps belong to the same selected US or JP execution, with identical memory and control stack at each join. No independently chosen snapshots. | From the accepted boundary through the retry, including the scheduler between Mario updates. |
| H2 — Start and control | The initial depth is zero, the three position records agree, the initial action and timer are the accepted ones, and the first scheduled call really uses that memory. The accepted memory boundary does not itself specify the next instruction or call stack. | Initial state and the first action call. |
| H3 — Live identities | Each fresh global, MarioState, object, controller, body-state, floor-owner and animation-buffer reference names the intended live record. Record changes of slot or lifetime explicitly; do not replace a fresh read by an old reference. | At each dereference, call and object/area lifetime change. |
| H4 — Storage and effects | Every reached write has its actual destination and size. It either misses the tracked cells or is a checked update to them. Copies, indirect calls and outside calls need their own reached effects. Body-state and animation/audio destinations must be proved separate, not assumed so because of their names. | Every intervening instruction, not merely helper returns. |
| H5 — Readings | Preserve the exact Float32 values and failed or unexpected reads until classified. A finite-number lemma applies only after finiteness is derived. Pointer offsets, signed-16 conversions and overlap tests use the selected program's real layout. | Every height/depth read, comparison, conversion and copy. |
| H6 — Order | Carry the real phase: controller sampling, Mario preparation, special floors, interactions, repeated action dispatch, sinking, object copying, remaining object/camera/audio work and the next update. A repeated dispatch is not a new controller sample. Time stop, skipped updates and area transitions are explicit branches. | Each phase transition and callback. |
| H7 — Last producer and survival | For every changed height or depth, identify its last actual writer in this execution and the intervening resets or frames. A changed value at a helper boundary is insufficient if it was changed and restored inside the helper. | Backward from the useful sink read or Graphics retry. |

## Floor-alignment rules

| ID | Precise rule to carry | Where it must be established |
| --- | --- | --- |
| F1 — Three heights | Track movement Y, raw object Y and display Y separately, together with X/Z. A copy reads its source at its actual entry, and a later copy/reset ends that value's lifetime. Equality is required only where the code really establishes it. | Ground-step display refresh, alignment, object synchronization and retry. |
| F2 — Two floor readings | The floor cached in MarioState and the floor returned by the current quarter-step query are separate observations. Each must come from its own actual query and stores; water adjustment and the null-floor retry are separate cases. | Geometry preparation and every quarter step. |
| F3 — Query ownership | Each selected floor belongs to the live list and owner at that query, with the actual triangles, insertion order and lifetime. Moving geometry and retained surfaces cannot be replaced by static geometry from another time. | Every relevant floor, wall and ceiling query. |
| F4 — Blocked-step relation | Relate the caller's attempted position to the position after both wall responses and to the actual new floor/ceiling readings. If the high branch is taken, distinguish ceiling block from leaving the ground. Also cover the earlier missing-floor block and a newly higher floor. | The actual quarter-step branch and its caller's result handling. |
| F5 — Alignment eligibility | Prove which crawling/sliding action still calls alignment after the ground-step result. Track movement minus the *cached* floor at this point; do not infer this difference from the other floor's 100-unit test. The snap uses the cached floor and the matrix-building tail needs its own effect. | Ground-step return, display refresh, alignment snap and tail. |
| F6 — Gap bound or witness | Either derive a bound too small for the actual installation point for every retained mismatch, or preserve one exact useful mismatch through the remaining action, sink, object copy, two retry queries and top/warp timing. There is no established universal bound to assume here. | From the last refresh through the useful lookup. |

## Negative-depth rules

| ID | Precise rule to carry | Where it must be established |
| --- | --- | --- |
| N1 — Depth phase | At a useful sink read, trace the depth to a surviving producer. Inside the landing subtract-and-clamp sequence a temporary negative value is allowed: prove the clamp completes before any use. “Depth is nonnegative at every instruction” is **not** the proposed invariant. | Every depth write, clamp and useful sink read. |
| N2 — Complete producer cases | Cover special-floor changes, interactions, each dispatched action, action setters, landing calculations, initialization/reset paths, later scheduler writes and specified outside effects. A descriptor/table argument needs its established immutability and actual read, not a nominal constant. | The first surviving change and every earlier pass. |
| N3 — Timer phase | The timer belongs to the current action, resets at the actual setter, and advances only through classified instructions. Carry cancellation and all landing outcomes, including animation and sound calls, to the final calculation. Reuse the checked long-jump landing bound only at its matching live call. | From action entry to the late landing write. |
| N4 — First long-jump origin | Follow the first long-jump constructor in this history. A repeat-jump cycle must lead back to an earlier constructor, not justify itself. Other actions and transitions require explicit exclusion or a concrete alternative. | Across all action passes back to the accepted initial action. |
| N5 — Physical input history | Button-pressed bits come from the actual current and previous physical samples. Later processing and remembered-A updates retain that provenance. Held A at the boundary is allowed and is not a new press. Demo or substituted input must be excluded by execution, not by renaming it physical input. | Controller sampling, input processing and the constructor's actual guard. |
| N6 — Closure | After H1–H7 and N1–N5 are established, the first useful negative depth must have a preceding new physical A press. With no such press, sinking cannot be this installation's height producer. This closes the negative-depth branch only; F1–F6 remain a separate obligation. | The useful read, not an isolated landing snapshot. |

## Proof construction order

Start with the common action prefix, preserving exact readings for both
branches. Open `mario_reset_bodystate`, then input preparation, special-floor
handling and interactions. Continue through every action-loop case and the
sink. Close the remainder of the scheduler and the controller sampling edge
before inducting over successive passes. At each stage reuse the existing
floor, landing and controller theorems at their actual memory endpoints.

The proof is universal over executions, not a finite controller search. Its
induction step must classify each reachable instruction or retain an explicit
unresolved case. A test run can supply a counterexample, but cannot discharge
that universal step.

## First shared proof extension

`InkSharedReadings.v` defines 24 exact memory observations: the action and
previous action, action state/timer/argument, remembered-A counter, movement
X/Y/Z, cached wall/ceiling/floor pointers and heights, the object/body/controller
references, depth, and display/raw-object X/Y/Z. They preserve failed loads
and non-finite values instead of silently filtering them. The accepted start
initializes zero depth and the three matching Y readings. This observation
set is the frame for the initial prefix, not a claim that the full game has
only 24 relevant cells. Mario's flag word, for example, has a separate update.

`InkBodyResetFrame.v` checks the US/JP body-reset source and layouts, opens its
five body-state stores and final Mario flag-word store, and derives the memory
frame of the completed helper. There is no outside call in this helper.
`InkBodyResetResolution.v` resolves the actual callee in each selected program.
The refined visibility theorem also identifies its exact two-byte store.

`InkBodyResetHistory.v` uses the actual fresh global read at the reset call,
proves that the visibility store preserves that global and the body reference,
and joins the two actual stage executions onto the previously constructed
action-call prefix. Its result is one `ImportedClightRun` ending immediately
before `update_mario_inputs`, with the same 24 readings and the initial zero
depth and equal Y values. This is a shared H1/H4/H7 preservation step for both
branches, rather than another standalone landing/button calculation.

**The conditions matter.** The result is quantified over actual successful
completions of these two stages; it does not generate their completions from
the accepted memory alone. The body pointer must load successfully and name
storage separate from MarioState and the object pool. Those facts and the
real scheduler control point are **not** fields of the accepted start, and
were not added to it. Establishing them from initialization and carrying them
through the scheduler is still required. The theorem's first later unchecked
stage is the actual `update_mario_inputs(gMarioState)` call, not a promise
that its effects or the later action loop are safe.

The invariant families above were defined before that extension. The checked
local reset case does not establish H1–H7, F1–F6 or N1–N6 for every game history.
The branch status remains **whole-history connection missing**, not
**route closed**. The capstone retains its whole-run coverage obligations.

## Verification

The individual Coq checks and the integrated active SSL audit passed on
2026-09-10. The audit built Main and the requested dependencies, checked five
theorem assumption reports, and passed source inventory, proof-hole, link and
import-closure checks. All four new modules are in Main's import closure;
the shared extension is consumed by `InkBackwardHistoryCheckedBoundary`.
No new project-specific axiom or accepted outside-call effect was added.
The report is retained locally at `build/audit/20260910-103603-vh50_sqf/`.
This was not a rebuild of every standalone proof and is not a full-game
impossibility verdict.

[Floor history](ink-floor-history.md) ·
[Negative-depth closure argument](negative-depth-shared-closure.md) ·
[Ink route](../no-a-route-atlas.md#route-rank-2)
