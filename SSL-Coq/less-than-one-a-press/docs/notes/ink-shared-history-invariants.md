# Ink: one-history invariants for both height producers

The objective is still to reach the conditional Ink installation from the
accepted fresh, normally initialized level-select SSL Area-1 start. The user
confirmed this scope on 2026-09-10; earlier gameplay carrying prepared state
into SSL is not required. We must follow both ways of creating a gap: raising
the displayed position, and lowering the movement position while the display
stays behind. The known installation uses a 960-unit gap; that is not a
universal threshold for every possible installation point.

The user has now accepted complete normal starting-state facts at the
post-initialization boundary. Startup reconstruction is no longer required.
The current priority is the first useful negative depth; floor alignment's
separate height bound is deferred, not ruled out.

The preservation rules below are **proof requirements, not assumptions about
later gameplay**. “Invariant”
here means a rule preserved at its specified program checkpoints. Several
rules need different cases at different instructions. Defining the list does
not prove that all reachable executions satisfy it. If a case fails, retain
the actual instruction and readings as an unresolved case; do not discard it.

There is now also an explicitly [granted 100-coin reward setup](ink-conditional-100-coin-setup.md).
For that conditional investigation, both milestone-triggering starting totals
and ordinary starting totals are allowed and coin/placement provenance is
postponed. This does not grant
negative depth, move Mario, replace the normal collection/dialog rules, or
turn later scheduler or preservation obligations into assumptions.

## Shared rules

| ID | Precise rule to carry | Where it must be established |
| --- | --- | --- |
| H1 — One execution | Every checkpoint has an actual Clight state. Its preceding and following steps belong to the same selected US or JP execution, with identical memory and control stack at each join. No independently chosen snapshots. | From the accepted boundary through the retry, including the scheduler between Mario updates. |
| H2 — Start and control | Normal initial depth, positions, action, timer and storage are accepted at the post-initialization boundary. Every game step after that boundary must still have its actual control point and continuation; the memory contract alone is not a scheduler execution. | Accepted initial state, then the first and later game updates; no startup reconstruction. |
| H3 — Live identities | Each fresh global, MarioState, object, controller, body-state, floor-owner and animation-buffer reference names the intended live record. Record changes of slot or lifetime explicitly; do not replace a fresh read by an old reference. | At each dereference, call and object/area lifetime change. |
| H4 — Storage and effects | Every reached write has its actual destination and size. It either misses the tracked cells or is a checked update to them. Copies, indirect calls and outside calls need their own reached effects. Normal initial references are accepted; initial separation follows from actual storage names, and later destinations require preservation proofs. | Every intervening instruction, not merely helper returns. |
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

### Additional reward-history rules

| ID | Rule to carry | Status |
| --- | --- | --- |
| R1 — Exact allowance | Mark where coin/100-coin-star placement is granted, and keep the preceding Mario pose, action, timer, depth, input history and three positions. Do not label that unproved preparation an ordinary Clight step. | User-approved conditional boundary; its formal execution interface is not yet constructed. |
| R2 — Normal availability | The reward is a normal no-exit star, not a moved Mario, instant award, or unlimited repeated reward. Keep the spawn lifecycle, time stop, ordinary coin/star contact, and any delay before collection. | Placement provenance is granted; execution and timing remain obligations. |
| R3 — Real star totals | Initial current and remembered totals agree. Cover a newly saved star and a duplicate reward separately; identify the actual count reads and save result at collection. The milestone choice is derived from those counts, not chosen independently. | Initialization source and one-star threshold arithmetic checked; live save/count history remains open. |
| R4 — Distinct dialogs | Separate the ordinary 100-coin save prompt during star dance from the later automatic milestone message. Cover both the milestone and ordinary-idle continuations, including B-based dialog progression with no new A edge. | Source chronology known; complete reached effects and input chronology open. |
| R5 — Seed versus accumulation | The stalled sink can amplify an existing negative-depth height effect. Trace the depth back before the star contact, through any intervening landing/clamp/reset, rather than assuming the popup produces it. Track the floor-alignment alternative simultaneously. | The full milestone-check helper is now framed; surrounding actions and scheduler are not. |
| R6 — Honest result scope | A successful granted route is conditional until its setup is reached cleanly. An impossibility theorem must cover every permitted setup and history, and show that the stock cases under discussion are included. | Neither a full granted-route witness nor an impossibility theorem is established. |

These are additional obligations, not proved invariants. The grant changes
the search boundary; it does not discharge the shared H or branch F/N rules.

### Shared execution construction

Reuse the checked common action prefix and `mario_reset_bodystate` frame,
establishing their remaining entry/storage conditions. Then open input
preparation, special-floor handling and interactions while preserving exact
readings for both branches. Continue through every action-loop case and the
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

**Earlier result, now strengthened below.** This original result was quantified over actual successful
completions of these two stages; it does not generate their completions from
the accepted memory alone. The body pointer must load successfully and name
storage separate from MarioState and the object pool. Those facts and the
real scheduler control point are **not** fields of the accepted start, and
were not fields of that original boundary. The user has since accepted the
normal initial facts, and the construction below removes both completed-stage
premises. Carrying storage through later game updates is still required.
That original theorem's first later unchecked
stage is the actual `update_mario_inputs(gMarioState)` call, not a promise
that its effects or the later action loop are safe.

The invariant families above were defined before that extension. The checked
local reset case does not establish H1–H7, F1–F6 or N1–N6 for every game history.
The branch status remains **whole-history connection missing**, not
**route closed**. The capstone retains its whole-run coverage obligations.

## Accepted initial storage and constructed preparation

`InkAcceptedInitialStorage.v` states the normal initial body reference,
integer flags and writable cells used so far. It derives separation between
the body array, MarioState, object pool and Mario pointer cell from the
selected program's actual global names. These are explicitly accepted
starting conditions, not new project axioms or promises about later calls.
No particular later action, timer, depth or height is supplied.

`InkVisibilityConstruction.v` and `InkBodyResetConstruction.v` construct the
visibility store and all six body-reset stores, including their reads,
casts, write permissions and real internal call. `InkPreparationConstruction.v`
joins them to the native-command/action prefix with its original continuation.
There is no longer a premise that either stage successfully completed. The
result also derives the fresh Mario pointer, integer status flags, unchanged
collision metadata and surviving permissions needed by the next helper.

`InkInputPrefixConstruction.v` constructs the next four writes: clearing
particles, clearing input, copying the object's collision metadata and
masking Mario's status flags. `InkInputSharedConstruction.v` connects their
actual input-function entry and resolved button call to the initial action
prefix. This gives one uninterrupted action-call execution through eleven
writes. All 24 tracked readings, including zero depth and matching initial
heights, survive, and the input word is zero at the button-call entry. The
old input word need not be assumed harmless; it is actually overwritten.

**What this does not prove:** these action-call fragments have not yet been
joined to every intervening post-boundary world update. The native extension
still needs its reached command readings. The continuation through successful
button and joystick calls is now connected below; their completion has not
yet been constructed from the initial storage. Geometry queries, special
floors, interactions, the repeated action loop, sinking and later scheduler
effects still require their same-history connections. No first useful negative seed has been found or universally
excluded. This is a removed local execution premise, not route closure.

## Controller history at that same call

The controller's initial new-press word now survives the eleven preparation
writes by a derived storage frame. The proof uses the actual controller,
body-array, MarioState and object-pool symbols to establish their separation;
it does not add a premise saying that the intervening operations leave the
controller alone. The word read at the button call is exactly the accepted
current/previous sample's new-press word, and MarioState still points to that
same controller. Held A remains permitted.

`InkInitialControllerGuard.v` extends the constructed action history through
the button helper's real entry, controller-reference read, new-press-word
read and A-pressed test. The A-pressed branch is not taken and memory remains
unchanged. An explicit same-run cut retains the preceding button-call entry.
The existing complete-button no-new-A theorem is then instantiated at that
exact call with its now-derived input and controller readings: every
successful completion of that call still has the A-pressed input bit clear.
This is not a separate hypothetical controller snapshot.

`InkButtonTailFrame.v` classifies every statement in the actual remaining
US/JP button tail using its checked source structure. Its only writes are
the input word and the two button-age bytes. At the reached tail, every
successful execution therefore preserves depth, action and the action
timer. The age counters themselves are allowed to change; this is not a
claim that all 24 original readings survive the entire button helper.
No sound, animation, other outside-call effect or later controller sample
is assumed safe by this result. The constructed prefix ends after the first
A-pressed guard, not after the entire input helper, and the whole-history
negative-depth claim remains open.

A read-only check for the later sampling obligation also locates the normal
demo-input switch: `src/menu/title_screen.c:run_level_id_or_demo` clears the
demo pointer and can install a demo at the idle title screen;
`src/game/game_init.c` consumes/advances an already active demo. This source
observation is not a proved exclusion of every later title/demo path. The
later controller-history proof must distinguish those paths from ordinary
physical samples, rather than labeling generated demo input as a physical
press or assuming the demo gate stays inactive forever.

## Consecutive button and joystick calls to the first wall query

`InkInputGeometryHistory.v` now keeps the saved input-function continuation
from the constructed prefix. Given actual, consecutive completed button
and joystick calls, it follows both returns, the next named calls, and
geometry-function entry in one `ImportedClightRun`. The endpoint is the
first `f32_find_wall_collision` statement, with the original Mario pointer,
the actual accumulated memory and the full caller stack. A same-run cut
retains the earlier button-call entry; the two helpers cannot be taken from
executions with mismatched intermediate memory.

`InkInputAngleFrame.v` resolves `atan2s` and `atan2_lookup` in both selected
programs and proves their complete successful calls leave memory unchanged,
including entry and return. No outside-effect specification is assumed for
either. `InkJoystickFrame.v` checks every branch of the real joystick body:
the only writes are intended magnitude, intended yaw and an input update
that cannot set A-pressed. Together with the completed button-call frame,
the extension derives zero depth, the unchanged initial action and timer,
and clear A-pressed at the first wall-query statement. The result does not
need to choose particular stick directions or assume finite stick readings
just to obtain this memory-effect classification. An unsuccessful or undefined
execution is not turned into a successful gameplay continuation.

**What was removed:** an unclassified joystick/angle-helper effect, plus the
missing call/return connection between the reached button call and geometry.
**What remains:** the actual completed button and joystick executions are
still premises of this extension; they have not been constructed from the
initial storage or extracted from an arbitrary start-to-use history. For a
universal proof, extracting them from that same history is sufficient;
constructing one selected controller run alone would not establish coverage
of every execution. The first wall-query effect is not yet classified here.
Later samples, geometry and action transitions, the landing calculation,
and world updates before and between Mario passes remain unconnected.
The initial action-call fragment is still not proof that the surrounding
post-initialization scheduler reaches that call in that exact memory.

This is a local classification and same-history extension, not closure of
the negative-depth route. The source review identifies the next concrete
work inside the wall query: a temporary collision record, the two wall-list
traversals, a diagnostic counter and the X/Y/Z copy-back. Their effects must
be proved in the selected execution, not accepted from this description.

## Milestone helper extension

`InkStarDialogFrame.v` derives the complete milestone helper's single
two-byte store to the remembered count and proves it preserves depth and all
24 shared readings. Its count-search loop has no memory write or outside
call. `InkStarDialogCall.v` resolves the actual callee in each selected
program and carries the same frame through the named call instruction.
Both are consumed by `InkBackwardHistoryCheckedBoundary`. This classifies
one real effect relevant to R3/R5 for both star-count outcomes; it does not
connect the reward setup or the surrounding star dance to the accepted start.

## Behavior command to the shared action prefix

The shared construction now starts two real calls earlier. It follows the
native behavior command's fresh command-pointer read, callback-operand
read and conversion, the indirect call into Mario's callback, that
callback's fresh current-object read, and its direct call into
`execute_mario_action`. The action then reads MarioState and Mario's object
from that same memory. Both linked US and JP functions are resolved from
their actual definitions; no outside-call frame is assumed for these calls.
The new steps change only local temporaries and the call stack, not memory.

This is not restricted to the spawn action. The action prefix now accepts
any actual action reading for which the real branch test succeeds. The
original spawn-specific theorem is recovered as a special case. The
callback's passed object and MarioState's object need not be assumed equal
for this prefix: its action code reads the latter. A defined argument
conversion is still required, and the callback's later stores after the
action returns are **not** covered by this observation.

`InkScheduledSharedHistory.v` attaches these constructed steps to the exact
final state of a supplied `ImportedClightRun`. It retains that run's start,
all preceding events, the full memory, and both nested caller continuations.
It also constructs an `InkRunCut` recording the actual prefix and suffix,
so a matching-looking snapshot from another run cannot be substituted.
The original visibility/body-reset extension attached successful stage
executions at that endpoint. The newer `InkPreparationConstruction.v`
constructs both completions from their concrete storage facts. It transports all 24
observations for both height-producer branches, including failed or
non-finite height readings. Initial zero depth and equal heights survive
if they held at the reached command boundary.

| Connection | What is now derived | What is still required |
| --- | --- | --- |
| Native command → Mario callback | The actual operand read, conversion, internal-function resolution and call steps, with unchanged memory. | Reach the command with the live pointer and operand shown in `InkNativeEntryReadings`. The stock operand receipt is not proof of its later load. |
| Mario callback → action prefix | The actual fresh argument read, call, MarioState/object reads and successful action branch, with both callers retained. | Establish the actual global readings and defined argument conversion at this boundary. No equality between the two object readings is needed for this prefix alone. |
| Existing run → extended run | Exact endpoint equality, trace concatenation and a same-run cut; no completed callback/action is assumed. | Supply any preceding post-boundary gameplay execution. Startup reconstruction is excluded, but ordinary scheduler steps cannot be replaced by independent calls. |
| Prefix → input preparation | Visibility and body reset are now constructed, preserve the readings and supply the next helper's metadata. The initial action-call case continues through input reset to the actual button call. | Initial normal storage is accepted. Establish its live counterparts at later calls, then connect the remaining input/action/scheduler effects. |

The first earlier unconnected source boundary is still the behavior
interpreter in `cur_obj_update`: its assignment from the current object's
saved command pointer, the command-table selection, and the preceding
commands must be connected to the scheduler/list traversal. In the stock
Mario script the callback command is at byte 36 and its operand at byte 40;
the preceding debug callback and the script's first-time setup cannot be
skipped merely because the desired callback's initializer is known. The
post-boundary scheduler writes and later live references remain unproved;
normal initial facts are accepted rather than reconstructed. After the now
constructed input prefix, the completed button and joystick effects are
classified and their consecutive execution is connected to geometry. Their
completion from the initial storage, the geometry queries, remaining input
processing, special floors, interactions, action loop, sinking and the rest
of the scheduler still need coverage.

This discharges a concrete **internal call-chain construction**, not the
accepted-start reachability premise or the all-history producer classifier.
It finds no negative seed or useful floor-alignment mismatch, and neither
Ink branch is closed. The granted reward is not inserted anywhere in these
ordinary Clight steps.

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

The later milestone-helper extension passed both individual module checks
and the integrated audit at `build/audit/20260910-111113-mrtooyyg/`. The audit
built Main and its requested dependencies, checked five assumption reports,
and reported 345 of 439 proof modules in Main's import closure, 94 retained
standalone modules, and no inventory or integration problems. The new
helper/call theorems use only seven existing allowed foundations; no new
project axiom or outside-call frame was accepted. This also was not an
all-standalone build or a route-closure result.

The behavior/callback shared-history extension passed its individual checks
and the integrated audit at `build/audit/20260910-115116-31zwthl9/`. Main
compiled; all five requested assumption reports passed. Both new execution
theorems use seven existing allowed foundations. The audit counted 519
sources, with 349 of 443 proof modules in Main's import closure and 94
standalone modules, and found no inventory, proof-hole, link or integration
problems. All four new modules feed the shared Ink boundary. No new project
axiom, accepted outside-call effect, or whole-run coverage assumption was
added. The explicit command-entry and reset/storage premises above still
need to be established; passing these checks is not a route-closure result.

The constructed-preparation tranche passed the individual checks and the
integrated audit at `build/audit/20260910-134435-p9ojec6r/`. Main compiled;
all four requested assumption reports passed. The two new execution results
use seven existing foundations, with no project-specific axiom or new
outside-call effect. The audit found 525 sources, 355 of 449 proof modules
in Main's closure, 94 standalone modules, and zero hygiene/integration
problems. All six new modules are on Main's proof path. The accepted initial
storage contracts are explicit hypotheses, as authorized by the user;
the later universal coverage conditions are still unproved.

The controller-connection tranche passed its individual checks and the
integrated audit at `build/audit/20260910-140239-um8kiqs_/`. Main compiled and
all three assumption reports passed. The new same-history guard theorem
uses seven existing allowed foundations; no new initial assumption or
outside-call effect was needed beyond the preceding tranche's accepted
normal storage. The audit found 527 sources, 357 of 451 proof modules in
Main's closure, 94 standalone modules, and zero hygiene/integration problems.
Both new modules are consumed at the shared Ink boundary. This verifies the
stated initial-call connection and button effects, not universal route closure.

The joystick/geometry tranche passed its individual module checks and Main
build. The first audit, `build/audit/20260910-152521-jdh463lx/`, verified both
new theorem assumption reports (seven existing allowed foundations each),
but failed overall because both Main queries exceeded the 180-second limit.
The bounded retry at `build/audit/20260910-154309-4t_4iqhd/` passed with a
360-second per-query limit: the shared Ink boundary uses the same nine
allowed foundations and the consolidated conditional theorem uses six.
No proof assumptions or memory limits were changed for the retry. The audit
counted 531 sources, 361 of 455 proof modules in Main's closure, 94 standalone
modules, and zero inventory, proof-hole, link or integration problems. All
four new modules feed the shared Ink boundary. This is not an all-standalone
build, a constructed full gameplay history, or a route-closure result.

[Floor history](ink-floor-history.md) ·
[Negative-depth closure argument](negative-depth-shared-closure.md) ·
[Ink route](../no-a-route-atlas.md#route-rank-2)
