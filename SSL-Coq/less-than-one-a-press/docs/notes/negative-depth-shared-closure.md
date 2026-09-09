# Negative depth: one shared-history closure

## The claim we need

Starting from the agreed SSL Area-1 boundary, any first useful negative-depth
value must have a history containing a new physical A press. This is the
single closure target for this branch. Unrelated route exploration is paused.
The existing proof collection does **not** establish this claim.

“Useful” here starts with a negative depth actually read by the sinking code
to raise Mario's display or display matrix. A stronger result excluding every
negative depth at that use point would suffice; we need not also solve the
dialog transport, pillar timing or star collection to exclude the seed.
Conversely, a surviving negative seed alone would not prove the full Ink route.

Do not replace this target with “no intermediate instruction ever stores a
negative depth.” In `quicksand_jump_land_action`, the game subtracts from depth
and immediately clamps a result below one to 1.1, before calling the sound or
animation helpers. Small incoming depths can therefore give a temporary
negative result in this code. This source observation is not a no-A reachable
counterexample. The shared proof must cover the complete adjustment, or show
that no relevant use intervenes, instead of treating the temporary store as a
surviving seed. It must also cover later writes after the clamp.

## The argument, working backward

1. Fix **one** successful execution of the selected US or JP program, starting
   at the accepted boundary. Take its first useful negative-depth read. Keep
   the exact Mario record, instruction, memory and input history from this
   execution throughout; do not assemble them from separate possible runs.
2. Trace that value back through copies, changes and resets to its surviving
   producer. The accepted start already supplies zero depth and an action
   outside the long-jump cycle. A negative supplied before the agreed boundary
   is not an extra case under those boundary conditions. Intermediate negative
   values that are clamped away must not be mistaken for this producer.
3. Classify every remaining producer. If it is the ordinary final landing
   calculation, reuse the checked arithmetic: starting nonnegative, a negative
   result needs a timer of at least four. Carry the actual cancellation bound
   to that exact write. Only then does the stock split give long-jump landing
   at timer four or five. A failed timer, pointer or writer check is an open
   alternative, not evidence that long jump is the only possibility.
4. Trace that landing back to the **first** entry into the long-jump cycle.
   Repeated long jumps cannot explain their own first origin. The source
   census and checked crouch-slide guard are reusable, but every reached action
   change and callback still needs classification. Several action changes can
   occur within one frame; one input sample is not one action transition.
5. Trace the constructor's A-pressed input back to the actual controller
   sample. Carry the remembered input and the live controller reference from
   the accepted boundary through polling, later input processing and action
   execution. Establish that these are ordinary device samples, not demo
   input. Held A is allowed; the required event is a new up-to-down transition,
   not merely a set button or action flag.
6. This supplies a new physical A press before the useful negative read,
   contradicting a no-new-A history. Only when every preceding step is proved
   for the live execution is the negative-depth branch closed in this model.

The argument is not restricted to a single attempt. Resets, transitions and
earlier unsuccessful attempts must all remain in the same prefix. No castle
entry or new IDO-to-Clight start bridge is required under the agreed boundary.

## What is already available, and what is not

| Required connection | Reuse | Present status |
| --- | --- | --- |
| Accepted start has zero depth and no prepared long jump | `DefaultArea1StartBoundary`; `ordinary_area1_entry_memory_excludes_prepared_fixture` | Already follows from the agreed boundary; not new initialization work. |
| The actual useful display adjustment reads negative depth | `iq_actual_sink_raise_requires_negative_depth` | Local reduction checked under its storage and finite-number conditions; live identity and storage connection missing. |
| The surviving producer is one of the checked depth cases | `NegativeDepthDefinedProducerClosure` and its source inventory | Whole-history connection missing; a source census is not reached-write coverage. |
| The landing timer has the stock bound at the negative write | `imb_actual_negative_landing_with_stock_gate_requires_long_jump`; landing gate, timer-reset and late-call results | Local cases checked, with explicit conditions; the intervening execution and remaining effects are not closed. |
| Long-jump landing has a legitimate first constructor | `LongJumpProvenanceBoundary`; `InkCrouchSlideHistory` | Source/guard cases checked; whole action-history connection missing. |
| The constructor's input comes from a new physical press | Controller edge, remembered-input and complete button-helper results | Local sample processing checked; whole input history and physical-sample authentication missing. |

The [detailed history notes](ink-negative-depth-history.md) retain individual
theorem statements and verification records. Their checked conditions must
be discharged where the real execution reaches them, not promoted to global
facts because the local theorem compiled.

The action ordering and subtract-then-clamp observation above can be checked
in the generated Mario bodies ([US](../../generated/us_mario.v),
[JP](../../generated/jp_mario.v)) and moving-action bodies
([US](../../generated/us_mario_actions_moving.v),
[JP](../../generated/jp_mario_actions_moving.v)). They are source observations,
not newly proved whole-execution facts.

## Which work comes next

The next selected obligation is **surviving-producer coverage in one live
history** (the third row above), starting with the action pass that reaches
the useful read. In the decompile, `execute_mario_action` orders input
preparation, special-floor handling, interactions, the repeated action
dispatch loop, and finally sinking. Follow this actual ordering while carrying
Mario's identity and the depth value. Include the remainder of the scheduler
between passes when extending to earlier frames. This is shared execution
work; another standalone timer or button lemma is not the next deliverable.

Use the existing `ImportedClightRun` and concrete frame-evidence machinery:
each checkpoint must have actual Clight states, matching memory at adjacent
ends, and a trace decomposition in that run. The existing controller
chronology interfaces are obligations to instantiate, not facts already
proved by naming them. Account for every reached internal write and every
reached outside effect on the relevant record. Reuse the local results at
their matching calls. Do not introduce a blanket “all relevant calls are
safe” or “the history is valid” premise in place of this work.

Invalid identities, non-finite readings or an unclassified effect must remain
explicit cases until excluded or explained. They cannot be silently dropped
to make the local theorems' conditions hold.

The acceptance test is a derived, same-run producer classification, or one
exact reached instruction whose effect cannot yet be classified. An explicit
unproved coverage condition is a better specification, but it is not a
removed premise and must not be reported as such. A finite sample of runs
also does not close an all-controller-history claim.

## Reporting and stopping rules

- **Local case closed:** name the real code covered, its remaining conditions,
  and the shared-history obligation it helps discharge.
- **Whole-history connection missing:** the local facts exist, but the actual
  run has not been shown to satisfy and connect them. This is the current
  branch status.
- **Route closed:** all in-scope surviving producers have been covered in the
  same execution argument and the physical-A implication has been proved.
  This status is **not** reached.

Future tranches must say which row they discharged or sharpened, what proof
consumes the result, and what remains. Adding another conjunct to
`InkBackwardHistoryCheckedBoundary` or passing its build is not by itself a
whole-history connection. This document is a source-backed obligation audit
and work-selection correction, not a newly discharged execution premise or
a new Coq closure theorem.

All work remains ordinary successful, defined in-bounds game execution,
including glitches within that model. Outside-model memory/code modification
and emulator, operating-system or network vulnerability work remain excluded.

[Back to the negative-depth route](../no-a-route-atlas.md#route-rank-19)
