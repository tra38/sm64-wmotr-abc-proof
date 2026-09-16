# Fresh triplet spawning from the elevator

**The fresh triplet cannot spawn during the specified conditional sequence
of checks.** The first check rejects the initialized distance of 19,000;
every later check calculates a distance of at least 3,882 and rejects too.
The proof carries the same parent's unloaded state through any finite
number of checks. It assumes the stated parent preservation, raw Mario
position bounds and named library contract. Establishing those conditions
through every intervening part of ordinary gameplay remains separate.
This closes the requested conditional claim, not all Goomba access or
Rank 10A.

## The conditional result

The proof begins at the first native-command check, after the stock
script's setup. The parent has its stock X/Z, action zero, flags 65,
intangible timer -1 and initialized distance 19,000. It follows the actual
generated US and JP code. Later checks include the real six-coordinate
distance calculation, the post-call current-object read, the distance-field
write and the complete native-command dispatch and return.

Between checks, the contract preserves five parent fields: flags,
intangible timer, X, Z and action. Between a distance write and its check,
it also preserves the stored distance. The current-object pointer and live
script operand must identify this parent and its real callback at the
stated boundaries. Ordinary storage conditions keep the distance write
away from the retained fields and the command-pointer global separate
from the parent. Mario's **raw Object** coordinates at each calculation
must lie in the full elevator rectangle; the rounded vertical difference
must be finite and within the proved range.

The named square-root contract requires the correct result for the reached
argument and preservation of the current-object pointer and those five
parent fields. It assumes nothing about unrelated calls. The instruction
and explicit local binding proofs separately give a stronger unchanged-RAM
result under their processor controls; this theorem does not silently
identify that runtime with the older Clight external oracle.

The key distinction is that the interlude contract preserves the previous
action value; it does not assume action zero anew at every check. The
actual distance write preserves that value, and the actual callback rejects
spawning and preserves it again. Induction carries the initial unloaded
state through the sequence. Each callback has a proved path containing no
calls or writes, so its child-creation code is not reached. Its local
allocation and cleanup and the native dispatcher's command advance are
included in the existing execution proofs used here.

The theorem covers every check in any supplied finite sequence satisfying
these conditions, with no sample count or time limit. It does not certify
that a selected list contains every check of an arbitrary gameplay run.
Applying it to a whole confinement episode still requires the contracts
at all of that episode's checks. Children created before this starting
boundary and the six singleton Goombas are outside the claim.

## Why this parent is a poor supplier

The only stock triplet parent starts at `(3181,0,3587)`. The full elevator
base covers X from -511 to 512 and Z from -255 to 768. At the nearest
corner the horizontal differences are 2669 and 2819. Their squared sum is
15,070,322, giving about 3,882.05 units of horizontal separation. The parent
requires a distance strictly below 3,000 to create its children. This is
the activation distance of the parent, not a home-range rule for children
that have already been created.

The new Coq bound includes every fractional Float32 X/Z in that rectangle
and rounding in the actual three-dimensional expression. It proves a
lower bound of 3,882 when the rounded vertical difference is finite and
between -16,384 and 16,384, a generous range for the stock elevator journey.
This is a universal arithmetic result, not a sampled movement search.

## What keeps the parent still

The exact US and JP behavior scripts enable only distance calculation and
graphics copying. Their flag value is 65. The ordinary X/Z movement,
vertical movement and parent-relative transformation gates all reject
that value. The initial floor drop concerns Y; it does not request an
X/Z move. Afterward the script repeats the spawner callback. When its
action is unloaded and the distance test rejects spawning, the complete
callback leaves every existing memory cell unchanged, including its X/Z,
action, flags and intangible timer. The proof includes its local allocation
and cleanup, rather than assuming those operations are harmless.

The parent starts with intangible timer -1. The actual collision gates
skip such an object whether it is the first or second participant; the
countdown also leaves -1 alone. Thus the ordinary collision-push proposal
needs a real earlier change to that state. The complete graphics helper
only writes the object's display coordinates and angles. Its checked
memory frame preserves all raw fields, including the actual X/Z and the
intangible timer. These facts remove specific possible parent movers;
they do not assume that all other calls preserve the parent.

There is a first-update detail: the engine calculates distance before the
script first enables that calculation. Allocation initializes the distance
field to 19000, which also fails the spawning test. For subsequent enabled
calculations, the engine's call now resolves to the real linked distance
helper. Its six Object reads supply the three differences, and the complete
helper returns exactly the square-root call's value and memory. The engine
then stores that value through the current-object pointer it reads after
the call. The proof keeps this later read visible; it does not presume
that the external call preserved the pointer. RNG does not appear on the
rejected native path.

The complete native-command dispatcher is checked too. When its live
operand identifies this spawner and the unloaded parent's distance rejects
spawning, it calls the real linked callback, preserves every existing cell
outside the command-pointer cell, advances by two words and returns the
interpreter's continue result. For the stock script this reaches the
end-loop command. This includes the callback's local allocation and cleanup.
The conditional sequence now connects this return to the next distance
stage through the explicit five-field preservation contract. The loop and
the next whole engine update have not themselves been proved to supply it.

## What remains beyond the conditional closure

The engine's distance helper reads **Mario's raw Object position**. A claim
that Mario remains in the elevator must establish the rectangle for those
reads, not just for MarioState or the displayed position. The remaining
state-preservation work includes the interpreter's loop return and command
table, the rest of the object's engine update, collision-list traversal and
intervening actors. Each must carry the same fresh parent's fields to the
next check. The new theorem uses that preservation as the user's explicit
condition and proves what follows; it does not claim to have derived the
condition from the scheduler. Already loaded children, a different entry
history, or leaving the rectangle are outside the fresh-confinement claim.

The [square-root implementation proof](sqrtf-implementation.md) now decodes
the authentic two-word routine, follows its return delay slot and derives
the correctly rounded result and unchanged RAM. The actual triplet input
is finite and between 15,070,322 and 536,870,912. This excludes the tiny
subnormal inputs that make the older “finite, nonnegative” wording too broad.
The routine proof uses explicit ordinary CPU controls; it is a local
instruction result, not a complete console semantics. A concrete local
library binding now checks the exact selected US/JP declaration, passes the
C argument to the instruction routine, and returns its result and memory.
The complete generated helper has a constructed linked execution that
rejects the distance test. The binding's external result is unique; no
matching-machine-call premise is needed. The old unspecified-call semantics
is not equated with this runtime. Preservation of the entry controls
through earlier game/OS activity and transport of the surrounding engine
to this local runtime remain explicit work. The conditional sequence instead
retains its precise named-call premise in the older Clight semantics.
No new axiom or blanket external-call frame is used.

The result therefore closes the named conditional fresh-triplet claim.
It does not close these three actors for every controller history, close
the six singleton approaches, or close Rank 10A.
The overall Rank 10A estimate remains 2–5%; that is a subjective route
estimate, not a probability supplied by this proof.

## Proofs and checks

[Area2TripletChecks.v](../../proofs/Area2TripletChecks.v) contains
`tcs_fresh_triplet_never_spawns_under_contract`. Its `TripletFreshChecks`
input spells out the real calls, boundary reads and interlude contracts.
The conclusion certifies every listed callback and preserves the parent's
five fields through the last return. The Main and combined Rank 10A
boundaries consume this result through `Area2TripletSpawnerBoundary`.

The selected audit passed on 2026-09-15 at
`build/audit/20260915-225949-v9qy04zh/`: 574 registered sources, successful
Main build, proof-hole and link checks, and no integration problems.
The Main boundary, live distance-stage connection, conditional sequence
and callback-path consequence each use seven existing allowed foundations.
The run used Coq 8.16.1 and CompCert 3.15 with the established memory limit.
No new axiom or admitted proof was added. These checks validate the
conditional result; they do not prove its gameplay premises.

The initial modules are [Area2TripletSpawner.v](../../proofs/Area2TripletSpawner.v),
[Area2TripletEngine.v](../../proofs/Area2TripletEngine.v) and
[Area2TripletGraphics.v](../../proofs/Area2TripletGraphics.v).
[ReadOnlyClightPaths.v](../../proofs/ReadOnlyClightPaths.v) proves that each
certified path determines every corresponding Clight execution. The
capstone consumes these results through
`current_fresh_triplet_spawner_execution_boundary` and the existing
combined Rank 10A boundary.

[Area2TripletDistance.v](../../proofs/Area2TripletDistance.v) now connects the
complete helper to the reached square-root call, including its memory
effect. [Area2TripletDistanceUpdate.v](../../proofs/Area2TripletDistanceUpdate.v)
resolves the engine's call and follows its distance-field store.
[Area2TripletCommand.v](../../proofs/Area2TripletCommand.v) proves the complete
native-command frame and advance. The main boundary uses these results;
its distance-rejection component now concerns a live helper call with the
square-root numerical premise stated explicitly.

The later [implementation tranche](sqrtf-implementation.md) adds the
decoded instruction result, RAM frame and reached-input domain proof.
Its selected audit passed on 2026-09-15 with 570 registered sources and
five allowed-foundation reports. The subsequent concrete-binding tranche
is described there as well; the earlier oracle-conditional premise is not
silently discharged by changing execution models.

The earlier distance/store/dispatch audit passed on 2026-09-12 at
`build/audit/20260912-171553-cstgvtwa/`, using Coq 8.16.1 and CompCert 3.15
through the established pipeline and memory limit. It checked 556 registered
sources, built Main and the three new modules, and passed proof-hole, link
and integration checks. All five selected entry points use seven existing
allowed foundations. No new axiom was added. The 131 local links in the five
edited documents, the atlas's three single-paragraph sections and whitespace
checks also pass. These checks validate the stated connections, not the
unfinished unconditional confinement theorem.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a).
