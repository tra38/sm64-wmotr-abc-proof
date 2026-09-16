# Fresh triplet spawning from the elevator

The stock triplet parent is too far from the elevator to activate at its
original position. Its own inactive update cannot move it, and its script
does not enable movement. The new proofs check the distance and several
actual update paths. The live distance helper, its caller's store and the
complete native-command dispatch are now connected. **The complete theorem
covering every spawning check from fresh entry is still open.** The actual
square-root routine now has a local instruction proof of its rounded result
and unchanged RAM, and the reached triplet argument is in its supported
range. An explicit local library binding now executes the complete generated
helper through that routine and rejects the distance test. The old external
oracle is not equated with this runtime; broader game/OS control history and
composition through every update remain open. Those limits supply no
stock-game route to the children.

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
It does not yet establish the return through the loop and the next engine
update.

## What remains to finish the requested closure

The engine's distance helper reads **Mario's raw Object position**. A claim
that Mario remains in the elevator must establish the rectangle for those
reads, not just for MarioState or the displayed position. The remaining
state-preservation work includes the interpreter's loop return and command
table, the rest of the object's engine update, collision-list traversal and
intervening actors. Each must carry the same fresh parent's fields to the
next check. A proof about consecutive calls with those fields simply
assumed again would not close this gap. Already loaded children, a different
entry history, or leaving the rectangle are outside the fresh-confinement
claim.

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
is not equated with this runtime. Composition with the surrounding engine
and preservation of the entry controls through earlier game/OS activity
remain explicit work. No new axiom or blanket external-call frame is used.

The result therefore narrows the preservation work and establishes exact
local exclusions. It does not yet close these three actors for every
controller history, close the six singleton approaches, or close Rank 10A.
The overall Rank 10A estimate remains 2–5%; that is a subjective route
estimate, not a probability supplied by this proof.

## Proofs and checks

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
unfinished confinement theorem.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a).
