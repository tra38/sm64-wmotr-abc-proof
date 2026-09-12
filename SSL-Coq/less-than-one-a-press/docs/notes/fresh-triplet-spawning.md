# Fresh triplet spawning from the elevator

The stock triplet parent is too far from the elevator to activate at its
original position. Its own inactive update cannot move it, and its script
does not enable movement. The new proofs check the distance and several
actual update paths. The live distance helper, its caller's store and the
complete native-command dispatch are now connected. **The complete theorem
covering every spawning check from fresh entry is still open.** A missing
library model prevents treating the checked distance formula as an
unconditional fact about the current Clight execution. This is a limitation
of the proof, and supplies no stock-game route to those children.

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

The real `sqrtf` implementation is a return plus a `sqrt.s` instruction in
the return's delay slot, with no memory store. The current generated Clight
program nevertheless exposes it as an unresolved external. CompCert's
generic external-call rules do not say that a function named `sqrtf`
computes square root or preserves writable object storage. The live-call
proof has reduced the helper's entire effect to this exact library call;
its remaining contract cannot be derived from the C declaration alone.
The machine implementation must be connected to the execution model, or
the model must be explicitly refined and its transfer proved. Another
geometry check or induction that assumes this contract cannot finish it.
No new axiom or blanket external-call frame is used to skip this step.

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

The selected audit passed on 2026-09-12 at
`build/audit/20260912-171553-cstgvtwa/`, using Coq 8.16.1 and CompCert 3.15
through the established pipeline and memory limit. It checked 556 registered
sources, built Main and the three new modules, and passed proof-hole, link
and integration checks. All five selected entry points use seven existing
allowed foundations. No new axiom was added. The 131 local links in the five
edited documents, the atlas's three single-paragraph sections and whitespace
checks also pass. These checks validate the stated connections, not the
unfinished confinement theorem.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a).
