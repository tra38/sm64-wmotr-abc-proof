# Fresh triplet spawning from the elevator

The stock triplet parent is too far from the elevator to activate at its
original position. Its own inactive update cannot move it, and its script
does not enable movement. The new proofs check the distance and several
actual update paths. **The complete theorem covering every live spawning
check from fresh entry is still open.** In particular, these results must
not be described as an exhaustive gameplay-history proof.

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
field to 19000, which also fails the spawning test. Subsequent enabled
calculations must be connected to their actual reads and return value.
RNG does not appear on the rejected native path. Waiting or suspending an
update supplies no movement through any of the proved cases.

## What remains to finish the requested closure

The engine's distance helper reads **Mario's raw Object position**. A claim
that Mario remains in the elevator must establish the rectangle for those
reads, not just for MarioState or the displayed position. The exact caller,
behavior-script dispatch, collision-list traversal and intervening actor
updates still need to carry the same fresh parent's fields between checks.
The proved gates and helper frames are ingredients for that argument;
they are not a substitute for it. Already loaded children, a different
entry history, or leaving the rectangle are outside the fresh-confinement
claim.

The real `sqrtf` implementation is a return plus a `sqrt.s` instruction in
the return's delay slot, with no memory store. The current generated Clight
program nevertheless exposes it as an unresolved external. Its numeric
result and memory effect must be linked to that implementation before the
Float32 formula can be asserted as the result of the live distance call.
No new axiom or blanket external-call frame is used to skip this step.

The result therefore narrows the preservation work and establishes exact
local exclusions. It does not yet close these three actors for every
controller history, close the six singleton approaches, or close Rank 10A.
The overall Rank 10A estimate remains 2–5%; that is a subjective route
estimate, not a probability supplied by this proof.

## Proofs and checks

The new modules are [Area2TripletSpawner.v](../../proofs/Area2TripletSpawner.v),
[Area2TripletEngine.v](../../proofs/Area2TripletEngine.v) and
[Area2TripletGraphics.v](../../proofs/Area2TripletGraphics.v).
[ReadOnlyClightPaths.v](../../proofs/ReadOnlyClightPaths.v) proves that each
certified path determines every corresponding Clight execution. The
capstone consumes these results through
`current_fresh_triplet_spawner_execution_boundary` and the existing
combined Rank 10A boundary.

The selected audit passed on 2026-09-12 at
`build/audit/20260912-154422-vcpt8a96/`, using Coq 8.16.1 and CompCert 3.15
through the established pipeline and memory limit. It checked 553 registered
sources, built Main and the new modules, and passed proof-hole, link and
integration checks. The combined boundary, complete callback and graphics
frame each use seven existing allowed foundations; the universal Float32
bound uses four. No new axiom was added. The 128 local documentation links,
the atlas's three single-paragraph sections and whitespace checks also pass.
These checks validate the stated local results, not the unfinished live
confinement theorem.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a).
