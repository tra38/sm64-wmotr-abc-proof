# Working backward from Ink installation

## The destination we are working backward from

Ink's known supplied setup **bypasses the elevator**; clean installation
remains open. In the recorded Japanese test, supplying the right three positions
makes the game remember the pyramid top, retain that reference when the top
disappears, and apply its movement after entering Area 2. The
[new recording](ink-area2-arrival-video.md) makes the consequence explicit:
Mario bypasses the elevator and lands on an upper walkway. Its short
continuation reaches one puzzle secret; a separate existing continuation
also records conditional Act-6 collection. Creating the supplied positions
through gameplay remains open; this particular recording does not contain
an Act-3 collection. The
[timer-131 note](timer131-surface.md) records both the successful mid-face
setup and an earlier setup that finds the top but loses it before the warp.

For the present search, reaching the upper walkway is the accepted useful
downstream boundary, supported by the supplied gameplay videos. We are
working on creating the Ink setup, not searching for another star route
after that arrival. This does not turn the videos into a complete Coq proof
of star collection.

The useful setup has Mario's collision position touching the upper warp,
his movement position at `(-2200,768,-1024)`, and his stored displayed position
at `(-1862,1778,-902)`. The top must be on its spinning update numbered 131.
These are simultaneous requirements in one run, not interchangeable parts
from different runs. The displayed height is 1,010 units above the warp
center, or at least 960 above any collision position touching that warp.

## How to walk backward

Start with a specific successful event, find the operation that can produce
it, and ask what must be true immediately before that operation. For a copy,
the required number must already be in its source. For a conditional branch,
its actual test must allow the branch. For a floor selection, the accepted
surface must be present in the list the game really searches. Each answer
becomes a smaller earlier question.

There are two different kinds of branching. If the installation needs a
warp contact **and** a failed first lookup **and** a useful retry, all three
must coexist; disproving any necessary part closes that installation. If
several different actions can supply one required value, those are
alternatives; disproving one leaves the others open. A failed controller
search is evidence about the inputs tested, not proof that every alternative
fails.

To rule a branch out, prove that its necessary earlier condition contradicts
a checked property of the game. Carry the identity, timing and memory facts
needed by that argument explicitly. A restriction on one action, one pose or
one recorded run cannot silently become a restriction on all play. Repeated
actions need a rule that survives every repetition; simply searching farther
back does not handle an unlimited history.

Walking backward does not mean reversing the controls or playing the physics
in reverse. A landing, reset or disappearing object can have many possible
earlier states. Keep all allowed alternatives until a checked condition
excludes them, and carry the no-new-A-press rule through the whole history,
not just the final frame.

Then work **forward** from the accepted start to test the surviving earlier
conditions. Backward reasoning identifies what a successful run must supply;
forward reasoning establishes whether controller play can supply it. A real
counterexample needs those two accounts to meet in the same state, without
placing Mario or editing game memory to bridge the gap. Ordinary gameplay
glitches remain in scope; methods for ACE, out-of-bounds memory corruption or
arbitrary memory/code modification are not part of this search.

## Ink's backward chain

Read this table from the desired result toward earlier requirements.

| Desired result | What must happen earlier | What can already be rejected, and what is open |
| --- | --- | --- |
| Useful top movement after the warp | The correct top reference survives the remaining frames and Area-2 entry. | The earlier low side-face setup loses its support and fails this continuation. The supplied mid-face setup survives in the JP recording; a clean installation is open. |
| Mario remembers the top | A live floor query selects a surface owned by that top. | A high displayed position alone is insufficient. The correct loaded face, list order and later support still matter. |
| The displayed-position retry runs | The floor pointer read after the first lookup is null. | A non-null pointer at that test skips this retry, even if an older cached floor was null. A clean first miss remains a separate requirement. |
| The retry starts at the useful height | The required height is already in the display record when the retry begins. | For ordinary separate storage, the real copy's local initialization and X write preserve that height; the Y assignment writes it unchanged. The copy itself is not a height producer. |
| The high source belongs to Mario's display record | The live Mario-object reference names the expected object. | The selected US and JP field reads and copy arguments are proved. The floor-reset helpers also keep the object reference actually read at their own entry, through their preceding calls. The correct object identity across the wider history remains open. |
| An old high display survives a downward floor snap | The usual display reset is skipped, or something changes again afterward. | The stop routine and the stationary routine's no-moving-ground branch write the newly read floor height to the display. Their State-only snap leaves the separate collision/display object untouched. The moving-ground branch remains distinct. |
| The ordinary collision copy leaves a useful height gap | Movement and display already differ when that copy begins. | With the ordinary matching Mario references, the actual height assignment copies the incoming movement height and leaves the incoming display height unchanged. Its four preceding writes preserve both readings. Earlier changes and survival through the remaining statements are still open. |
| Display remains high while collision touches the warp | Some earlier operation creates and preserves that separation. | Moving only Mario's movement position preserves the prior display/collision gap; the checked collision copy can then transfer an existing movement/display difference into a collision/display gap. The full history and skipped resets still need joint accounting. Stock visual offsets are too small under their checked conditions. |
| Every ingredient occurs together | One no-A history creates the gap, activates the pillars and reaches the warp while the needed top surface exists. | A clean pillar run is recorded, but it reaches the warp after the top disappears. That recording does not supply the installation. |

The 960-unit figure belongs to the **known capture-preserving mid-face
setup**. It is not a minimum proved for every conceivable Ink installation.
The more general checked timer-131 floor-height calculation requires at least
632 units under its signed-range and stock-mesh conditions. A different point
must establish its own floor result and support lifetime. Signed-coordinate
wrapping and a different selected surface cannot be dismissed by applying a
bound whose premises they do not satisfy.

## What the checked retry copy establishes

The [source checkpoints](../../proofs/InkBackwardSource.v) and
[execution proof](../../proofs/InkBackwardExecution.v) replace a source-order
observation with necessary predecessors in actual executions of the selected
US and JP code. A completed geometry call has an ordered prefix, the actual
floor read, the chosen retry-or-skip branch and the remaining suffix. The
prefix includes both wall queries and the first floor lookup. Its effects
are retained as real subexecutions, not assumed harmless.

The retry's vector-copy name resolves to the selected internal game function,
not an unspecified outside effect. A taken retry supplies its actual object
read, copy call and second floor query in sequence. The
[copy-entry proof](../../proofs/InkCopyEntry.v) carries the Y read backward
through both earlier writes. The function really allocates a fresh local
pointer cell, initializes it from its argument, then copies X to the supplied
destination. With source and destination in their ordinary separate storage,
neither write changes the source height. The destination pointer also survives;
it is not replaced with an assumed temporary value.

The [caller proof](../../proofs/InkCopyCaller.v) checks the selected US and
JP field layouts and derives the actual two copy arguments: MarioState's
position and the named object's display position. MarioState storage and the
object pool are different globals, so their separation follows from the
program's symbol rules. Combining these facts proves that the Y assignment
writes the displayed height already present at retry entry into MarioState's
Y cell, unchanged. The object read, copy and following floor query still
belong to one actual branch execution. No animation increment, local-pointer
initialization or earlier X write inside this copy can supply the missing
height under these conditions.

This result still requires the caller to be using the ordinary MarioState
storage and its object field to name a position in the existing object pool.
It proves exactly where the caller looks and what it copies once those facts hold;
it does not prove that every preceding gameplay frame supplies them. In
particular, membership in the object pool alone does not identify Mario's
correct slot or establish its lifetime. The incoming display height is read
from memory, not assumed to be low or assumed reachable through controller
play.

This does **not** yet prove that the first query traverses the expected live
list, that every earlier frame keeps the intended live Mario-object reference, or
that every no-A history keeps the displayed position low. It also does not
derive a complete small-step frame or retail-machine simulation. Those are
the connections needed to turn these local backward cuts into a universal
route verdict.

## A downward floor snap is now checked

The new [source checkpoints](../../proofs/InkFloorResetSource.v),
[saved-object proof](../../proofs/InkFloorResetExecution.v), and
[reset execution proof](../../proofs/InkFloorResetCopy.v) cover two ordinary
US and JP paths: the stop-and-snap routine, and the stationary-ground routine
when its actual test does **not** select moving-ground movement. The latter
can choose another branch; the proof records that choice rather than treating
both branches as a reset. No numerical bound on the sampled floor height is
needed for this result.

Each routine first remembers the object named by MarioState. The proof follows
that actual read and establishes that the same saved reference reaches the
reset, even across the preceding helper calls. Those calls retain their actual
memory effects: the result concerns the caller's saved reference,
not a claim that the calls leave all memory unchanged. Identifying this object
as the intended live Mario throughout an earlier gameplay history remains a
separate requirement; the reset theorem also requires its allocation to remain
valid at the reached cut.

At the reset, the game first writes the sampled floor height to Mario's
movement position. With the ordinary separate storage, this write leaves
every read from the collision/display object's allocation unchanged. The
following real vector copy then writes that **new floor height** to the
display's Y cell. Its local setup and earlier X write cannot substitute the
old display height. Thus a large downward snap cannot explain retaining the
old high display through this particular Y assignment: the display is reset
along with the movement position, however large the drop.

This does not prove that the sampled floor is low. A legitimately high floor
could still supply a high display, while raw collision has not yet caught up.
That possibility must explain the actual selected floor and the subsequent
collision update; the theorem does not declare every reset gap-free.

This is an exact checkpoint, not a promise about every later operation. The
proof keeps the copy's entry, earlier statements, Y read and write, remaining
statements, return, and caller's remaining statements in one memory-linked
execution. Keeping those later operations in the same execution does **not**
yet prove that they preserve the new display height. The later angle helper,
other action paths, and following frames still need their own effects checked.
The collision-position copy now has the additional local cut below, but the
intervening path from this reset into that call remains open.

## The collision-height handoff is now checked

After Mario's action, the game normally copies his movement position into his
collision object. That copy does not use the displayed position as its source.
The new [source checkpoints](../../proofs/InkRawCopySource.v) match the actual
selected US and JP function, reusing the existing checked function resolution.
The [identity proof](../../proofs/InkRawCopyIndex.v) follows its real comparison:
if the current object and Mario's object name the same ordinary pool slot at
entry, the copy selects MarioState number zero. That selection is derived from
the test, not supplied as an unexplained temporary value.

Before writing collision Y, the function copies velocity X, Y and Z, then
position X. The [read and address proof](../../proofs/InkRawCopyExpressions.v)
and [store proof](../../proofs/InkRawCopyStores.v) derive where each actual write
goes. None changes the displayed Y, the separate movement-height source, or
the global current-object reference used by the next write. This checks the
whole four-write prefix, not just one convenient store.

The [completed-call proof](../../proofs/InkRawCopyHeight.v) therefore reaches
an exact checkpoint: immediately after collision Y is written, it equals the
movement height at copy entry, while displayed Y still equals the displayed
height at copy entry. The source movement height also remains unchanged.
These are exact stored Float32 values; no approximate height arithmetic is
needed. If movement and display agree on entry, collision and display agree
at this checkpoint. If they differ, this copy can transfer that existing
difference into a collision/display gap. It does not invent a new height.

This is not a proof that a useful incoming difference is reachable, or that
it survives until the retry. The remaining copy statements belong to the same
execution, but their memory effects are not yet proved harmless here. The
caller, the preceding action tail, the wider live Mario identity and the path
to the next lookup still need connecting. In particular, the floor-reset
result and this copy result are not spliced together as though their endpoints
were already the same state. No clean Ink producer is established.

## The next useful backward cut

Work backward from the movement/display difference required at the ordinary
collision copy's entry. Find the last display change and account for every
movement change between that point and the copy. A checked floor reset passes
the height question back to the floor actually sampled, rather than the old
display; then both the remaining reset statements and action tail must be
followed into this copy. Also classify the remaining collision-copy statements
and the path to the next lookup in that same run, retaining the correct live
object reference. Lowering movement while leaving display high can become a
collision gap at the checked copy, but only if that difference survives until
the copy reads it.

The other concrete direction is movement during an action that skips the
usual display reset. Platform movement during a stalled dialog was already
identified in the [dialog audit](negative-quicksand-unreanchored-dialog.md);
this is not a new demonstrated route. It still needs an actual movement and
collision history that creates a useful gap and preserves it until the retry.
The stationary routine's moving-ground branch and any later changes also
remain open, rather than being excluded by the no-moving-ground reset proof.

A wall push may unlock the retry, but the retry still needs
something useful to copy. If every allowed earlier producer is too small or
resets the gap, the installation is impossible under those established
conditions. If one survives, test it with the pillar timing and warp contact
before spending effort on the star continuations.

## Verification and remaining scope

The active SSL `check-ink-backward` target compiles the integrated main proof
and checks seventeen theorem assumption reports, including the earlier retry
and floor-reset results plus the collision-copy source, identity test,
four-write frame and completed-call height cut. No project-specific axiom was added.
`MainTheorem.current_ink_backward_execution_boundary` exposes the strengthened
`InkRawCopyCheckedBoundary`, which includes all previous cuts and the existing
selected collision-copy resolution.
The ultimate impossibility theorem still has its three explicit whole-run
and route-coverage requirements; this tranche sharpens the real branch/copy/reset
part of that work rather than removing those requirements. The repository's
separate legacy build check still cannot run because its `sm64-proof`
toolchain is absent; the successful SSL checks use `sm64-item-proof`.

[Return to the Ink approach in the atlas](../no-a-route-atlas.md#route-rank-2)
