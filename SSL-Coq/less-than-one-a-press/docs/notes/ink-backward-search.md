# Working backward from Ink installation

## The destination we are working backward from

Ink has a strong **conditional installation**, not yet a clean no-A route to
both stars. In the recorded Japanese test, supplying the right three positions
makes the game remember the pyramid top, retain that reference when the top
disappears, and apply its movement after entering Area 2. The continuation
reaches one puzzle secret. Creating the supplied positions through gameplay,
and collecting each target star afterward, remain separate tasks. The
[timer-131 note](timer131-surface.md) records both the successful mid-face
setup and an earlier setup that finds the top but loses it before the warp.

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
| The retry starts at the useful height | The vector copy reads the required height from its source. | The copy supplies no upward increment. It cannot turn a low source height into the desired high one by arithmetic. |
| The high source belongs to Mario's display record | The live Mario-object reference and source coordinates are the expected ones. | Ordinary source syntax identifies this record, but a universal live identity and memory-history connection is still needed. |
| Display remains high while collision touches the warp | Some earlier operation creates and preserves that separation. | Moving only Mario's movement position preserves the prior display/collision gap; it does not create one. Stock visual offsets are far below the known required gap under their checked conditions. |
| Every ingredient occurs together | One no-A history creates the gap, activates the pillars and reaches the warp while the needed top surface exists. | A clean pillar run is recorded, but it reaches the warp after the top disappears. That recording does not supply the installation. |

The 960-unit figure belongs to the **known capture-preserving mid-face
setup**. It is not a minimum proved for every conceivable Ink installation.
The more general checked timer-131 floor-height calculation requires at least
632 units under its signed-range and stock-mesh conditions. A different point
must establish its own floor result and support lifetime. Signed-coordinate
wrapping and a different selected surface cannot be dismissed by applying a
bound whose premises they do not satisfy.

## What this tranche adds to the proof

The new [source checkpoints](../../proofs/InkBackwardSource.v) and
[execution proof](../../proofs/InkBackwardExecution.v) replace a source-order
observation with necessary predecessors in actual executions of the selected
US and JP code. A completed geometry call has an ordered prefix, the actual
floor read, the chosen retry-or-skip branch and the remaining suffix. The
prefix includes both wall queries and the first floor lookup. Its effects
are retained as real subexecutions, not assumed harmless.

The retry's vector-copy name resolves to the selected internal game function,
not an unspecified outside effect. A taken retry also supplies its actual
object read, copy call and second floor query in sequence. Within that actual
copy, Y is read from the source and its Float32 value is stored unchanged at
the Y assignment. The proof retains the
earlier X operation and later Z operation as distinct parts of the same
execution. It does not assume that the Y read sees the memory from before X:
carrying the value back to copy entry still requires the appropriate
separation and preservation facts.

This does **not** yet prove that the first query traverses the expected live
list, that the copy's source points to the intended live Mario object, or
that every no-A history keeps the displayed position low. It also does not
derive a complete small-step frame or retail-machine simulation. Those are
the connections needed to turn these local backward cuts into a universal
route verdict.

## The next useful backward cut

Work backward from the Y value actually read by the copy, first to the
display record at copy entry and then to its last change or reset. Prove the
ordinary destination/source separation for the preceding local and X writes;
establish the Mario-object identity read by the caller; then classify the
earlier display and raw collision-position changes together. Each proposed
producer must explain both the gap and why it survives until this lookup.
Lowering the collision position while leaving the display behind can create
the same gap as raising the display; a complete exclusion must cover both.

A wall push may unlock the retry, but the retry still needs
something useful to copy. If every allowed earlier producer is too small or
resets the gap, the installation is impossible under those established
conditions. If one survives, test it with the pillar timing and warp contact
before spending effort on the star continuations.

## Verification and remaining scope

The active SSL `check-ink-backward` target compiles the integrated main proof
and passes five assumption audits, with no new project-specific axioms.
`MainTheorem.current_ink_backward_execution_boundary` exposes the new cuts.
The ultimate impossibility theorem still has its three explicit whole-run
and route-coverage requirements; this tranche sharpens the real branch/copy
part of that work rather than removing those requirements. The repository's
separate legacy build check still cannot run because its `sm64-proof`
toolchain is absent; the successful SSL checks use `sm64-item-proof`.

[Return to the Ink approach in the atlas](../no-a-route-atlas.md#route-rank-2)
