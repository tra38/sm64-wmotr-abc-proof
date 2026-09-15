# Rank 10A: what could actually make Mario miss the descending base?

The eleven-descent ground-quarter hold is now **conditionally excluded**.
Starting aligned, Mario ends each contracted ground-quarter call at the
current base height. The proof follows the real US/JP call through its
position write, wall handling and return; it does not assume alignment.
The live query and between-call conditions are stated below.

The earlier ordinary blocked-step diagnostic remains separate evidence.
The new native source check really loads the elevator's collision, corrects
positions against walls, finds its floor and executes the ground quarter.
Every tested gap up to 100 realigns Mario. No missing base or outward
correction appeared. This is stronger evidence than the earlier geometry
table, but it is still a finite diagnostic, not a proof about every controller
history.

There is also a useful correction: a ceiling **can** stop a supplied ground
quarter near the top if Mario is already more than 100 above the base. That
case needs the very mismatch we are trying to create. It does not produce it.

## The four proposed causes

| Possible cause | What this check establishes | What is still unproved |
|---|---|---|
| Missing live floor | With the ordinary upright elevator loaded by the actual C loader, all 23,855,421 queried quarters return its base. Time stop does not erase existing collision: the real US/JP clearing body now has a Coq proof of unchanged memory. | Connect initialization, the renderer's transform reset, loading and list traversal across complete selected-program updates. |
| Wall correction outside the interior | Every tested correction stays within X=-410..411, Z=-154..667. A complete Coq census finds no static triangle anywhere in the larger wall-query corridor. | Cover all reachable floating-point positions and proposed movement steps, including the elevator's own wall-list traversal. |
| Another moving surface | All 12,293 tested transforms of the eight stock scripted moving obstacles miss that corridor at their stock transverse coordinates. The closest horizontal Grindel reaches only X=-584. | Prove the owner positions stay on their tracks through complete updates, especially the horizontal Grindels' wall checks; this transform check does not assume that proof has been completed. |
| Intervening state change | The actual ledge-down helper never requests an action change in the query sample. Active time stop freezes an ordinary elevator in all 64 tested combinations of the named time-stop bits. Ordinary looking away still reaches the renderer's matrix reset. | Cover the complete reachable action/interaction history. A collected coin/star or a previously arranged enemy remains a distinct producer question. |

The verdict is therefore **no working producer found**, with stronger
conditional exclusions. It is not “all four causes are impossible.” Ground
pound, a useful sideways departure and the whole no-A route remain open.
The atlas's subjective estimate for all of 10A stays at 2–5%; this narrower
ordinary-ground stall is less promising than it was.

## Why mention gameplay histories?

The missing history connection means that the conditions used in a local
check must hold when real gameplay reaches it. It does not demand a replay
of every button sequence. The diagnostic supplies ordinary elevator fields
and a fresh transform reset; a general exclusion must justify their continued
applicability, or account for the ways they can fail.

There are shorter proof methods. An invariant establishes the conditions at
entry and proves that each allowed update preserves them. A backward argument
examines the first loss of a required condition, including alignment. The
earlier updates satisfy the chosen conditions, so their first failure
needs a classification of the immediate mechanisms.
A sound finite abstraction can also cover more choices than the game allows,
but its coverage needs proof; a sample alone does not provide it.

For the user's conditional question, that narrower target is now proved.
The proof below closes the stated hold mechanism under explicit conditions.
It does not require proving those conditions for every controller history.

## Conditional eleven-descent exclusion

**Proved:** an initially aligned Mario cannot remain at his starting height
through eleven ten-unit descents in the contracted ground-quarter sequence.
The stronger theorem proves alignment after any number of these calls while
the base remains in the specified range. It is an induction over actual
selected-program calls, rather than a generalization from the nine sampled
eleven-descent paths.

The conditions are precise:

- The initial base height is an integer from 238 to 4966 for the eleven-step
  result, and each descent lowers it by ten, staying at or above 128.
- Each interval contains a completed call to the real
  `perform_ground_quarter_step` with ordinary MarioState and next-position
  pointers. After its actual query prefix, the floor pointer is non-null and
  the returned floor height is the **current** base height. A stale or lower
  floor answer does not satisfy this condition.
- The returned ceiling is finite and at least 5222. The actual action's
  riding-shell bit is clear, excluding the water-floor override.
- Between calls, the world may update, including moving the elevator and
  reloading collision, while Mario's Y is carried unchanged. The next
  proposed query Y is that carried value. This is the scoped hold proposal's
  vertical-input contract, not an assumption that he follows the floor.

After a descent, that carried height is only ten above the new base. The
real leave-ground comparison is false, and the separate floor/ceiling
comparison cannot stop the quarter. The actual vector setter then writes
the new base height into MarioState. Its temporary allocation, all three
coordinate writes and cleanup are covered. The following floor bookkeeping
does not overwrite Y, and the already-proved internal `atan2s` call leaves
memory unchanged. The outer quarter's local cleanup also preserves Y.

This rules out the first missed alignment under the contract. Repeating
the argument keeps the gap from accumulating: after eleven calls Mario is
110 units lower, aligned with the base, rather than held at the old height.
Wall contact is allowed; its post-alignment handling is included.

**Still conditional:** the relation between calls exposes the Y-carry
condition and allows other world data to change. It does not pretend to
execute or verify the whole intervening scheduler. The loading and transform
requirements are expressed by the actual query answers they must supply;
this tranche does not prove that every reachable rendering/loading history
supplies them. Omitted ground calls, different actions or vertical inputs,
and missing or stale floor answers remain outside this closure. Whole 10A,
ground-pound entry by other means and a useful sideways departure remain
open. Its subjective 2–5% estimate is unchanged.

The proof is in [GroundAlignment](../../proofs/Area2Rank10AGroundAlignment.v)
and [GroundHold](../../proofs/Area2Rank10AGroundHold.v), using the
[selected setter source](../../proofs/Area2GroundVectorSetSource.v).
`rank10h_completed_quarter_aligns` proves the complete call result;
`rank10h_no_first_missed_alignment` supplies the one-step invariant;
`rank10h_every_contracted_descent_realigns` proves the induction; and
`rank10h_eleven_descent_hold_impossible` gives the requested exclusion.
MainTheorem consumes the new conditional boundary.

The selected audit passed on 2026-09-14 in
`build/audit/20260914-222711-3xxviy24/`: 568 registered sources, 398 of 492
proof modules in Main's import closure, and 94 standalone modules. The Main
boundary, complete vector setter, complete ground quarter and eleven-descent
exclusion have respectively 7, 6, 7 and 7 allowed foundations. Compilation,
proof-hole, link and integration checks passed. These counts do not count
the explicit conditional premises above, and the audit is not a whole-game
proof or a rebuild of every standalone module.

## What the actual loader checks

The elevator's behavior script calls its movement routine and then
`load_object_collision_model`, with collision distance 20,000. Ordinary object
creation sets room to -1 and distance to 19,000. This elevator does not request
the behavior engine's distance-update flag. The loader recognizes the 19,000
sentinel and computes the distance itself; it does not replace that object
field. A nearby Mario is comfortably inside its loading distance. The
room-rendering helper is bypassed for room -1. These are source findings,
not an assumed invariant covering every outside call.

Both clearing and loading test `TIME_STOP_ACTIVE`. The new Coq theorem reads
the real global flag and executes the entire generated clearing body. If the
active bit is set, memory is unchanged. The native check additionally runs
the real time-stop object-list loop on an ordinary elevator: none of the 64
flag combinations calls its update. A frozen elevator cannot supply eleven
descents. Enabling time stop and committing its active bit are separate
scheduler steps; their connection is not replaced with a harmless-call
assumption.

The collision loader can reuse an object's transform when `throwMatrix` is
non-null. The diagnostic explicitly supplies the ordinary reset between
updates. Source inspection of `geo_process_object` shows that the reset
comes after the visibility test, including when the object is outside the
camera's view. The inactive-object branch also clears it. Merely looking
away does not skip that reset. Failure to visit the object's normal graph
node would need a separate gameplay explanation; the full rendering
connection is not proved here.

## The finite check, exactly

The harness extracts 39 C functions unchanged from the pinned source revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, recording their hashes. It decodes
the actual generated US and JP collision arrays and scripted obstacle
positions and requires agreement. It uses the real surface allocation,
partition insertion, transform, floor/ceiling/wall queries, ground quarter,
ledge-down helper, elevator descent and time-stop loop. Native address
translation is explicit; the action and object-update callbacks are observed
stubs that are never reached in the rejecting cases. No stub returns a floor.

The world fixture contains the complete 1,558-triangle Area 2 static mesh and
36 live elevator triangles. Other actors are omitted from its collision
lists. The driver supplies ordinary elevator fields, Mario without a shell,
normal collision flags and the transform reset; it does not execute the
whole behavior interpreter, action dispatcher or renderer. All arithmetic
runs with contraction and fast math disabled and undefined-behavior checks
enabled. This does not establish native-to-Clight equivalence.

For every integer base height from 128 through 4966, it checks gaps 0, 10,
100 and 110 at 225 boundary/corner/fractional combinations and all 920
integer points on the base diagonal. At the two endpoint heights it also
checks all 846,400 integer interior positions at gap 10. One time-stop
retention query brings the total to 23,855,421 in each version. The result:

- No missing floor, wrong floor owner, outward correction or low-gap stop.
- No failed floor alignment at a tested gap of at most 100.
- No ledge-down action request.
- Nine composed eleven-descent paths realign after each ten-unit descent.
  These deliberately supplied ground-quarter sequences are not controller
  witnesses or a complete gameplay scheduler.

The positive ceiling cases are reported separately: 4,770 supplied
110-unit-gap quarters stop near the top. The first base height is 4952.
For example, proposed X=-459, Y=5062, Z=-203 is corrected inward, but Y+160
reaches the ceiling at 5222. The lower-gap floor-plus-160 comparison would
not stop that quarter. Nothing in this test establishes how Mario could
enter its ground action with that already-large gap.

## Other surfaces and ordinary controls

The moving-mesh check allows all 4,096 table-indexed yaw angles of each
horizontal Grindel, all 4,096 pitch angles of Spindel, and the five remaining
stock poses: the vertical Grindel and four moving walls. It uses the actual
transform code and generated vertices. The horizontal Grindels use scale
0.9. Their transverse coordinates, Spindel's X and the walls' Z are inputs
to this geometric check; they are not a newly proved gameplay invariant.

The vertical Grindel stays far to the east in its behavior's Y-only motion.
Spindel's behavior changes Y/Z and pitch, while the moving walls change Y at
Z=-2307. The horizontal Grindels are the case needing particular care:
their behavior moves along Z when jumping and turns while stopped, but
their movement helper also performs wall checks. The nearest rotating mesh
still ends at X=-584 at its stock X=-870, outside both the base edge and the
wall-query corridor. The remote blue-coin switch and boxes have no ordinary
track into the cage. None of this substitutes for an all-owner history proof.

Idle, crouching, braking, first-person looking and ordinary punching reach
their ground-step helpers. Pausing does not update the elevator. Sign and
automatic dialogs can skip Mario's alignment, but their active time stop
also suspends this elevator; starting or finishing one needs its actual
trigger and timing. There is no nearby stock sign or NPC in the cage.
The two fresh homing Amps require Mario's displayed position within 800 of
their homes at X=1621. Even the cage's outermost X=512 leaves 1109 units of
horizontal separation. This excludes ordinary fresh activation while the
display stays in the cage, not an Amp arranged before confinement or a
different display-position history.

## Coq result and reproduction

[Area2Rank10AStallSources.v](../../proofs/Area2Rank10AStallSources.v) is consumed
by `MainTheorem.current_rank10a_ground_pound_moving_geometry_boundary`.
Its complete static census has no orientation filter: no source triangle's
vertex box intersects X=-509..510, Y=113..5141, Z=-253..766. The numerical
connection allows the interior, radius 50, base 128..4966, gap 0..110,
wall offsets -10..60 and five units of vertical surface padding. Applying
this geometric result to every accepted live wall query remains separate.
The other theorem executes the real collision-clearing body in both selected
programs and proves that active time stop leaves memory unchanged.

Run the native checks from the active project:

```sh
bash instrumentation/rank10a-live-support/run.sh
PROBE_VERSION=JP bash instrumentation/rank10a-live-support/run.sh
```

The [harness](../../instrumentation/rank10a-live-support/probe.c) and
[extractor](../../instrumentation/rank10a-live-support/build_probe.py) state
their fixtures and omissions. Outputs remain under `build/instrumentation`.
The earlier static-corridor and time-stop audit passed on 2026-09-14 in
`build/audit/20260914-211059-50uvwm4u/`: 565 registered sources, 395 of 489
proof modules in Main's import closure, and 94 standalone modules. The Main
boundary, new static-corridor theorem, new time-stop theorem and existing
low-gap execution theorem have respectively 7, 2, 7 and 7 allowed foundations.
Compilation, proof-hole, link and integration checks passed. No new axiom or
admitted proof was added. This is a selected dependency audit, not an
all-controller proof or a rebuild of every standalone module.

The matching [US/JP result receipt](../../instrumentation/rank10a-live-support/checked-results.json)
records the finite native check separately from that Coq audit.

[Back to the earlier blocked-step proof](rank10a-blocked-steps.md)
