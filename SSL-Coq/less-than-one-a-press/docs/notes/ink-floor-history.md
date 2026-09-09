# Ink: tracing the retained floor mismatch backward

The surviving crawling/sliding idea does not preserve an old displayed height
through the ground-step refresh. That refresh copies the movement height it
actually reads. A later floor-alignment snap can lower movement while leaving
that refreshed display behind, so the question is whether movement was already
sufficiently far above the recorded floor. No clean controller history creating
the required 960-unit display/collision gap is established here.

The floor-history tranche keeps all memory endpoints separate. Its sources are
the generated US and JP `perform_ground_quarter_step` and
`update_mario_geometry_inputs` bodies, selected in the same linked Clight
targets as the existing backward proof. It makes no statement about execution
after undefined behavior or about corruption, arbitrary code execution, or
emulator behavior.

## The high-gap quarter-step choice

At the checkpoint after the two wall wrappers, floor query, ceiling wrapper,
water query, wall-field assignment, missing-floor gate and water adjustment,
the real quarter-step code first reads `nextPos[1]`. Its exact Float32 test is
whether that value is greater than the selected temporary floor height plus
100. If true, it reads the same Y cell again before any further memory write.
The second test is whether that Y plus 160 is at least the ceiling height.

This temporary is the **quarter step's newly queried floor height**, possibly
replaced by the water adjustment. It is not automatically the cached
`MarioState.floorHeight` that the later alignment reads. A large mismatch
against that older cached height does not, by itself, establish this test.

For this high-gap path there are only two continuations:

- A ceiling block returns result 2 without changing memory **from this
  post-water checkpoint**. It retains any incoming mismatch; it does not
  create one in this tail.
- A clear ceiling executes the generated left-ground commit and returns 0.
  This is not the grounded accepted branch. Crawling and ordinary sliding do
  not then take their grounded floor-alignment branch.

In particular, the later `floorHeight + 160` ceiling test is not an alternative
way to block this high-gap path relative to the newly queried floor. That test
belongs to the other side of the first comparison, before the grounded
`vec3f_set` call. An accepted grounded step uses the selected floor height for
its new movement Y, then records that
floor and height; its subsequent wall-angle code is a distinct continuation.
The accepted branch's full helper effects remain outside this tranche.
If the quarter query selects a different, higher floor, its lower clearance
test can still block while retaining an older, much lower cached floor. This
case is not excluded by the high-gap execution theorem.

The missing-floor return happens earlier. The full-call cut retains the
actual local allocations and six-stage prefix ending before that test.
Consequently no claim that the **whole quarter step** preserves movement,
floor, display, or object storage follows from the memory equality of a
blocked tail. The earlier query and callback effects are real parts of the
same invocation and have not been erased.

## Where the recorded floor height comes from

The earlier geometry-input routine first performs both wall-collision calls.
It then samples the resulting movement coordinates and calls the selected
`find_floor` body, passing the address of MarioState's actual `floor` field
(byte 104). The query's returned Float32 value is stored in `floorHeight`
(byte 112).

The execution cut exposes the actual movement-Y read at byte 64, the selected
`find_floor` invocation receiving it, the query's resulting memory, and the
subsequent height store. That last scalar store preserves movement Y. **The
query itself is not assumed to preserve movement Y.** Its output memory stays
explicit, as do both preceding wall calls. If the primary floor is null, the
existing retry branch may first copy display into movement and run a second
query; the primary-query result must not be silently substituted for the
later result on that path.

Thus an earlier movement/floor disagreement now points to a specific live
query and the movement value supplied to it. It is not a free-standing
"old floor" chosen independently of program execution.

## What remains to connect

To establish or exclude a clean Ink producer, the remaining work is to:

- Follow the same live Mario and object from a clean boundary through the
  wall/floor/ceiling queries, water adjustment and moving-action entry.
- Relate the queried floor, ceiling and `nextPos` values to the actual loaded
  collision geometry, including dynamic support, and prove any useful
  finite-value and separation conditions from that history.
- Relate the earlier cached floor height to the quarter step's new local floor
  height. The proof does not identify these two samples by assumption.
- Trace the caller's construction of `nextPos[1]` from movement Y into the
  actual quarter call. The source does copy that value, but a source equation
  alone does not frame all intervening collision effects.
- Carry the resulting ground-step outcome through the caller's return mapping,
  display refresh and crawling/sliding control flow, then through alignment's
  matrix tail, post-action helpers, collision copy and the next retry.

A missing-floor return can block before the high-gap checkpoint. Once that
checkpoint is reached with a high gap relative to the quarter query, only the
**high-Y ceiling block** avoids the left-ground continuation. A changed floor
selection, a prefix effect or an intervening helper can invalidate the high-gap
premise and remains explicit. The result neither proves a candidate reachable
nor excludes it universally. The capstone's whole-program refinement, route
classification and open-writer obligations remain open.

## Checked artifacts

- [Source selection and exact cuts](../../proofs/InkFloorHistorySource.v)
  authenticate both selected quarter-step bodies and the queried-floor branches.
- [Quarter-step execution](../../proofs/InkFloorHistoryExecution.v) proves
  `ifh_high_gap_requires_ceiling_block_or_leaves_ground`, with actual Float32
  tests and both Y reads.
- [Complete-call histories](../../proofs/InkFloorHistoryCall.v) retain the full
  quarter-step prefix and the geometry routine's two preceding wall calls.
- [Primary floor-query execution](../../proofs/InkFloorHistoryQuery.v) proves
  `ifh_primary_floor_query_uses_movement_y_and_stores_result` for the actual
  selected `find_floor` call and subsequent scalar store.
- [Combined backward boundary](../../proofs/InkFloorHistoryBackward.v) exports
  `InkFloorHistoryCheckedBoundary`, proved by
  `ifh_floor_history_boundary_checked`, including the actual missing-floor
  return or continuation to the water-adjusted tail.

All five leaves pass the active `pipeline/check.sh` wrapper with Coq 8.16.1,
CompCert 3.15 and the `sm64-item-proof` switch. These checks establish the local
execution cuts above, not the still-open clean-history connections.

[Return to the Ink approach in the atlas](../no-a-route-atlas.md#route-rank-2)
