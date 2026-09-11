# Rank 10A: work backward through a change of support

## Result

The next missing event is more specific than "use a different floor."
Inside the elevator, its base has no geometric hole, and the static floors
below it cannot displace a successfully returned, higher base in the checked
floor-selection segment. A useful lost-support entry must explain why the
live base is absent or rejected, why Mario leaves this interior, or what
other gameplay event changes his position or action.

This does not supply a ground pound or disprove every Rank-10A route. It adds
a complete finite source-mesh certificate and a conditional execution of the
actual US/JP selection code. No new controller run is claimed.

## The backward chain

1. Ground-pound startup has the already-checked height window, but starting
   the action and leaving sideways are separate requirements.
2. Ordinary freefall accepts Z, provided B does not take priority. The
   existing airborne census does not make rollout, jump kick or the initial
   upper-entry fall eligible just because Mario is above a floor. Source
   inspection confirms that a normal rollout or jump-kick wall hit stops
   horizontal speed without changing to freefall.
3. For a grounded Mario, the existing same-base proof excludes the ordinary
   elevator cycle as a producer of the more-than-100-unit gap needed by the
   off-floor input. The lost-support proposal therefore needs an earlier
   change in the actual selected floor or position.
4. The new certificate checks the alternative static supports and the
   elevator's base. It then follows the real selection code from the two
   loaded height answers through the floor-pointer output store.
5. The remaining predecessor is the first live query that fails to return
   the base under the ordinary conditions, or a different concrete action or
   position change. Granting a freefall action would skip this missing step.

## What the geometry certificate covers

The query box is X = -459 through 460 and Z = -203 through 716. These are
integer coordinates strictly between the elevator's inner wall planes at its
stock horizontal origin. This is a domain of the certificate, not a claim
that every reachable Mario position stays in it. Wall corrections and
signed-16 conversion still have to put a real query inside this box.

The scan reuses the generated US/JP Area-2 collision stream and the existing
Coq parser. It examines all 1,558 triangles, using positive geometric normal
Y as a conservative superset of floors. Of the 534 such faces, only 34 have
X/Z bounding boxes intersecting the query box. Every vertex of those 34 is
at or below Y = -101. The theorem covers every point in each candidate's
vertex box, not a finite sample of Mario positions.

The complete 36-triangle elevator initializer has only two upward faces
overlapping the corresponding local interior. They are base faces 10 and 11,
at local Y = 0, and together cover the entire query box, including their
shared diagonal. The eight upper-rim faces do not overlap this interior.
These facts do not establish a live transform, surface allocation, list
entry, or successful floor query.

## What the actual selection code now establishes

In `surface_collision.c`, `find_floor` queries the dynamic list and then the
static list, handles the optional intangible-floor retry, and finally compares
the two height answers. The new proof extracts that final choice and its
immediately following output store from the generated US/JP bodies.

Its explicit conditions are the actual local-variable bindings, loaded
finite heights, dynamic-floor pointer, output pointer, and two successful
ordinary memory stores. When the dynamic answer is at least Y = 128 and the
static answer is at most Y = 0, the segment reads those heights, takes the
dynamic branch, stores its height, and writes exactly its floor pointer to
the caller's output. This extends a numerical comparison to the actual
reads, branch and pointer store. The later debug-counter update and function
return are outside this checkpoint.

The static vertex bound and the loaded-height bound are deliberately
separate: the proof does not silently equate ideal geometry with a live
rounded plane calculation. Deriving that calculation's bound is still
required. Likewise, Y = 128 is the normal elevator's lowest base height,
but the live dynamic answer must still be shown to belong to that base.
The theorem assumes no intact-list or whole-frame preservation predicate.

## The next concrete predecessor to check

Follow one actual dynamic query backward through surface loading and the
earlier position updates. Establish the live elevator identity and transform,
its base's presence and order in the queried cell, query coordinates and Y
eligibility, and the floor traversal's real answer. Account for other dynamic
owners and any earlier wall correction or position change. A failure of one
of these checks must identify a gameplay event, not merely an unfinished
proof.

The source gives a focused starting point. The elevator behavior calls its
movement routine and then `load_object_collision_model`, with collision
distance 20,000. Loading tests time stop, distance and room status. However,
`clear_dynamic_surfaces` also skips clearing when it observes active time
stop. Thus a loader skip alone does not establish that the base disappeared:
a timing proposal must follow the flag at both calls and any intervening
changes. These are source observations, not a proved scheduler history.

If a genuine loss of support survives, then connect the resulting eligible
airborne action, Z input, headroom, moving-elevator height window and sideways
departure. Another interaction or support outside this interior remains a
separate candidate. Clean reachability and the whole route remain open; this
tranche does not justify a new numerical success probability.

## Reproduction

From the active SSL project:

```sh
node instrumentation/rank10a-ground-pound/check_support.js
bash pipeline/build.sh audit-build AUDIT_VO_TARGETS=proofs/Area2Rank10ASupportChange.vo
```

The implementation is [Area2Rank10ASupportChange.v](../../proofs/Area2Rank10ASupportChange.v).
Its geometry and selection-execution results feed
`current_rank10a_ground_pound_moving_geometry_boundary` in Main.

The selected pipeline audit passed on 2026-09-11 at
`build/audit/20260911-170533-9ad_wzuv/`, using Coq 8.16.1 and CompCert 3.15
in the installed `sm64-item-proof` switch. It checked 545 registered sources,
compiled the new module and Main, and passed proof-hole, link and integration
checks. The Main boundary, selection-execution theorem and combined support
boundary each use seven existing allowed foundations, with no new axiom.
The offline source checker and atlas paragraph/link checks also passed.

The progress is the new static-support restriction, base coverage and actual
read-to-output selection segment on the Main boundary. The old live same-base
premise has not been discharged: source geometry and supplied list answers
still need their execution connection. Neither clean reachability nor the
whole route is closed by this audit.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a)
