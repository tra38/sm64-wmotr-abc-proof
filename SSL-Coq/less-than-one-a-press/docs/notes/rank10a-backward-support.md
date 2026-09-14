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

## Invariants for entry, and what walking off would mean

Walking off a ledge is one way to reach ordinary freefall, not the only
ground-pound predecessor in the game. The [generated action census](rank10a-ground-pound-moving-geometry.md#eligible-predecessors)
also contains jump, flying and ceiling-hanging actions. Their existence in
the source does not make them reachable inside this elevator without a new
A press. Freefall itself can start when support changes beneath Mario;
there need not be a literal edge beside him.

The most useful proposed invariants depend on which action is running:

| Proposed invariant | What it would exclude | What is checked, and what is missing |
|---|---|---|
| The actual floor queries after wall correction stay over the base and return that live base. | An interior hole or an unexplained switch to a much lower floor. | The base covers the checked interior, and the floor-choice proof preserves a successfully returned higher base. Live loading, traversal, query coordinates and acceptance remain open. |
| While grounded, both the pre-action query and each attempted movement quarter keep Mario at most 100 units above the selected floor. | The ordinary off-floor input and the walking step's leave-ground branch. | The nominal elevator cycle and same-base height tests are checked. Preservation through actual movement, blocked returns and intervening updates is not. |
| Each permitted airborne episode has its own bounds on height, velocity, timer and bounce state. | The corresponding height- or timer-based handoff into freefall. | The ordinary slide-kick flight and bounce miss their freefall gate, and rollout endings preserve their action. Other launches, collisions, interactions and support histories still need coverage. |

These are proposed proof obligations, not newly established gameplay
invariants. A universal 100-unit height bound would be false even in the
ordinary checked slide-kick episode: its first flight and bounce reach gaps
of 142 and 206 at the timeout checks. The grounded bound must therefore be
kept separate from the airborne bounds. A complete exclusion also needs the
actual action transitions to preserve the appropriate case from the accepted
start, including interactions; assuming that preservation would assume away
the central question. Breaking one proposed invariant would only identify a
candidate. It would not by itself prove ground-pound entry or escape.

The pre-action argument also needs the current frame's input reset and any
other input writes. The existing false-guard proof says that this test does
not add the off-floor flag; it does not clear a previously supplied flag.

The walking code makes the geometric problem concrete. Each movement quarter
first corrects its proposed position against walls and queries a floor. A
null floor returns a stopped-step result. With a floor present, leaving the
ground requires the proposed Y to exceed the returned floor height plus 100,
and proposed Y plus 160 to be below the ceiling. The comparisons use the
game's Float32 arithmetic. The walking action responds to the leave-ground
result by requesting ordinary freefall. A later eligible Z check can then
request ground pound, subject to the earlier action checks.

The existing [source cuts](../../proofs/InkFloorHistorySource.v),
[missing-floor proof](../../proofs/InkFloorHistoryBackward.v) and
[high-gap proof](../../proofs/InkFloorHistoryExecution.v) already expose those
real US/JP branches. This review reuses them; it adds no new Coq theorem and
does not construct the full walking-to-ground-pound continuation.

There is no ledge within the checked bucket interior: the flat base covers
it, and the base's outer edge lies beyond the inner walls. Simply walking
around on that base cannot manufacture the required drop. Reaching the rim
or crossing the enclosing wall first requires its own explanation, so it
cannot be silently supplied as the starting point of the escape.

One precise remaining case is an early blocked movement return. Ordinary
accepted ground movement snaps Y to its selected floor before processing
the final wall response, so merely pushing against a wall is not a reason
to retain the old height. A null-floor or insufficient-headroom return can
occur before that snap. To use this, a real continuation would have to keep
Mario from reanchoring while the base continues descending, accounting for
the next pre-action query, platform movement, action changes and later
movement attempts. Neither that repeated obstruction nor its impossibility
has been established. This is distinct from the pre-action failed-floor
retry, which has its own display-copy recovery.

The next useful invariant proof should cover those actual blocked and
accepted ground steps with the live base, then connect the separate
airborne cases. Rank 10A remains open and its subjective 2–5% estimate is
unchanged.

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
