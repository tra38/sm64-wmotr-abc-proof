# Rank 10A: can blocked steps leave Mario behind as the elevator descends?

The [follow-up check of all four proposed causes](rank10a-live-support.md)
now runs real collision loading and ground quarters. It finds no missing
base or outward correction in the finite sample. It also distinguishes a
real ceiling stop with an already-supplied 110-unit gap from a way to create
that gap. The results below remain the earlier conditional Coq boundary.

## Result

The ordinary ceiling explanation now has a checked conditional exclusion.
The static ceilings over the elevator are too high to stop a grounded
movement quarter, and the elevator's own underside is rejected by the
ordinary ceiling query. The real US/JP low-gap quarter-step proof reaches
the floor-alignment code under the stated loaded-height conditions. This
does not yet exclude a missing live floor, a query outside the checked
interior, another moving surface, or an earlier action/position change.

No repeated blocked run, ground-pound entry or clean escape was constructed.
Nor are all three proposed gameplay invariants proved. Their status is:

| Proposed invariant | Verdict | Remaining connection |
|---|---|---|
| Corrected queries stay inside the bucket and return its live base. | Geometry proved; gameplay invariant still open. | Actual wall-corrected coordinates, live loading and floor-list traversal must supply the base answer. |
| While grounded, the pre-action and quarter-step gaps stay at most 100. | Same-base descent checked; the low-gap ceiling-stall case is now conditionally excluded. | Connect the query answers and floor-alignment effects across actual complete frames, including missing-floor returns and action changes. |
| Permitted airborne episodes cannot hand off to freefall. | The ordinary slide-kick episode and rollout-ending cases are checked, with their stated conditions. The entire family is open. | Cover different launches, hard landings, interactions, support changes and intervening effects. |
| Mario is always at most 100 above his floor, including airborne actions. | False for the existing checked vertical episode. | This stronger claim must not be used. It is not a clean-controller counterexample to the whole route. |

The last refutation is now explicit in Coq: sample 11 of the checked
ordinary slide kick has a gap of 142. The first bounce reaches 206 elsewhere
in that same certificate. Neither gap supplies that action's required
combination of timer greater than 30 and gap greater than 500.

## Where a stopped ground step can occur

`perform_ground_quarter_step` first corrects the proposed position against
walls, queries the floor and ceiling, and checks water. The existing proofs
retain the actual effects of those calls; they do not assume the calls are
harmless. The relevant branches then run in this order:

1. A null floor returns the stopped-step result before floor alignment.
2. If proposed Y is more than 100 above the returned floor, proposed Y plus
   160 must be below the returned ceiling to leave the ground. Otherwise it
   returns the stopped-step result.
3. With the smaller gap, floor height plus 160 reaching the ceiling also
   returns the stopped-step result.
4. Otherwise the code calls `vec3f_set` with the selected floor height as Y,
   stores the floor pointer and height, and only then handles the final wall
   response.

The new theorem proves the previously missing third-versus-fourth execution
split. A taken ceiling return has no memory effect from that checkpoint.
A non-taken return reaches the actual alignment continuation. The theorem
does not by itself complete `vec3f_set`, the rest of the quarter, or the
outer frame. Its name “reaches alignment” refers to this precise checkpoint.
The existing full-call cut ties that checkpoint to the real quarter body.

Thus the final wall response alone cannot explain skipping alignment.
A proposed stall must identify an earlier return or another state change.

## Check every ceiling over the interior

The domain is the same integer-query interior as the earlier base proof:
X from -459 through 460 and Z from -203 through 716. It is a certificate
domain, not an assumed invariant of Mario's actual wall-corrected position.

The complete 1,558-triangle static mesh has 18 downward-facing candidates
whose bounding boxes overlap that interior. All are horizontal. Their
heights are 5222, 5734 or 6144. Coq proves the full census and the lower
height bound for every point in every candidate's vertex box; this is not a
sampled set of Mario positions.

The base's nominal maximum is 4966. Even the lowest static ceiling leaves
256 units of headroom there, and the gap increases during descent. The new
binary32 proof allows any finite returned floor height from 0 through 5000
and any finite returned ceiling height at least 5222. Under those bounds,
the real low-gap ceiling test is false and execution reaches the alignment
continuation. The default ceiling answer, 20000, also meets that bound.

The elevator mesh has only two downward faces over its local interior:
faces 4 and 6, both at local Y=-50. The ceiling wrapper asks at floor height
plus 80. The list query rejects a ceiling when query Y is more than 78 above
it. For an ordinary base-relative query, the underside is about 130 below
the query, so it is rejected before it can be returned.

That last statement now has an actual US/JP execution proof. With a base
reference from 0 through 5000, integer query Y between base+79 and base+81,
and finite underside height between base-51 and base-49, the generated
rejection expression has a positive difference between 50 and 54. Its
branch executes `continue`, preserving memory and locals. The actual
ceiling-list callee is resolved in both selected programs. The bounds are
explicit query/plane conditions, not a proof that every live caller supplies
them.

An independent source-data checker also computes the loaded static plane
heights and checks the translated underside at all 4,839 integer base
heights from 128 through 4966 in both versions. The rejection difference is
52 throughout that finite check. These computations do not establish the
contents of a live floor or ceiling list.

## What remains of the repeated-stall proposal

The platform helper does not automatically add the elevator's vertical
velocity to Mario's Y. Source inspection of `apply_platform_displacement`
shows X/Z translation and an optional rotation path; with zero angular
velocity, Y passes through unchanged. Floor alignment therefore matters.
This observation is not a new whole-helper preservation theorem.

If Y were held at 4000 while the selected base descended ten per update,
the gap would be 100 after ten updates and 110 after eleven. That arithmetic
is checked, but holding Y is the missing gameplay event. Under the ordinary
query conditions above, a low-gap quarter cannot keep taking the early
ceiling return even once. Repetition cannot be obtained from that return
without first breaking one of those conditions.

The concrete alternatives to resolve across full gameplay histories are a missing/rejected live base, a
wall correction that moves the query outside this interior, another live
dynamic ceiling, a differently positioned Mario, or an intervening action
or interaction. The static geometry does not supply an interior floor hole
or a low ceiling. Deriving the actual lists and corrected queries would
turn these conditional exclusions into a stronger gameplay invariant.
Ground-pound entry and a useful sideways departure remain open. The atlas's
subjective 2–5% estimate is unchanged.

## Checked deliverables

- [Ground-quarter execution and ceiling census](../../proofs/Area2Rank10ABlockedStep.v).
- [Actual ceiling-list underside rejection](../../proofs/Area2Rank10ACeilingReject.v).
- [Independent source-data checker](../../instrumentation/rank10a-ground-pound/check_blocked_steps.js).

Both boundaries are consumed by
`MainTheorem.current_rank10a_ground_pound_moving_geometry_boundary`.
The selected audit passed on 2026-09-13 in
`build/audit/20260913-232440-dlpk1plq/`: 564 registered sources, 394 of 488
proof modules in Main's import closure, and no proof-hole, link or integration
problems. The Main boundary, low-gap execution and underside-rejection
reports each have seven existing allowed foundations; the static-ceiling
height theorem has two. No new axiom or admitted proof was used. This was a
selected dependency build, not a rebuild of all standalone modules.

[Back to the backward support question](rank10a-backward-support.md)
