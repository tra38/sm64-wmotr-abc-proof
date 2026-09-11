# The vertical Ink setup works conditionally in JP

The supplied vertical-only setup now has a successful original-JP test.
The first floor query misses, the retry selects the live pyramid top, Mario
processes the warp, and the top remains his remembered platform through its
explosion and the warp. The first Area-2 platform update moves him outside
the elevator. This answers the conditional usefulness question. It does not
establish that gameplay creates the supplied state or that either target
star can be collected without a new A press.

## The tested starting state

All positions are **(X, Y, Z)**. Immediately before the timer-131 top update:

| Reading | Supplied position |
| --- | --- |
| Raw collision position | `(-2200, 768, -1024)` |
| Actual position | `(-2200, 768, -1024)` |
| Stored display position | `(-2200, 1938.8648681640625, -1024)` |

The test reuses the existing declared fixture to complete the pillar puzzle
and supply these positions, with the remembered platform cleared. It inherits
idle from the game and observes quicksand depth zero. It supplies no floor,
surface owner, disappeared action or warp outcome. Thus this receipt tests
the raised-display boundary, not a negative-depth or dialog history. A future
producer must also account for the depth and other state it actually leaves.

The low point is 152 units from the upper warp centre, inside the combined
collision radius of 187. Both collision and actual position use the low
point; no separate collision-centre placement is needed. The displayed Y has
bits `0x44f25bad` and is exactly the checked top height. Its gap above actual
Y is `1170.8648681640625`.

## What the game did

The read-only query observations show that the wall calls leave the low
point unchanged. The first query returns no floor. The retry then queries
the exact high point and returns a surface owned by the top. The final
platform query in that update also returns the top; Mario's action is now
disappeared. These are observations of the actual calls, not deductions
from a later position sample.

The complete ordered lists at the first two query returns contain four
dynamic floors and 26 static floors, with matching links and surface data.
The new [Coq certificate](../../proofs/InkVerticalLiveSelection.v) checks
their order and mesh identity, evaluates the floor-test expressions extracted
from the generated US/JP code, and checks the real dynamic-versus-static
comparison. At Y=768 both lists miss; at the raised query the top wins over
the static floor at Y=1280. This closes the finite snapshot-selection question.
It is not a full Clight execution proof of traversing the live memory lists.

All 21 recorded Area-1 polls from 493 through 513 retain the top. On poll 513
the top is inactive and in the free list. The actual first Area-2 platform
call, on timer 515, still uses that retired top and moves Mario from
`(0,5500,256)` to `(365.5927734375,5500,-1096.8026123046875)`. The later short
stick continuation reaches one puzzle secret. No A press or held A is
observed after the supplied boundary. This recording does not collect a
target star, and the JP result does not transfer to US, whose entry code
clears the remembered platform.

The [probe, saved receipt and checker](../../instrumentation/jp-vertical-retry/README.md)
make this reproducible with the authenticated original JP ROM. The earlier
successful midpoint and failed lower side-face tests remain useful contrasts;
their outcomes are no longer being substituted for this new point's outcome.

## Working backward toward a gameplay producer

The upward transfer is the failed-floor retry itself. The successful test
starts idle with neutral input in Area 1; it needs no jump or ordinary upward
movement once the raised display exists. Working backward therefore means
finding where that display came from and how actual Mario becomes floorless
before an ordinary action replaces it.

A concrete arithmetic target is now checked: with depth `-0.5`, 1,318
uninterrupted sink subtractions raise display from Y=1280 to Y=1939. The
recorded floor lists still select the same top at Y=1939, just over 0.135 units
below the display and inside the four-unit contact tolerance. This is a
finite binary32 calculation, not a claim that 1,318 gameplay updates with
those conditions have been constructed. At the same X/Z, actual Y=1280
still finds the static floor. This candidate producer must also lower actual
Mario by 512 units to Y=768 without losing the display. A large display
height by itself does not solve that step.

That 512-unit drop belongs only to the proposed Y=1280 starting pose. It is
not a necessary step in every possible producer. Starting at the upper warp
centre `(-2048,768,-1024)` instead makes the proposed journey a **152-unit
westward move at the same height**, ending at `(-2200,768,-1024)`.

### Working backward to the upper warp

The successful endpoint includes more than Mario's low coordinates. The
stored display must also have the useful high position, and the earlier raw
collision position must produce an eligible warp contact at the right top
timing. The retry copies all three display coordinates. Moving actual Mario
west while leaving display X at the warp centre would therefore be a
different candidate, requiring its own floor and contact check.

For ordinary contact, the upper warp does not randomly stop Mario. Once its
non-fading handler accepts the contact, it sets the disappeared action before
ordinary action movement. That action stops Mario and snaps him to his
cached floor, then copies the result to display. Walking or crawling is not
an extra movement opportunity after that accepted contact. The pre-action
geometry preparation happens earlier, which is why the supplied successful
retry can still work before the stopping action.

Suppressing that interaction does not by itself supply a path west. If an
ordinary ground quarter-step queries the low target and finds no floor, it
returns before committing the attempted position. If a step instead leaves
the ground, the crawling and sliding callers skip floor alignment. A blocked
step can retain an incoming movement/floor mismatch, but that mismatch still
needs a producer. Alignment's floor snap changes Y; it cannot supply the
152-unit X change. Its terrain matrix is separate from the stored display
position used by the retry.

The useful search is therefore for a named change **before** the first
geometry query or before an eligible warp interaction: for example a real
platform displacement, a checked wall correction, a loss of support, or a
different action/contact history that creates and retains the mismatch.
The checked nearby west wall pushes Mario east and ignores the target point;
it is not such a producer. These are remaining obligations, not established
ways to reach the endpoint. The two coordinates alone do not establish either
reachability or impossibility for all gameplay states at the upper warp.

The [stopping-helper proof](../../proofs/InkWarpStop.v) follows the actual
US/JP helper from entry through its speed setter, floor snap and completed
display copy. It derives the speed setter's effects instead of assuming it
leaves position alone. At that copy checkpoint, actual X/Z still equal the
helper's entry X/Z, and actual Y and display Y both equal its entry floor
height. With entry X=-2048 and floor height 768, that reset cannot supply
either X=-2200 or the old high display. If the helper instead receives the
top's floor height after a successful retry, the same snap puts actual and
displayed Y at that height; stopping is compatible with the installation.
The proof retains the remaining angle-setting call without assuming its
effects. It does not establish what an earlier animation call or the later
warp preserves. Later negative-depth sinking may create a new offset. This closes the
named stopping/reset producer at its copy checkpoint, not every continuation
from the warp or every floor-alignment producer.

The source and existing proofs narrow the predecessor search:

| Earlier operation | What it can supply, and the remaining obstacle |
| --- | --- |
| Milestone dialog with existing negative depth | Repeated sinking can raise display while the dialog has no direct position refresh. The star dance refreshes display before the automatic-dialog interval; that refresh is the starting point to track. A valid reward contact and surviving negative depth are still required. |
| Waiting during the dialog | Time stop can freeze ordinary terrain updates, so waiting need not consume the top's spinning timer. It also disables remembered-platform displacement while active. The actual stop flags and object state must support that schedule. |
| Finishing the dialog | The handler changes to idle at state 25 and returns false. It does not request an idle movement pass in the same update. That leaves a possible next-update window, but does not move Mario into a floorless position. |
| Closing the dialog while standing on unchanged static support | The next first query still finds that floor. At `(-2200,1280,-1024)` the static floor is already eligible, so the raised display is not used by the retry. Waiting alone at this pose is insufficient. |
| Pre-action wall correction | The normal wall code changes X/Z, not Y. The checked west wall pushes the nearby `X=-2199` sample to `-2099`; it ignores `-2200`. That wall does not supply the proposed downward move or the required westward step. Other full wall sequences need their own check. |
| Remembered-platform movement after time resumes | This runs before object contacts and the geometry queries, making it a possible place for actual position to change before display refresh. It needs a real earlier platform capture. The top's yaw motion does not add its vertical speed directly; a low static floor supplies no platform owner. |
| Ordinary walking, crawling or sliding | A completed ground step refreshes display from the movement position. Stored speed cannot be spent before the pre-action query. A failed quarter-step query is a different event and does not substitute for this retry. |
| A retained floor-alignment mismatch | Alignment can lower actual Y after the ground step has copied a higher movement position to display. The large movement/floor disagreement and its surviving floorless endpoint remain unconstructed; this stays a separate candidate. |

An active automatic dialog also skips object interaction handlers, including
the warp. The [generated interaction-gate proof](../../proofs/InkDialogInteractionGate.v)
closes that local case. Changing to idle later in the same update cannot
retroactively process the earlier contact. A dialog-based producer needs a
usable contact after release, together with the useful gap and first miss.

The next concrete connection is a supported dialog endpoint followed by a
named pre-action change in position or support, or a reachable floor-alignment
mismatch. No such controller sequence is established. Negative depth may
still be granted while testing that transfer; producing it without A is a
separate obligation. Startup reconstruction and a new star-suffix search
are not prerequisites.

## Verification and limits

The runtime checker passes the saved receipt and rejects altered first-query,
owner, list-link, retention, first-displacement and A-input evidence. The
finite Coq certificate is consumed by `InkBackwardHistory` and the selected
main boundary. The selected pipeline audit passed at
`build/audit/20260911-112438-k20_z7no/`: 541 registered sources, successful
build and integration, no proof holes, and only existing allowed foundations
(nine for the main boundary, four for the new certificate).
Runtime success, the finite snapshot certificate, and the earlier local
Clight proofs are separate results. Clean reachability and the whole route
remain open.

The later stopping-helper audit passed at
`build/audit/20260911-134733-hxn2pcvu/`: 542 registered sources, successful
build and integration, no proof holes, and only existing allowed foundations
(nine for the main boundary, seven for the stopping theorem, four for the
finite floor certificate). It checks the new entry-to-copy connection; it
does not turn the remaining gameplay-producer question into a disproof.

[Return to the atlas](../no-a-route-atlas.md#route-rank-2)
