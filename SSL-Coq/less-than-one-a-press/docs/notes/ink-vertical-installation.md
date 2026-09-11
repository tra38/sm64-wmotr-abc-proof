# Would the raised-position setup install Ink?

## The question now

First decide whether a supplied setup is useful. We do not need to prove its
earlier controller history to answer that conditional question. Negative
depth may be granted for this test even if obtaining it used A. A successful
test would establish a conditional mechanism; recovering a clean no-A setup
would be a separate task. The grant does not make later floor selection,
warp activation or platform retention automatic.

The older [midpoint setup](ink-area2-arrival-video.md) already has a recorded
conditional JP elevator bypass. The newer vertical-only point below has not
been validated through that continuation. Its initial geometry is promising,
but coordinates alone do not specify an Ink installation.

## The vertical-only candidate

All positions are **(X, Y, Z)**. At the relevant timer-131 update, consider:

| Reading | Candidate position |
| --- | --- |
| Raw collision position, when object contacts are collected | `(-2200, 768, -1024)` |
| Actual position, after the two wall corrections and before the first floor query | `(-2200, 768, -1024)` |
| Stored display position, when a failed first query starts the retry | `(-2200, 1938.8648681640625, -1024)` |

The low point can itself overlap the upper warp: it is 152 units from the
warp centre, within the combined radius `150 + 37 = 187`, with overlapping
heights. A separate horizontal difference between collision and actual
position is therefore **not required by this contact test**. This does not
establish that the warp is active, both objects are tangible, collision-list
space is available, or the contact is processed.

The checked static mesh and timer-131 top both miss the first low query.
At the high query, the checked top face is eligible and higher than the
checked static floor. The display height is exactly that face's binary32
height, bits `0x44f25bad`; the required display/actual gap is
`1170.8648681640625`. The real retry copy transfers all three coordinates,
and the completed floor call and height-result store preserve them.
These results still leave live floor-list contents, order and ownership open.

The high point is on a different face from the recorded midpoint
`(-1862,1778,-902)`. That recording's successful retention cannot be assigned
to this new point without checking its continuation.

## An active dialog blocks the warp interaction

`ACT_READING_AUTOMATIC_DIALOG` includes the intangible flag. When the
interaction gate reads that action, it skips the entire handler loop,
including any cached warp contact. The new
[interaction-gate proof](../../proofs/InkDialogInteractionGate.v) constructs
that transition in the actual selected US/JP body, with no memory change
and no handler call. It assumes the action value at this particular read;
it does not assume that earlier calls preserve it.

Interactions run before the action loop. Consequently, an update that is
still reading the automatic dialog at the interaction gate cannot use a
change to idle later in that update to retroactively process the warp.
The conditional setup must provide an action that permits the warp handler
when interactions are checked, or establish a later valid warp contact.
This closes the active-dialog interaction case, not the post-dialog route.

## What must follow the retry

The useful sequence is: the first query fails; the retry selects the live
top; an eligible cached warp interaction selects the disappeared action;
that action snaps actual Y to the returned floor and refreshes the display;
the ordinary collision-position copy follows; and the final platform query
selects a top-owned floor within four units of Mario. That last query sets
the remembered platform. The floor retry alone does not set it.

Exact-height display removes the initial vertical contact discrepancy if the
checked top is selected. Display Y=1861 merely enters the 78-unit floor-search
allowance, leaving Mario about 77.865 units below the face until some later
operation snaps him. The disappeared action is such an operation when it
actually executes. Reaching actual Y=1202 instead already makes the checked
static floor eligible and removes the proposed failed-first-query trigger.

After initial capture, check this point through spinning timers 131 to 150,
the explosion update, the final queries and the delayed warp. An older low
side-face test captured the top initially but lost it at timer 138, so this
is a substantive test. The successful supplied midpoint has JP retention
and an Area-2 displacement; US clears the remembered platform on entry and
does not inherit that JP result.

## Next decision and evidence

The next deliverable is a conditional forward check of this exact candidate:
identify the live ordered floor results and top owner, process the warp under
an eligible action, then determine whether support survives to the JP warp
continuation. List any required remaining state explicitly. Creating the
negative seed, preserving the raised display while reaching the low pose,
and finding a no-A controller history remain open, but are not prerequisites
for this conditional test.

The position and finite-geometry results are in
[InkRetryCallCompletion.v](../../proofs/InkRetryCallCompletion.v) and
[InkVerticalRetryGeometry.v](../../proofs/InkVerticalRetryGeometry.v).
The low-point warp-contact arithmetic already appears in
`ink_geometry_kernel_checked` in [InkFallback.v](../../proofs/InkFallback.v).
The recorded retention contrast is in [the timer-131 note](timer131-surface.md).
Source review used the actual generated US/JP interaction and platform
bodies, alongside `mario.c`, `interaction.c`, `mario_actions_cutscene.c`,
`object_collision.c` and `platform_displacement.c` in the decompilation.
The local C warp file also contains a conditional TAS-only block; the
generated warp bodies used here have the ordinary radius calculation and
do not contain that block.

The selected pipeline audit passed on 2026-09-11, including the integrated
main boundary, the new dialog gate, completed retry and finite geometry.
Its report is `build/audit/20260911-103945-yu1k_vpo/`; all 540 registered
source files passed the inventory and discipline checks, and the four
assumption reports use only existing allowed foundations. This verifies the
stated local results, not the new point's installation or clean reachability.

[Return to the atlas](../no-a-route-atlas.md#route-rank-2)
