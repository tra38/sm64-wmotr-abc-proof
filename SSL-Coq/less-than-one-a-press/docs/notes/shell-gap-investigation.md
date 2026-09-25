# Shell gap investigation — 25 September 2026

No way to make the shell's own offset grow to 1170.8648681640625 units was
found. The normal grounded offset is 45; the airborne offset is 42. Walls
do not provide a way to add those amounts repeatedly without the intervening
display refresh. This is a source review plus a bounded native diagnostic,
not a new universal Coq exclusion of every shell-assisted history.

The target is **display Y minus movement Y**, at the useful checkpoint. At
movement Y=768, the ordinary shell endpoints are display Y=813 or 810,
not 1938.8648681640625. A separate downward movement would need another
1125.8648681640625 units after a ground offset, or 1128.8648681640625 after
an air offset, while preserving the display. Collision position and warp
acceptance remain separate requirements. These numbers are exact at this
anchor; they are not a claim that binary32 subtraction yields exactly 45
at every possible magnitude.

## Mechanisms checked

| Proposed way to grow the gap | What the stock source does | Verdict for shell amplification |
| --- | --- | --- |
| Run into a wall on the ground | `perform_ground_step` copies State to display after its quarter-step loop, including early wall-stop results. The caller then adds 45; the hit-wall case dismounts and selects backward ground knockback. | No accumulating shell lift on this path. |
| Hit a wall in the air | `perform_air_step` copies after its loop; the shell caller then zeros forward speed for the wall result and adds 42. | Wall contact does not skip this refresh. |
| Lose the floor inside movement, hit a ceiling, or stop quarter steps early | The quarter-step return changes the result or ends the loop, not the whole step function. Both complete step functions still reach their display copy. | A quarter-step miss is not the pre-action retry. |
| Fall from a ledge or land repeatedly | Ground-to-fall and air-to-ground changes are followed by that caller's one offset and `return FALSE`. The action loop does not immediately repeat the new shell action in that invocation. | Not 45+42 in one pass, and not an accumulating counter. |
| Press A or Z on a ground shell | Both returns occur before movement and before the +45 write. A changes to shell jump; Z dismounts into crouch slide. | Early exit preserves an incoming offset but adds none. A is also outside a no-new-A route. |
| Other early cancellations | Water, stomp, squish and health cancellations happen before the shell action. The selected replacement action needs its own writer analysis. | No extra shell addition on the canceled path; not a blanket bound on the replacement action. |
| More speed, backward hyperspeed or stronger turning | Speed/turning affect movement and tilt angles. The display-Y addition remains the literal 45, or 42 in air, after refresh. | No speed multiplier on the shell's vertical offset. Invalid float-to-integer conversions are outside the defined model. |
| Shell plus negative quicksand depth | A continuing ground shell resets depth in `mario_update_quicksand`; the normal air dispatcher also resets it before the shell action. | Riding does not preserve a negative seed through these resets. A prior interruption must be analyzed separately. |
| Water surface riding | The shell can substitute the water pseudo-floor; actual height alignment still precedes the ordinary display copy. | Changes the support height, not an extra retained shell offset. |
| Underwater shell and water pitching | `act_water_shell_swimming` calls the common swimming step; water movement copies before the separate pitch offset. Its constructor checks the underwater-shell behavior, a different object from the ordinary rideable shell. | No basis for adding land-shell and water offsets together. Stock availability and subsequent water histories are separate checks. |
| Remount, dismount, shell actor motion or more shells | Successful mounting sets object references and action; the riding shell actor calls `obj_copy_pos(o, gMarioObject)`, copying Mario **into the shell**. Dismount signals the shell and clears the ridden pointer. | The shell actor is not a platform that drags State downward; no per-shell offset stack was found. Live receiver/ownership conditions still matter. |
| Floor alignment or a downwarp during the ground step | Any changed State height is the height the final step copy uses. | A large movement before that copy is erased as a gap. |
| Moving support after the shell display copy | The platform phase can move actual Mario while preserving display and collision, as already proved conditionally. | A separate producer could enlarge the gap; this investigation does not exclude a useful live support/timing combination. |
| Reward/dialog, damage, warp, pre-action recovery or another later writer | An interruption can retain a previous small offset. The next frame's failed-first-floor recovery copies display into State, consuming that vertical disagreement at the copy. An action skipped because the floor stays null does not execute another shell offset. | Preserving 45 is not creating 1170.865. A separate State drop, negative-depth effect or other writer must supply the missing amount before the relevant checks. |
| Camera/model tilt, particles and the shell's drawn height | These are not automatically Mario's stored display Y, State Y or collision Y. | A larger-looking pose is not an Ink gap. |

The review follows pinned `mario.c`, `mario_step.c`,
`mario_actions_moving.c`, `mario_actions_airborne.c`,
`mario_actions_submerged.c`, `interaction.c` and `behaviors/koopa_shell.inc.c`.
The stock ordinary shell source in SSL Area 1 is the box at (5840,940,2500).
This is a catalog of the identified shell mechanisms, not a proved exhaustive
classification of every controller history or every aliased writer.

## What was checked mechanically

The [native branch diagnostic](../../instrumentation/shell-gap/README.md)
uses unchanged stock callers and movement-loop/copy code. In each US/JP
build, 7760 supplied outcome/height cases and their repeated calls retained
only 42 or 45, with two early-exit checks adding nothing. The driver explicitly
replaces other helpers and terrain outcomes; these are not controller replays.
Some supplied outcome sequences are unreachable and some suffixes are skipped
by early loop termination. The result is a test of the caller ordering under
those supplied effects, not evidence that all live callees preserve positions.

Existing Coq results already establish the complete ground call's copy
checkpoint (`igb_completed_ground_call_reaches_display_refresh` and
`ipg_whole_ground_call_has_completed_copy_checkpoint`), shell source shapes
in `ClightFacts.v`, and the explicitly modeled normal shell frame in
`InkFallback.v` / `CleanJPGraphicsGap.v`. Those are reused, not promoted into
a whole live shell theorem. This batch adds no Coq module or assumption.

## Where to leave case 17

Keep **Insufficient alone — source review and finite branch check**.
Do not promote every shell-assisted continuation to **01 Already proved**.
The ordinary copy is already proved within its stated scope; the new branch
diagnostic does not discharge the helper frames or the later gameplay writer
coverage. To revisit the shell as an installer, identify the extra downward
State writer and the interval that preserves the small offset. Repeating wall
hits or increasing speed alone is not such an explanation. The atlas estimate
stays below 1%, a subjective judgment, not the diagnostic's success rate.
