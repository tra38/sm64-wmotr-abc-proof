# Where a useful position split could come from

Updated 24 September 2026. The full catalog is also on the private [Fine Print site](https://pyramid-proof-fine-print.tra38.chatgpt.site/#split-catalog).

The proposed method is sound: classify the actual ways the game can write or retain the three positions, then eliminate the ones SSL cannot use and follow the remaining ones to the chosen warp checkpoint. An enemy being absent can eliminate its ordinary spawn path. It cannot eliminate a different SSL actor using a shared helper.

This catalog groups whole-game source mechanisms into 27 cases. It includes actual writers, ways to preserve a gap, and tempting false positives. It is not a list of 27 demonstrated Ink routes or a completed classification of every live memory write.

## What counts as useful?

**State** is MarioState.pos, **collision** is MarioObject's raw oPosX/Y/Z, and **display** is the stored header.gfx.pos vector. A rendered animation or camera offset is not necessarily a change to that display vector. The target is immediately after the upper nonfading SSL warp returns success, still in Area 1 and before act_disappeared. State = display with different collision coordinates qualifies; all three need not differ. Useful final Area-1 top capture is reported separately.

Ordinary controller gameplay and defined, in-bounds execution remain the scope. The negative-depth and valid-reward grants are diagnostic assumptions, not a grant of the useful split, failed first query, contact or timer. Arbitrary state injection, memory corruption and debug-action injection are not routes in this catalog.

## The result so far

Chuckya and King Bob-omb's shared anchor, Dorrie's lift, the LLL/BitFS tilting pyramids, Hoot, Heave-Ho, the named bullies, Bowser's shockwave, whirlpools and butterflies have no stock Area-1 selector in the checked paths. The new source checks supplement the existing Chuckya/King Bob-omb and butterfly proofs. These are selector exclusions, not an assumed all-gameplay object-lifetime invariant.

SSL still has ordinary geometry correction and floor retry, platform movement, floor alignment, palm-tree pushes, interactions, a cannon, Tweesters, a shell, quicksand, dialogs and an oasis. A particularly concrete case is normal cannon firing: it moves State and returns before the display copy, but that branch requires an A press. Ordinary confinement refreshes display. Swimming offsets also cannot be excluded just by calling SSL a desert.

The accepted-warp action tail preserves any gap it receives. The successful supplied JP Ink fixture remains conditional; the clean replay has all three records equal. No new clean installation or all-history impossibility has been established. Atlas route estimates are unchanged; no probability is assigned to these source rows.

## The catalog

| # | Situation | SSL / current verdict |
| --- | --- | --- |
| 01 | [Ordinary walking, falling and action movement](#split-ordinary-step) | Present Â· timing matters |
| 02 | [Wall corrections and the failed-floor display retry](#split-geometry-retry) | Present Â· central open producer |
| 03 | [Floor alignment and animation translation](#split-floor-animation) | Present Â· open |
| 04 | [Ordinary moving-platform displacement](#split-platform) | Present Â· preservation proved |
| 05 | [Chuckya and King Bob-omb's held-Mario anchor](#split-chuckya-anchor) | Stock selectors absent |
| 06 | [Dorrie's neck lift](#split-dorrie) | Stock selectors absent |
| 07 | [LLL and BitFS tilting inverted pyramids](#split-tilting-platform) | Stock selectors absent |
| 08 | [Riding Hoot](#split-hoot) | Stock selectors absent |
| 09 | [Palm-tree and object pushes](#split-push) | Present Â· open |
| 10 | [Enemy bounce, knockback and environmental forces](#split-bounce) | Present Â· effects differ |
| 11 | [Heave-Ho, bullies and Bowser's shockwave](#split-absent-launch) | Stock selectors absent |
| 12 | [Trees, poles, ledges and hanging](#split-attachments) | Present / geometry-dependent |
| 13 | [Cannon entry and confinement](#split-cannon) | Present Â· action-limited |
| 14 | [Tweester / tornado capture](#split-tornado) | Present Â· timing matters |
| 15 | [Water entry, swimming pitch and surface bobbing](#split-water) | Present Â· open transfer |
| 16 | [Whirlpool capture](#split-whirlpool) | Stock selectors absent |
| 17 | [Shell riding and the graphical offset](#split-shell) | Present Â· bounded local results |
| 18 | [Quicksand depth and a stalled reward dialog](#split-quicksand) | Present Â· conditional producer remains open |
| 19 | [Signs, NPC dialog and skipped refresh](#split-dialog) | Present Â· preservation is not production |
| 20 | [Doors, teleports, instant warps and level entry](#split-warp-reset) | Mixed Â· reset/transfer barrier |
| 21 | [Butterfly's temporary collision-position perturbation](#split-butterfly) | Stock selectors absent |
| 22 | [Endgame and other scripted placements](#split-cutscene) | Not stock Area-1 action entry |
| 23 | [Debug free movement](#split-debug) | Outside selected stock gameplay |
| 24 | [Renderer, mirror Mario, camera and local vectors](#split-render) | Not a Mario-record producer by itself |
| 25 | [Generic object movement, spawning and slot ownership](#split-generic-objects) | Present Â· receiver proof required |
| 26 | [Ordinary synchronization, time stop and skipped updates](#split-copies-pauses) | Present Â· preservation/eraser |
| 27 | [Signed-16 query aliases and different samples](#split-query-alias) | Present code Â· not a record writer |

<a id="split-ordinary-step"></a>

### 01 — Ordinary walking, falling and action movement

**Position effect.** State moves first; action helpers usually copy it into display, and the Mario callback later copies it into collision.

**Whole-game prerequisite.** Walking, sliding, jumping/falling, damage movement and ground-pound startup use this machinery in every course.

**SSL Area 1.** SSL Area 1 has ordinary ground and air movement. Availability of a particular airborne action without a new A press is a separate question.

**The next copy or check.** The warp interaction runs before the ordinary action loop. Movement later in that pass cannot cause a split at the earlier accepted-warp return. Earlier updates still need their last copy traced.

**What is established.** The normal ordering is read from stock source; existing copy and ground-step proofs cover named segments. It is not a proof that every action always refreshes display.

**What is still needed.** Close an actual earlier action segment and its intervening copies; a large stored speed is not itself a position change.

Stock source: [perform_air_quarter_step](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_step.c#L388); [perform_ground_step](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_step.c#L322); [perform_air_step](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_step.c#L610); [perform_water_step](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_submerged.c#L167); [act_ground_pound](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_airborne.c#L918); [stationary_ground_step](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_step.c#L236); [stop_and_set_height_to_floor](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_step.c#L223).

Related atlas ranks: 2, 5, 13B, 18.

<a id="split-geometry-retry"></a>

### 02 — Wall corrections and the failed-floor display retry

**Position effect.** Pre-action wall correction moves State. If its floor lookup misses, the retry copies display into State while collision can remain low.

**Whole-game prerequisite.** No special enemy is needed: geometry preparation runs before interaction.

**SSL Area 1.** This is the mechanism that makes the supplied SSL Ink setup work. The low actual/collision pose and high display must already coexist at the right top timing.

**The next copy or check.** Both wall corrections and the first floor query precede warp interaction; the retry can leave State = display â‰  collision at acceptance.

**What is established.** The real copy-to-second-query segment and finite/top-selection certificates are proved separately; the supplied JP installation has a replay. A clean gameplay predecessor remains open.

**What is still needed.** Derive the wall-corrected first miss, eligible raised display, live top and low collision contact together.

Stock source: [update_mario_geometry_inputs](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L1314); [resolve_and_return_wall_collisions](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L521); [find_floor](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/surface_collision.c#L513).

Related atlas ranks: 1, 2, 3, 13A.

<a id="split-floor-animation"></a>

### 03 — Floor alignment and animation translation

**Position effect.** Alignment can write State.Y from a remembered floor without itself replacing stored display. Animation translation can move State in X/Y/Z.

**Whole-game prerequisite.** Ground actions, ledge/door animations and support changes can produce intermediate disagreements.

**SSL Area 1.** Ordinary floor alignment and animation helpers exist in Area 1. A retained large floor mismatch is a candidate, not an established seed.

**The next copy or check.** These writes mostly occur in the action phase; follow the return and the next geometry pass rather than stopping at the assignment.

**What is established.** Conditional ground-reset and alignment results already exclude their stated cases. They do not cover every earlier action or remembered floor.

**What is still needed.** Find or exclude a concrete mismatch that survives the following action copy and is consumed by the pre-action retry.

Stock source: [align_with_floor](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_moving.c#L88); [update_mario_pos_for_anim](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L207).

Related atlas ranks: 2, 5, 13B.

<a id="split-platform"></a>

### 04 — Ordinary moving-platform displacement

**Position effect.** A platform can move State while preserving display and collision throughout the complete platform phase.

**Whole-game prerequisite.** Translation and rotation of an actually retained supporting object.

**SSL Area 1.** SSL has moving Tox Boxes and the pyramid top. Availability as Mario's support at the needed phase is not automatic.

**The next copy or check.** This phase precedes the next Mario update. The support check can clear the platform; platform movement alone cannot lower the collision record used for contact.

**What is established.** The full US/JP platform phase preserves both other records under its stated ordinary Object-pool conditions. The preceding missing/distant-floor clear is also proved.

**What is still needed.** Supply an earlier low collision pose with usable support and raised display, then connect floor loss and timing.

Stock source: [set_mario_pos](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/platform_displacement.c#L81); [apply_platform_displacement](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/platform_displacement.c#L91); [apply_mario_platform_displacement](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/platform_displacement.c#L171); [update_mario_platform](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/platform_displacement.c#L22).

Related atlas ranks: 1, 2, 5A, 6.

<a id="split-chuckya-anchor"></a>

### 05 — Chuckya and King Bob-omb's held-Mario anchor

**Position effect.** The shared anchor copies the anchor's raw position, plus its graphical Y offset, into Mario's stored display; the grabbed action can later copy display into State.

**Whole-game prerequisite.** A Chuckya or King Bob-omb parent must create and operate its Mario anchor.

**SSL Area 1.** Neither parent has a stock Area-1 regular, macro or special selector. Existing proofs identify both parent scripts and the anchor call chain.

**The next copy or check.** An anchor is a real display writer, unlike a mere launch velocity. Its usefulness elsewhere still depends on when collision and State are copied.

**What is established.** Existing US/JP source proofs exclude these stock selector paths and enumerate the shared helper's callers. This is not a theorem that arbitrary dynamic spawning is impossible.

**What is still needed.** For a universal exclusion, connect the stock spawn/ownership history to those checked selectors; do not assume a new Chuckya in SSL.

Stock source: [common_anchor_mario_behavior](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/chuckya.inc.c#L17); [obj_set_gfx_pos_at_obj_pos](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_helpers.c#L1881); [act_grabbed](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L656).

Related atlas ranks: 21, 2.

<a id="split-dorrie"></a>

### 06 — Dorrie's neck lift

**Position effect.** Dorrie calls the State-position setter using Mario's collision position and the neck displacement.

**Whole-game prerequisite.** A live Dorrie head-lift behavior.

**SSL Area 1.** Dorrie has no stock SSL selector.

**The next copy or check.** The exact setter-call census distinguishes this special lift from ordinary platform displacement.

**What is established.** New US/JP checks prove Dorrie's selector absence and that its head lift is one of exactly three direct callers of set_mario_pos across the generated corpus.

**What is still needed.** A course import would need to survive real initialization; the catalog does not grant retained foreign actors or state.

Stock source: [dorrie_raise_head](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/dorrie.inc.c#L3).

Related atlas ranks: 5, 5A.

<a id="split-tilting-platform"></a>

### 07 — LLL and BitFS tilting inverted pyramids

**Position effect.** Their custom rider correction calls the State-position setter.

**Whole-game prerequisite.** The tilting inverted pyramid behavior used in LLL or BitFS.

**SSL Area 1.** Neither behavior selector occurs in stock SSL. These are not SSL's exploding pyramid top.

**The next copy or check.** A different behavior with a similar shape is not the same position-writing callback.

**What is established.** New US/JP checks exclude both selectors and include their shared callback in the exact three-caller census.

**What is still needed.** Only an actual legal spawn or import of this behavior would reopen this named mechanism.

Stock source: [bhv_tilting_inverted_pyramid_loop](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/tilting_inverted_pyramid.inc.c#L65).

Related atlas ranks: 5, 5A.

<a id="split-hoot"></a>

### 08 — Riding Hoot

**Position effect.** The riding action anchors State to Hoot, then writes display from State.

**Whole-game prerequisite.** Hoot and a successful Hoot interaction.

**SSL Area 1.** No Hoot selector exists in stock SSL.

**The next copy or check.** The action's temporary mismatch must survive its own copy before it can help a later warp.

**What is established.** New US/JP source checks exclude Hoot selectors; source inspection identifies the position-copy sequence.

**What is still needed.** A global action-history proof must rule out entry without a legitimate Hoot; a behavior-name check alone is not that proof.

Stock source: [act_riding_hoot](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_airborne.c#L1850); [interact_hoot](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1560).

Related atlas ranks: 5, 21.

<a id="split-push"></a>

### 09 — Palm-tree and object pushes

**Position effect.** The push helpers change State.X/Z without directly changing collision or stored display.

**Whole-game prerequisite.** A pole/tree callback or an applicable object interaction with Mario.

**SSL Area 1.** The palm tree at (-5989,0,-4850) is real. Enemies and other solid objects also use collision/push logic; banning Chuckya does not ban these helpers.

**The next copy or check.** The tree's POLELIKE callback is before Mario's update, after collision detection. Interaction pushes must also respect the handler order and accepted-warp short circuit.

**What is established.** Existing source proofs show that a graph-only writer exclusion is false: the tree can write State. New selectors have a positive tree control.

**What is still needed.** Prove the actual push receiver, contact range, resulting floor query and copies; distance from the warp is evidence to investigate, not a universal history proof.

Stock source: [cur_obj_push_mario_away](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_helpers.c#L2200); [push_mario_out_of_object](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L616).

Related atlas ranks: 5, 13A, 13B.

<a id="split-bounce"></a>

### 10 — Enemy bounce, knockback and environmental forces

**Position effect.** A bounce can snap State.Y to an object's hitbox top. Other interactions change speed/action first; normal movement later changes positions.

**Whole-game prerequisite.** Goombas, Pokeys, Fly Guys, flames, damage and ordinary environmental movement, depending on the actual handler.

**SSL Area 1.** Several such actors and hazards are stock Area 1. An impulse is not automatically a display-only or collision-only writer.

**The next copy or check.** Most of these handlers are after INTERACT_WARP. A successful nonfading warp stops the loop; they cannot be appended after that acceptance in the same loop.

**What is established.** The source handler order and bounce write are explicit. Existing acceptance/replay work checks the selected warp path, not all earlier bounces.

**What is still needed.** Follow a reached earlier interaction and its action constructor to the last display/collision copies.

Stock source: [bounce_off_object](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L515); [interact_bounce_top](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1368); [interact_damage](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1423); [interact_tornado](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1088); [interact_strong_wind](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1136).

Related atlas ranks: 5, 13B.

<a id="split-absent-launch"></a>

### 11 — Heave-Ho, bullies and Bowser's shockwave

**Position effect.** Heave-Ho supplies launch speed/status, not the Chuckya display anchor. Bullies can adjust State.Y; shockwave bouncing changes State and then display.

**Whole-game prerequisite.** Their distinct actor and interaction/action prerequisites.

**SSL Area 1.** The named Heave-Ho, five bully variants and BowserShockWave selectors are absent from stock SSL.

**The next copy or check.** Velocity changes alone do not create an instantaneous coordinate split. These mechanisms must not be conflated.

**What is established.** New US/JP selector checks cover all seven named behaviors. This excludes the stock selector paths, not an arbitrary asserted action history.

**What is still needed.** Retain separate no-actor/action-constructor obligations if using this as an all-gameplay exclusion.

Stock source: [bhv_heave_ho_throw_mario_loop](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/heave_ho.inc.c#L8); [bully_knock_back_mario](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L450); [act_shockwave_bounce](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_stationary.c#L790).

Related atlas ranks: 5, 13B, 21.

<a id="split-attachments"></a>

### 12 — Trees, poles, ledges and hanging

**Position effect.** These actions snap or translate State to an attachment point, generally followed by a display copy.

**Whole-game prerequisite.** A climbable pole/tree, ledge or hangable surface and the matching action.

**SSL Area 1.** The palm tree is present and ordinary ledges exist. A particular hanging surface or action entry still needs its own geometry check.

**The next copy or check.** Moving within an action is not the same as retaining that mismatch until the next warp interaction.

**What is established.** Source identifies the pole, ledge and stationary-hanging writers. Existing local proofs do not form a complete action-entry classification.

**What is still needed.** Trace each reachable attachment exit and the copies before a useful floor miss; no generic actor-absence shortcut applies.

Stock source: [set_pole_position](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L58); [check_ledge_climb_down](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_moving.c#L100); [climb_up_ledge](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L509); [let_go_of_ledge](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L490); [update_hang_stationary](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L375).

Related atlas ranks: 5, 13B, 18.

<a id="split-cannon"></a>

### 13 — Cannon entry and confinement

**Position effect.** Entry and confinement place State at the cannon and copy it to display. Normal firing moves State 120 units along the aim and returns before that display copy, so the stored display can lag.

**Whole-game prerequisite.** A live opened cannon and cannon-base interaction.

**SSL Area 1.** Area 1 has a cannon at (6863,0,-6860) and a Bob-omb Buddy that can open it.

**The next copy or check.** The firing branch explicitly requires INPUT_A_PRESSED. Its stale display is a real source-level case, but normal firing uses a new A press. Entry/confinement without firing follows the display copy.

**What is established.** The actual US/JP generated cannon body and stock C distinguish the early firing return from the ordinary tail. The new stock-selector positive control confirms the cannon is present; the firing-guard observation is source inspection, not a new action-history theorem.

**What is still needed.** Show a legal exit/interrupt with useful retained positions before the upper warp, or exclude that precisely defined continuation.

Stock source: [act_in_cannon](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L674); [interact_cannon_base](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1066).

Related atlas ranks: 5, 13B, 18.

<a id="split-tornado"></a>

### 14 — Tweester / tornado capture

**Position effect.** Tornado motion writes State around the tornado and updates display.

**Whole-game prerequisite.** An actual tornado interaction and the tornado-twirling action.

**SSL Area 1.** Tweesters are stock SSL Area 1 actors; a new positive selector check confirms this.

**The next copy or check.** The capture handler is after warp in the interaction order, and ordinary tornado movement occurs in the action phase.

**What is established.** Stock code gives a concrete writer/copy chain. Availability is not proof that it can transport a useful split to the top warp.

**What is still needed.** Trace a reachable release/interrupt and subsequent copies; do not replace it with arbitrary wind or position grants.

Stock source: [act_tornado_twirling](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L764).

Related atlas ranks: 5, 13B.

<a id="split-water"></a>

### 15 — Water entry, swimming pitch and surface bobbing

**Position effect.** Water entry/surface limits can move State.Y. Swimming pitch and surface bobbing add an offset to stored display after the swim copy.

**Whole-game prerequisite.** An ordinary water box and an appropriate submerged action.

**SSL Area 1.** SSL Area 1 has an oasis: water box 0 spans X -6911..-4223 and Z -7167..-4607 at Y=-127. 'Desert means no swimming' would be an incorrect exclusion.

**The next copy or check.** These are ordinary small/action-dependent offsets, not a supplied high display at the pyramid. Their survival through an exit and travel needs checking.

**What is established.** Stock water data and actual swimming writers are cataloged. No complete oasis-to-Ink transfer has been proved.

**What is still needed.** Establish legal action entry and a retained useful offset after leaving water; otherwise close that bounded transfer.

Stock source: [set_water_plunge_action](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L1174); [check_common_submerged_cancels](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_submerged.c#L1500); [update_water_pitch](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_submerged.c#L197); [surface_swim_bob](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_submerged.c#L428).

Related atlas ranks: 2, 5, 19, 21.

<a id="split-whirlpool"></a>

### 16 — Whirlpool capture

**Position effect.** The whirlpool action repositions State and updates display.

**Whole-game prerequisite.** A whirlpool object plus its interaction/action.

**SSL Area 1.** The whirlpool selector is absent from stock SSL, including the oasis.

**The next copy or check.** Ordinary swimming does not imply a whirlpool actor or its action.

**What is established.** New US/JP selector absence is checked. The action itself remains a different whole-game writer from normal swimming.

**What is still needed.** As with Hoot, a global proof needs legitimate action construction and actor lifetime, not merely a name-based ban.

Stock source: [act_caught_in_whirlpool](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_submerged.c#L1040); [interact_whirlpool](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1113).

Related atlas ranks: 5, 21.

<a id="split-shell"></a>

### 17 — Shell riding and the graphical offset

**Position effect.** Shell actions reanchor display and add a ride/tilt offset; the airborne code adds 42 to display.Y.

**Whole-game prerequisite.** A Koopa shell and the riding action.

**SSL Area 1.** A stock shell box is present at (5840,940,2500).

**The next copy or check.** A freshly added offset may be erased/recomputed by the next ordinary update. It is not the large gap by itself.

**What is established.** Existing shell-offset and refresh results are local. The whole-game catalog keeps shell/wall/floor scheduling as an available SSL family.

**What is still needed.** Find or exclude the exact interruption and geometry combination that consumes the offset before refresh.

Stock source: [act_riding_shell_air](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_airborne.c#L656); [tilt_body_ground_shell](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_moving.c#L745).

Related atlas ranks: 25, 2.

<a id="split-quicksand"></a>

### 18 — Quicksand depth and a stalled reward dialog

**Position effect.** Sinking subtracts quicksandDepth from display.Y. A useful negative depth raises display; a skipped refresh can retain it.

**Whole-game prerequisite.** A useful negative seed, valid collectible reward and a matching milestone dialog/action history.

**SSL Area 1.** Quicksand and reward opportunities exist in SSL; a useful no-A negative seed is not thereby established. The transfer test may grant a negative seed and valid coin/star opportunity.

**The next copy or check.** The dialog can preserve display across updates, but warp interaction and support retention have their own gates. Movement while display survives is already possible conditionally.

**What is established.** Seed-to-long-jump conditional proofs, entry resets, copy/refresh proofs and finite dialog continuations exist. None proves the useful floor-loss/contact/top combination.

**What is still needed.** Derive one concrete predecessor supplying useful display, low collision and the right first floor miss; do not assume that combination.

Stock source: [sink_mario_in_quicksand](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L1545); [act_star_dance](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L640); [general_star_dance_handler](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L590); [act_reading_automatic_dialog](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L443).

Related atlas ranks: 19, 2.

<a id="split-dialog"></a>

### 19 — Signs, NPC dialog and skipped refresh

**Position effect.** Some dialog states skip ordinary movement/copies; reading a sign also moves State during alignment.

**Whole-game prerequisite.** A sign/NPC/reward dialog with its actual action and timer.

**SSL Area 1.** Signs and Bob-omb Buddy are stock Area 1. Automatic milestone dialog is a separate reward-dependent path.

**The next copy or check.** A stopped update preserves what was there; it does not invent a gap. The next resumed action or geometry pass decides usefulness.

**What is established.** Existing dialog-gate and post-dialog refresh proofs cover specified paths. Treating all dialog as one harmless/beneficial freeze would be unjustified.

**What is still needed.** Identify the last writer before the pause and the first consumer after it, including contact and floor queries.

Stock source: [act_reading_sign](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L496); [execute_mario_action](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L1699); [mario_process_interactions](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L1780); [act_reading_npc_dialog](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L378).

Related atlas ranks: 2, 6, 19.

<a id="split-warp-reset"></a>

### 20 — Doors, teleports, instant warps and level entry

**Position effect.** Warp/entry code relocates records or initializes them; door actions move State through their own animation/copy sequence.

**Whole-game prerequisite.** The particular level command, warp kind and legitimate transition.

**SSL Area 1.** SSL has ordinary fading/nonfading warps, but Area 1 has no instant-warp command. The named door mechanisms are not stock Area-1 entrances.

**The next copy or check.** The chosen checkpoint is before the disappearing action or Area-2 initialization. Moving coordinates after that point cannot explain disagreement at acceptance.

**What is established.** Real entry depth reset and warp-call connections are proved. The accepted-warp final action call preserves all three positions; earlier calls have their own scope.

**What is still needed.** A foreign-course seed/actor or transient split must survive the actual transition, not be carried over by assumption.

Stock source: [check_instant_warp](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/level_update.c#L530); [init_mario](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario.c#L1788); [geo_obj_init_spawninfo](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/graph_node.c#L712); [act_entering_star_door](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L858); [act_going_through_door](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L919); [act_unlocking_key_door](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L775); [act_unlocking_star_door](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L817); [interact_warp](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/interaction.c#L855).

Related atlas ranks: 2, 13B, 18, 32.

<a id="split-butterfly"></a>

### 21 — Butterfly's temporary collision-position perturbation

**Position effect.** The butterfly helper adds to Mario's raw collision coordinates for aiming and subtracts afterward; State/display are not that scratch target.

**Whole-game prerequisite.** A live butterfly callback.

**SSL Area 1.** Existing US/JP proofs exclude stock Area-1 butterfly selector origins.

**The next copy or check.** The add/subtract intention must not be mistaken for a proved exact Float32 identity. No intervening consumer is granted.

**What is established.** Existing direct raw-Mario writer and butterfly-origin source checks isolate this unusual writer.

**What is still needed.** A universal frame would still need actual callback/receiver coverage; the stock absence result removes the named selector path.

Stock source: [butterfly_calculate_angle](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/butterfly.inc.c#L45).

Related atlas ranks: 13.

<a id="split-cutscene"></a>

### 22 — Endgame and other scripted placements

**Position effect.** Cutscenes deliberately place State or stored display, including the ending walk/wave and jumbo-star sequences.

**Whole-game prerequisite.** Their endgame/scripted action constructors and context.

**SSL Area 1.** The ending sequence is not a normal SSL Area-1 entry or reward dance. Ordinary SSL reward/dialog is listed separately.

**The next copy or check.** A function in the executable is not proof that the current course can enter that action.

**What is established.** The generated writer census finds these assignments; they are cataloged rather than silently dropped.

**What is still needed.** A complete no-A history theorem needs the actual constructor/transition exclusion. We have not replaced it with a blanket 'cutscenes harmless' premise.

Stock source: [act_end_waving_cutscene](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L2639); [end_peach_cutscene_run_to_castle](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L2469); [end_peach_cutscene_run_to_peach](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L2150); [jumbo_star_cutscene_falling](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L1811).

Related atlas ranks: 5, 18, 21.

<a id="split-debug"></a>

### 23 — Debug free movement

**Position effect.** The debug action writes State directly and refreshes display.

**Whole-game prerequisite.** A debug-action entry, not an ordinary retail controller constructor.

**SSL Area 1.** Its compiled helper appearing in the source census does not make debug mode a permitted SSL route.

**The next copy or check.** Arbitrary action injection is outside the project's controller-only model.

**What is established.** The census explicitly retains this name as excluded scope, rather than counting it as a gameplay counterexample.

**What is still needed.** If a claim includes debug builds or injected actions, change the model explicitly; this catalog does not.

Stock source: [act_debug_free_move](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_cutscene.c#L536).

Related atlas ranks: 31.

<a id="split-render"></a>

### 24 — Renderer, mirror Mario, camera and local vectors

**Position effect.** Render copies, camera positions, object transforms and local arrays may use a field named pos without modifying the three Mario records.

**Whole-game prerequisite.** A specific receiver or local storage location determines what is written.

**SSL Area 1.** Camera/render code is present; the castle mirror proxy is a separate object, not a second live Mario slot.

**The next copy or check.** An apparent visual displacement or a matrix translation is not automatically the stored display position read by the floor retry.

**What is established.** The mechanical census intentionally includes false positives such as coin-formation local pos and tilting-platform local pos. They are classified here.

**What is still needed.** Prove receiver/storage separation wherever a semantic preservation theorem needs it; do not treat all 'pos' writes as Mario writes.

Stock source: [geo_render_mirror_mario](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_misc.c#L589); [spawn_coin_in_formation](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/coin.inc.c#L170); [create_transform_from_normals](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/behaviors/tilting_inverted_pyramid.inc.c#L11); [update_ledge_climb_camera](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/mario_actions_automatic.c#L516).

Related atlas ranks: 20, 21, 31.

<a id="split-generic-objects"></a>

### 25 — Generic object movement, spawning and slot ownership

**Position effect.** Object helpers and behavior commands can write raw coordinates or display of their actual receiver; an allocator initializes a returned slot.

**Whole-game prerequisite.** A reached callback/command, its receiver and normal shared-pool ownership.

**SSL Area 1.** Many such helpers run in SSL. Spawning a child means another object, not another Mario.

**The next copy or check.** A non-Mario receiver can still share the pool's memory block; prove slot separation and the complete called segment rather than assuming every outside call harmless.

**What is established.** Existing allocation, child-copy and behavior results prove bounded effects. The complete callback/ownership history remains open.

**What is still needed.** Classify actual receivers and aliases for remaining reached calls in the fixed interval. Arbitrary pointer modification is not an allowed route.

Stock source: [allocate_object](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/spawn_object.c#L208); [obj_set_gfx_pos_from_pos](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_helpers.c#L634); [obj_update_gfx_pos_and_angle](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/behavior_script.c#L84); [obj_copy_pos_and_angle](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_helpers.c#L613); [vec3f_copy](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/math_util.c#L28); [vec3f_set](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/math_util.c#L36).

Related atlas ranks: 5, 13, 20, 21, 31.

<a id="split-copies-pauses"></a>

### 26 — Ordinary synchronization, time stop and skipped updates

**Position effect.** The ordinary State-to-Object copy synchronizes collision. Skipped phases can retain a preexisting disagreement but do not move positions by themselves.

**Whole-game prerequisite.** The real scheduler, action return, time-stop flags and copy receiver.

**SSL Area 1.** All apply to SSL; the initialized second-State copy proposal is already excluded in the existing source model.

**The next copy or check.** An early return from execute_mario_action still returns to bhv_mario_update, which performs the ordinary copy. A proposed skipped copy must identify the actual bypass.

**What is established.** Existing copy-index and completed-copy results are checked. Full all-history scheduling/ownership coverage is not proved.

**What is still needed.** Pair a real earlier writer with a reached skipped or delayed copy and the next contact/query. Freeze alone is not a producer.

Stock source: [copy_mario_state_to_object](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_list_processor.c#L224); [bhv_mario_update](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/object_list_processor.c#L267).

Related atlas ranks: 6, 18.

<a id="split-query-alias"></a>

### 27 — Signed-16 query aliases and different samples

**Position effect.** Converting a query or testing a different point can select different geometry even when no position record has just changed.

**Whole-game prerequisite.** The actual finite coordinate conversion, floor lists and query location.

**SSL Area 1.** The collision engine uses these conversions in SSL too. Useful distant coordinates still need legal movement and contact.

**The next copy or check.** A query-result disagreement is a consumer/geometric condition, not itself a write creating State/collision/display disagreement.

**What is established.** Finite geometry and alias checks exist with explicit domains. They are not all-controller-history coverage.

**What is still needed.** Connect a reachable pose to live list selection and accepted warp contact; no out-of-bounds memory effects are included.

Stock source: [find_floor_from_list](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/surface_collision.c#L401); [find_wall_collisions](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/engine/surface_collision.c#L184).

Related atlas ranks: 1, 3, 2.

## Exactly what was checked

[PositionSplitCatalog.v](../../proofs/PositionSplitCatalog.v), exposed as `MainTheorem.current_f02_position_split_catalog`, checks the actual generated US/JP program objects. Across all 38 generated units per version, the direct callers of `set_mario_pos` are exactly `dorrie_raise_head`, `bhv_tilting_inverted_pyramid_loop` and `apply_platform_displacement`. Twelve named actor behaviors fail the stock selector checks; tree, Tweester, Tox Box and closed cannon provide positive controls. The regular script test conservatively reads the whole SSL script, while macro and special checks use Area 1. Special-preset IDs reuse the earlier checked collision-data receipt.

The passing audit is `build/audit/20260924-104903-5dt7xgd1`: 595 registered sources, 425 of 519 proof modules in MainTheorem's import closure, 94 standalone modules, and no proof-hole/link problems. The catalog boundary and setter census each use four allowed foundations, the absent-selector theorem uses none, and the existing main Ink boundary still uses nine. Foundation counts do not count explicit gameplay premises.

The separate [source index](position-split-source-index.json) scans 336 pinned src C files, recognizes 4553 textual definition spans and records 824 coordinate-reference spans, including other courses, debug, camera and rendering code. It scans all 76 generated files (2,567 US and 2,561 JP function definitions; 9,156 and 9,110 assignments). All 50 distinct function names whose generated assignment destination contains `_pos` have a catalog home. This text check includes local arrays and other receivers and is deliberately broader than Mario writes. It is not a Coq coverage theorem.

The index reads the generator's pinned Git revision, never the modified decomp checkout. It records generated-file hashes. Five focused tests cover comments/strings, macro return types, version-alternative signatures, assignment destination versus read, and malformed assignment rejection. C spans retain preprocessor alternatives rather than pretending to be parsed bodies. Pointer aliases, union/byte writes, callees, externals and actual receivers remain semantic obligations. A syntactic named-position census cannot close those.

Regenerate with `python3 pipeline/split_catalog.py`; check both the index and this document with `python3 pipeline/split_catalog.py --check`. Run the scanner tests with `python3 pipeline/test_split_catalog.py`. The canonical prose is [position-split-catalog.json](position-split-catalog.json); this document and the private site use the same rows.

## How this becomes an exclusion proof

The remaining task is to prove that every reached write relevant to the fixed checkpoint belongs to the checked cases, with its real receiver and action/actor prerequisites. For each applicable case, prove either that its preconditions cannot occur there or that the next copy/contact/query removes its usefulness. Compose those results through the actual callback and interaction order. This classification is not presently a discharged theorem or an accepted premise.

The most focused next gameplay batch remains the pre-action geometry/retry interval fed by platform or floor alignment, with the raised display's last writer identified. Palm-tree pushes and water/cannon/shell transfers have separate catalog entries, so a proof for that interval will not silently claim to settle them all. Close a named case when its conditions and boundary match; expand only if another row actually reaches that boundary.
