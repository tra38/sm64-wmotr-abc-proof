# Bob-ombs, cloned coins and camera effects at a cog Pedro spot

Scope: `VERSION_US` and `VERSION_JP`, pinned SM64 source
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. Reviewed 2026-09-21.
This is a source analysis of three proposed routes, cross-checked against the
generated Clight. It adds no Coq execution theorem or gameplay witness.

## Current answers

| Proposal | Result at the cogs |
| --- | --- |
| Vary height across a Bob-omb's activation boundary | Real mechanism demonstrated on the red-coin spinners. The verified stationary-cog ordinary-air loop fixes the position used by the gate, so that loop supplies no height switch. Other preserving paths remain open. |
| Hands-free cloning followed by coin collection | Collection need not involve landing, but a standard non-holdable clone runs a replacement carry script and therefore does not automatically create ordinary coin sparkles. A preserving, controllable hands-free release/collection path has not been established. |
| Change camera-relative environmental RNG consumption | TTC selects environmental mode NONE. Moving the camera does not enable snow. The existing US/JP NONE-mode execution theorem preserves all memory under its entry conditions. |

None of these findings completes the preserving RNG-control target. In
particular, an object that consumes RNG on a predetermined schedule is not yet
an input-dependent choice while Mario remains in the spot.

## 1. What the Bob-omb video demonstrates

Tyler Kehne's [TTC Pedro Spot RNG Manipulation](https://www.youtube.com/watch?v=qoc4i4S4N5Q)
demonstrates the red-coin spinner setup. Its expanded description reports an
approximately one-unit height adjustment, changing the Bob-omb distance from
about 4000.44 to 3999.71. The Bob-omb is positioned in the cage and settles
against a wall while trying to return home. The author explicitly leaves the
moving-platform test open and describes the changed draw distance as a
visibility aid. The clip does not identify a US/JP ROM version or demonstrate
the cog arrangement. Its general claim about unavailable particles is not an
exhaustive proof of the action paths studied here.

The pinned source supports the activation-boundary mechanism, with two precise
qualifications:

- `bhv_bobomb_loop` runs its main body only if
  `is_point_within_radius_of_mario(..., 4000)` succeeds. The helper uses a
  strict, single-precision squared-distance comparison with `4000 * 4000`.
  It reads **`gMarioObject->header.gfx.pos`**, Mario's graphical root position,
  rather than directly reading `MarioState.pos` or an animated limb position.
- The blink helper draws `random_float()` when its blink timer is zero;
  nonzero blink-timer updates need no fresh draw. Thus activation permits RNG
  consumption but does not guarantee one blink draw on every active frame.
  Blink processing is outside the held/free-state switch. Holding the Bob-omb
  alone does not switch blinking off. Fuse smoke is another conditional source:
  each executed smoke initialization calls RNG three times.

For the recorded 30-update stationary-cog control, Mario stays at
`(1313, -2088, -1098)`. The attempted movement selects the lower cog top at
`Y = -2088` and an upper ceiling 154 units above it. The close-gap air return
retains actual X/Z and assigns Y to that same floor height. `perform_air_step`
then copies `MarioState.pos` into the graphical root. The regular freefall
landing path does not add a graphical-root displacement afterward. The
Bob-omb's destructive-object update occurs after the player update.

Consequently, if those complete ordinary-air returns continue and the Bob-omb
stays at the same position, changing the attempted velocity cannot change its
activation test. The cog top is horizontal: its collision vertices share a
height and the cog rotates about Y. The sloped spinner's height control does
not transfer to this same-floor cog loop.

This conclusion is deliberately narrower than saying that no action at any
cog Pedro spot can ever influence a Bob-omb. A different action could change
the graphical root, a different selected surface could change the returned
height, or the Bob-omb itself could move. Each requires a complete preserving
path and a pair of input continuations with different accepted RNG draws. An
animation that moves a limb alone is not sufficient. Nor is merely putting a
Bob-omb nearby: its settled position must put the controllable motion across
the actual activation boundary.

Sources: generated `us_obj_behaviors.v` / `jp_obj_behaviors.v`
(`f_is_point_within_radius_of_mario`, `f_bhv_bobomb_loop`,
`f_curr_obj_random_blink`, `f_bhv_bobomb_fuse_smoke_init`),
`us_mario_step.v` / `jp_mario_step.v` (`f_perform_air_step`,
`f_perform_air_quarter_step`), the freefall/common-air functions, and pinned
`src/game/object_list_processor.c`, `data/behavior_data.c`,
`src/game/behaviors/ttc_cog.inc.c`, and
`levels/ttc/rotating_hexagon/collision.inc.c`.
The actual control is documented in the
[ground-pound impact-and-successor investigation](ttc-cog-ground-pound-successor.md).

## 2. Hands-free holding is not automatically a coin-sparkle source

The air-action code contains a hands-free-holding route: a wall-result branch
with no referenced wall can change to a non-holding action without clearing
the held object. The normal Pedro `AIR_STEP_LANDED` branch is not that branch.
Preparing hands-free holding before entry is a candidate, not an established
cog entry/release sequence.

`interact_coin` itself increases coins and healing and sets the coin's
interaction status. Its ordinary branch neither calls RNG nor changes Mario's
position, action or speed. It does not require a landing result. Subject to
the real overlap, tangibility and interaction-dispatch conditions, Mario can
therefore collect a coin in the air without the coin handler moving him. This
local observation does not execute the rest of that frame.

For an ordinary live yellow coin, **the coin's behavior** notices the interaction
status, spawns `bhvGoldenCoinSparkles`, and marks the coin for deletion.
`bhv_golden_coin_sparkles_loop` then calls RNG twice for X/Z offsets. Its script
repeats the loop three times; two draws describe one loop invocation, not the
entire accepted effect or frame.

For the standard non-holdable cloning path, `obj_set_held_state` instead
replaces the object's current behavior command with the selected carry script
and clears the behavior stack index. `bhvCarrySomething3`, `4`, and `5` contain
`BEGIN` and `BREAK`, without the original coin loop. Ordinary yellow coins do
not have the holdable flag. A coin clone can retain the fields needed for coin
interaction while no longer executing the code that turns that interaction
into golden sparkles. Collecting such a clone therefore does **not**, by
itself, establish the advertised sparkle RNG source.

Important boundaries:

- A still-running coin occupying a reused held-object slot is distinct from a
  coin whose carry script has already been installed. Its lifetime, behavior
  and timing must be checked separately.
- Crossing 100 coins in a main course calls the 100-coin-star helper. This
  analysis excludes that branch from the ordinary-collection conclusion;
  its later effects need separate accounting.
- Dropping uses the last held-object X/Z position and Mario's current Y;
  throwing uses a different offset. Hands-free holding does not prove that
  those coordinates overlap Mario or that an input-triggered release preserves
  the spot. The direct release helper is not a complete preserving action.
- A live coin that reaches Mario on a fixed schedule could consume RNG, but
  does not supply a choice of collection time unless inputs can change the
  interaction while preserving the Pedro state.

Sources: generated interaction functions `f_interact_coin` and
`f_mario_drop_held_object`; object helper `f_obj_set_held_state`; airborne
`f_common_air_action_step`; behavior functions `f_bhv_coin_sparkles_init`,
`f_bhv_yellow_coin_loop`, `f_bhv_golden_coin_sparkles_loop`; and generated
behavior-script data, all for US and JP. The existing
[cloning/floor report](ttc-cog-cloning-floor.md) proves related carry-script
and floor-list facts, but does not prove this proposed coin route.

## 3. Camera-dependent environmental effects

TTC's area geometry selects `GEO_ASM(0, geo_envfx_main)`. The zero is the
environmental mode. Camera coordinates are separate inputs; moving the camera
does not change that zero into a snowfall mode. The normal-snow code's
different movement/respawn draw counts therefore supply no stock TTC method.

The existing
[`EnvironmentNoRNG.v`](../../proofs/EnvironmentNoRNG.v)
theorem `generated_environment_none_preserves_all_memory_us_jp` executes
the generated NONE-mode particle update, including its real getter and
initializer callees, and proves identical final memory. It requires
`gEnvFxMode = 0`, `gDialogID = -1`, and the stated global/function bindings.
`generated_ttc_environment_callback_zero_argument_us_jp` separately checks
the generated TTC callback data. A complete geometry-interpreter and level-entry
execution connecting these facts remains open.

This is not a claim that all camera code is RNG-free. Shock/handheld-shake and
some cutscene paths have their own RNG calls. Ordinary camera movement does
not, merely by changing its coordinates, establish such a preserving path.
Those paths remain in the [all-RNG inventory](ttc-cog-all-rng.md).

## Verification boundary and next obligations

The 14 generated US/JP function definitions listed above, excluding
`geo_envfx_main`, were text-compared after normalizing only the compiler's
anonymous numeric type names; they match under that normalization. The
geometry callback also contains version-dependent graphics commands, so no
whole-function textual equality is claimed for it. Its relevant zero-mode
data is already checked by the existing theorem. This comparison is a source
check, not a semantic-equivalence proof or an executed cog frame.

No emulator state was changed, no new runtime trace was produced, and no Coq
proof was added in this investigation. Remaining useful obligations are:

1. Find a preserving input choice that changes the graphical root seen by a
   settled Bob-omb across its activation boundary, or prove exclusion for the
   relevant complete action family.
2. For a coin route, establish the actual runtime behavior, overlap and
   controllable interaction/release, then execute all accepted particle or
   star effects and the following preserving update.
3. Connect environment NONE to actual TTC entry, and execute or exclude the
   remaining object/camera RNG paths with their real scheduling order.
