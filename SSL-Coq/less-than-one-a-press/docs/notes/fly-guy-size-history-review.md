# Fly Guy size history: growth, interruptions and clones

This review concerns the stock `bhvFlyGuy` actor in SSL Area 1. It grants a chosen clone position for a transfer test, as requested, but does not grant arbitrary scale, hitbox dimensions, action or timer values. The C reference is decomp commit `9921382a68bb0c865e5e45eb594d9c64db59b1af`; the checked generated counterparts are `us_obj_behaviors_2.v`, `jp_obj_behaviors_2.v`, the two `object_helpers` modules, and the two `object_collision` modules. Local instrumentation changes in the decomp are not part of this review.

The finding is narrower than a whole-game closure: repeated fire interruptions really can drive scale increasingly negative. They do not restart positive growth in the fire action, and the reviewed normal action cycles do not accumulate a larger positive scale. Connecting this source-derived size history to every live receiver and intervening call remains a proof obligation.

## The ordinary action cycle

The behavior script starts at scale 1.5. The native action graph is:

- **Idle:** `approach_f32_ptr(scaleX, 1.5f, 0.02f)` runs. Idle can leave for approach only when this call reports success, which writes exactly its 1.5 target.
- **Approach:** the fire-capable actor can enter shoot-fire and sets `oFlyGuyScaleVel = 0.06f`. The other choice enters lunge without writing scale. An ordinary generic Fly Guy does not select shoot-fire.
- **Lunge:** changes position, velocity and orientation. It returns to approach without a scale write or a scale-velocity reset.
- **Shoot-fire, facing Mario:** calls `obj_grow_then_shrink`. This helper changes only scale X. If the helper reports completion, shoot-fire changes to idle; helper completion follows a successful approach to exactly 1.1.
- **Shoot-fire, not yet facing Mario:** resets `oTimer` to zero and does not change scale or scale velocity in this branch. A later facing frame can therefore call the growth part again with the already reduced velocity.

The stock interpreter resets the timer on action changes and increments it after the native callback. These timer effects explain the interruption mechanic, but no timer manipulation in this graph resets the fire scale velocity to 0.06. That reset belongs to the approach-to-fire transition.

Starting from the normal script initialization, approach is reached either after idle has restored 1.5 or after a lunge that preserves this value. A completed fire cycle reaches idle at 1.1; returning from idle to approach again requires restoring 1.5. Therefore re-entry is not a way to add another positive growth prefix to the previous peak.

## What the shared growth helper actually writes

For timer below two, `obj_grow_then_shrink` writes `scaleX += scaleVel` and then `scaleVel -= 0.01f`. When the new velocity exceeds `-0.03f`, it also resets the timer. For timer above ten, it instead approaches 1.1 by 0.05, clamps at that target, and can set scale velocity to zero when firing. The intervening timer range writes neither scale nor scale velocity.

Thus skipped updates and facing failures can delay the sequence or extend its negative portion. They cannot add extra positive steps without consuming the descending scale-velocity sequence. The late recovery portion moves toward 1.1, and idle moves toward 1.5; neither target is above the positive-growth peak.

The following table uses the constants in the generated source. `ifgp_positive_prefix_bits_checked` in [InkFlyGuyGrowthPrefix.v](../../proofs/InkFlyGuyGrowthPrefix.v) checks the first seven steps with CompCert's actual binary32 operations. The eighth row remains an arithmetic diagnostic. Neither is a controller replay or coverage of every actor history.

| Completed growth calls | Scale X | Scale velocity after decrement |
| --- | ---: | ---: |
| 0 | 1.5 | 0.05999999865889549 |
| 1 | 1.559999942779541 | 0.04999999701976776 |
| 2 | 1.6099998950958252 | 0.03999999910593033 |
| 3 | 1.6499998569488525 | 0.029999999329447746 |
| 4 | 1.679999828338623 | 0.019999999552965164 |
| 5 | 1.6999998092651367 | 0.009999999776482582 |
| 6 | 1.7099997997283936 | 0 |
| 7 | 1.7099997997283936 | -0.009999999776482582 |
| 8 | 1.6999998092651367 | -0.019999999552965164 |

The maximum of this prefix is scale bits `0x3fdae146`. Multiplication by the stock hitbox height 60 gives `102.59999084472656`, bits `0x42cd3332`. Multiplication by radius 70 gives `119.69998931884766`, bits `0x42ef6665`. Additional growth calls with nonpositive velocity cannot increase finite scale. A size-history proof must establish the legitimate start and preserve the velocity sign through the real calls; the finite table alone does not establish those facts.

## X, Y and hitbox timing

At the beginning of `bhv_fly_guy_update`, `cur_obj_scale(oldScaleX)` writes that value to X, Y and Z. The chosen action then may modify X only. At the end, `obj_check_attacks` calls `obj_set_hitbox`, which writes:

- hitbox radius = current scale X times 70;
- hitbox height = scale Y times 60;
- hurtbox radius = current scale X times 40;
- hurtbox height = scale Y times 50;
- hitbox down-offset = scale Y times zero.

Radius and height can therefore come from adjacent growth stages. The positive prefix peak also bounds the preceding scale used for height within the reviewed normal cycle. The signed negative case must not be modeled as a positive hitbox with an absolute-value size.

Fly Guy is a general actor. Stock object order performs collision detection first, then Mario's player callback, then general actor callbacks. A new Fly Guy scale and hitbox ordinarily affect the following update's Mario collision checks. This source ordering is not by itself a memory-frame proof across every callback or every clone history.

## Attacks do not add an overlooked squish cycle

Fly Guy calls `obj_check_attacks`, not the shared `obj_update_standard_actions` or `obj_handle_attacks` squish machinery used by some other enemies. Its call supplies the current action as `attackedMarioAction`; the shared attacked-Mario branch therefore does not select a different action in this invocation. Ordinary successful attacks call the health/death machinery; the template initializes health to zero. That path does not invoke `obj_act_squished` and does not create the shared squish routine's enlarged X scale.

The direct native actor writes and selected normal branches therefore offer no squish-based route to a larger positive Fly Guy hitbox. A formal live memory proof must still account for reached spawn/death helper calls, allocation, ownership and alias separation rather than assuming every outside call is harmless.

## Freezing and placing a clone

Stock Fly Guy flags do not include the normal holdable flag. A fake-object pickup selects `bhvCarrySomething3`; a drop or throw selects the corresponding `4` or `5` carry script. For a non-holdable object, `obj_set_held_state` changes the behavior instruction pointer and clears its stack index. These three scripts consist of `BEGIN` followed by `BREAK`; they do not automatically resume the old Fly Guy native action on release.

The shown grab/drop/throw routines do not resize the actor or reset its fire scale velocity. A frozen clone retains the signed, possibly unequal size values that were present when its native behavior stopped. HOLP placement changes its position, not the signs of those fields. If a separate legitimate mechanism resumes or replaces its native behavior, that mechanism and its resulting fields need their own explanation. Respawning a normally initialized Fly Guy begins a new scale-1.5 generation; it is not a continuation that accumulates the old peak.

The remaining global inventory issue is exact: demonstrate that the selected live Fly Guy or frozen clone keeps its identity and fields through behavior-script execution, the called helpers and other callbacks, or classify every reached ordinary writer that changes them. This review does not silently assume that actor identity persists across slot reuse.

## Why enormous negative graphics do not supply a huge upward bounce

The actual collision guard compares the signed radius sum with the nonnegative horizontal distance. It does not take absolute values. With normal Mario radius 37, uniform scale `-0.5285714268684387` already gives a binary32 radius sum of exactly zero; the strict guard cannot register contact even at coincident X/Z. Adjacent scale bits `0xbf075074` give a positive sum of `0.000003814697265625`, while `0xbf075076` give its negative. These are finite binary32 sensitivity checks. The mixed X/Y phase should be checked using its actual fields rather than a uniform-scale assumption.

Existing Coq theorem `ibp_fresh_contact_bounce_cannot_snap_below_collision` already gives a stronger, placement-independent vertical obstruction under its explicit matched-read conditions: a registered zero-down-offset contact cannot snap movement below the collision bottom. It does not require a positive hitbox height. With synchronized movement/collision and nonpositive height, collision requires `MarioY <= enemyY + height <= enemyY`, whereas the falling-bounce branch requires `MarioY > enemyY`. Those conditions cannot both hold at matching reads.

Repeated negative growth is still a real gameplay size change. The argument above addresses its fresh bounce payoff, without relying on a later crash or investigating undefined conversion behavior. A pre-existing position split, changed collision/handler reads, another writer, or an alternate interaction remains a separate question.

## The new formal connection and its remaining boundary

The new [growth-prefix module](../../proofs/InkFlyGuyGrowthPrefix.v) extracts the actual timer choice from completed US/JP helper execution, keeps both growing and recovery alternatives, derives both reached growing stores, and proves their actual addresses and binary32 values. It separately follows completed `obj_set_hitbox` execution to its real height store. [InkFlyGuySizeBoundary.v](../../proofs/InkFlyGuySizeBoundary.v) composes that store with the checked prefix: if its actual scale-Y read is one of those prefix values and its actual template-height read is60, the height written is at most102.59999084472656. Delayed scale Y is not identified with the newly updated X.

This closes a real store-to-prefix connection; it does not derive the prefix-membership and read premises for every actor. Still required are legitimate fire-entry normalization, the complete native action-cycle and helper identities, the X-to-Y carry, and preservation between callbacks or across a frozen clone's lifetime. The finite prefix, signed-contact obstruction, reviewed action graph and conditional actual-store theorem remain distinct. No complete actor-history or maximum-separation closure is claimed.

The selected pipeline audit `build/audit/20261004-230645-87vpwpoo` passes compilation, proof-hole/link discipline and all six foundation checks: 642 registered sources, 470 of564 modules in the main import closure, 94 standalone and zero problems. The actual size-store statements have seven allowed foundations, the finite prefix four, and the connected backward boundary nine. The two new modules are registered and connected through `InkConcreteProducerBoundary.v` to `MainTheorem.v`. These counts describe mechanical validation, not discharge of the explicit gameplay premises.
