# Can a coin reach the pyramid elevator?

## Answer

**A Goomba's dropped coin remains a possible supplier; no gameplay setup has
been constructed.** The elevator is capable of catching a moving coin under
the conditions below. The fixed coins do not offer an ordinary relocation
mechanism, and none lies on the elevator's path. This does not justify saying
that every gameplay method of supplying a coin is impossible.

For Rank 10A, the hard part is supplying the drop while Mario is still
confined to the elevator. A method that first leaves the bucket to move or
defeat an enemy does not supply the missing first escape. Simply collecting
a yellow coin also does not change Mario to a ground-pound-compatible action;
a proposed 100th-coin/star interruption needs its own collection and action
sequence.

## Which coins could be used?

| Source | What the code permits | Elevator result |
| --- | --- | --- |
| 15 individual yellow coins | Ordinary contact collects them; their stock loop does not move them | All are outside the elevator footprint |
| 23 possible formation children | Ground children initially adjust Y to a floor; respawning uses the same parent and recipe | Their X/Z positions all miss the elevator |
| Three switched blue coins | The switch changes visibility and tangibility at existing positions | All three remain far from the elevator |
| Nine stock regular Goombas | An ordinary defeat can produce one moving yellow coin at the enemy's X/Z | Concrete mobile producer; enemy/drop transport and timing remain open |
| Two Area-2 boxes | Both stock presets contain walking 1-ups | No coin supply |

The prior [ordinary-coin census](rank9a-ordinary-coin-producers.md) concerned
the **second-pole shaft**. Its old separation rectangle was not an elevator
result. The new check decodes the elevator's generated level command at
`(0,4966,256)` and its base vertices. The full base footprint is X in
`[-511,512]`, Z in `[-255,768]`; descent changes Y, not this footprint.

All 41 fixed-layout coin actors miss even that rectangle enlarged by 150 on
every horizontal side. The closest coins are at X=`-260` or `260`, Z=`-600`,
at their three listed heights. Their horizontal distance to the full base is
**345 units**, already greater than the ordinary coin/Mario contact radii
combined. The 150-unit margin also exceeds those radii. The exact formation
diagnostic checks all 23 children; the Coq implication separately permits
any horizontal offset up to 320 per axis from each stock formation parent.
Live position preservation remains separate from an initializer census.

## Why a dropped coin could be caught

The real `bhvSingleCoinGetsSpawned` script continues running the moving coin
loop after its initializer changes the behavior identity to `bhvYellowCoin`.
It checks walls and floors, uses ordinary coin gravity and bouncing, and
becomes collectible after its resulting vertical speed turns negative.
Neither the identity change nor the fixed-coin loop makes this drop stationary.

The movement uses the ordinary `find_floor` query, including dynamic floors
and the 78-unit allowance above query Y. It then has a separate operation
that writes the selected floor height to the coin's Y when movement puts the
coin below that height. This later write matters: lookup success alone is
not the landing operation. The reviewed coin movement path has no ceiling
collision step that would, by itself, block entry through the base underside.
Walls, other selected floors, partial updates and the live collision lists
still need checking for any proposed trajectory.

A concrete **conditional local example** uses the elevator parked at Y=128:

| Checkpoint | Result |
| --- | --- |
| Coin query `(0,49,256)` | The two checked base faces miss |
| Coin query `(0,50,256)` | One base face is eligible at the 78-unit boundary |
| Coin query `(0,64,256)` | That same base face is eligible and has height 128 |
| Granted vertical speed 24, normal gravity -4 | New speed 20, proposed Y 84 |
| If active, non-water movement reaches the ground/air branch and the live floor result remains 128 through its flag handling | The actual position-copy segment writes coin Y=128 |

These are finite generated-mesh checks and a local Clight execution, not a
full coin update or a reached coin spawn. In particular, the example grants
the coin pose and velocity; it does not claim an RNG history, Goomba defeat,
wall result or full list execution. The copy theorem derives the written Y
and preserves disjoint reads from ordinary readable/writable storage.

This example also does not establish lasting carriage or collection. A
descending elevator can move away from a coin, which has its own gravity
and bounce state. Any useful catch must be followed until the coin is
tangible and Mario actually overlaps it. A coin caught only after the
elevator has stopped supplies no descending-support height window by itself.

## The next missing connection

Find a controller-reachable Goomba position, finishing attack and coin path
that brings the live drop into the elevator's footprint at the right height
and time. Work backward from a late-descent catch or from the bottom example
above, checking whether Mario can arrange the enemy and attack without
already leaving the bucket. A prearranged drop needs its real lifetime and
the area-transition/object-reset history; a coin does not survive such a
history merely because its coordinates are useful. Then check live floor
selection, the complete movement update, tangibility, contact and, if this
is the 100th coin, the star's placement and interruption timing.

The current Rank 10A full-route estimate remains **2–5%**, a subjective
judgment rather than a measured probability. The catcher is a conditional
positive result, but the gameplay producer and useful action change are
still missing. This tranche neither installs a coin nor closes Rank 10A.

## Checks

[Area2ElevatorCoins.v](../../proofs/Area2ElevatorCoins.v) is consumed by
`current_rank10a_ground_pound_moving_geometry_boundary`. It reuses the existing
coin census, generated elevator mesh and exact Float32 floor calculations.
Its local execution begins at the actual floor-height copy after the
preceding flag handling; the guard, callers and earlier floor effects are
not silently assumed discharged.

Run `node instrumentation/rank9a-coin-producers/check_producers.js` from the
active SSL project to reproduce the US/JP fixed-coin/elevator census. Use
`node --preserve-symlinks-main` on the restricted Windows runtime if its entry
path canonicalization fails. This is an offline diagnostic, not an emulator
run or a controller search.

The targeted module and Main compiled with Coq 8.16.1 and CompCert 3.15
through the installed `sm64-item-proof` pipeline. The selected audit passed
on 2026-09-11 at `build/audit/20260911-222027-kuhx9m6v/`: 546 registered
sources, passing proof-hole/link checks and no integration problems. Both
the combined Rank 10A boundary and the new coin boundary use seven existing
allowed foundations, with no new axiom. The US/JP diagnostic, local links,
atlas paragraphs and whitespace checks also passed. This is checked local
progress, not a completed coin installation or a no-A route.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a)
