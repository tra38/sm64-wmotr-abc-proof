# Can a coin reach the pyramid elevator?

## Answer

**A Goomba's dropped coin remains a possible supplier; no gameplay setup has
been constructed.** The elevator is capable of catching a moving coin under
the conditions below. The fixed coins do not offer an ordinary relocation
mechanism, and none lies on the elevator's path. This does not justify saying
that every gameplay method of supplying a coin is impossible.

Granting favorable Goomba movement and coin-launch choices still leaves the
death trigger. The reviewed stock Area-2 code supplies no ordinary passive
coin drop from quicksand, the moving blocks or despawning. Lava and drowning
can kill a Goomba elsewhere, but the checked Area-2 terrain provides neither
lava surfaces nor water regions. This narrows the proposal; it does not prove
that Mario cannot defeat a Goomba while remaining inside the elevator.

The backward approach check has not found a reachable Goomba contact either.
An ordinary jump from the low ground beside the bucket is too low. However,
Goombas rebound after hard falls, so the normal jump height cannot prove
that every approach fails. The precise remaining candidates and their
limitations are below.

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

## Could the Goomba die without Mario attacking it?

The regular Goomba's hitbox sets its health to zero and its loot count to
one. Zero health is normal for this enemy: it is not a countdown that kills
it automatically. A death handler still has to run before the moving yellow
coin is spawned. The relevant code is in
[Goomba behavior](../../../../../reference-sm64-decomp/src/game/behaviors/goomba.inc.c)
and the [shared enemy handlers](../../../../../reference-sm64-decomp/src/game/obj_behaviors_2.c).

| Proposed trigger | What the reviewed code does | Does this supply the drop? |
| --- | --- | --- |
| Walk above lava | The automatic death check calls the loot-spawning handler | Yes in suitable terrain; the checked Area-2 meshes have no lava surfaces |
| Drown | Standing underwater can call that handler when the water is at least 150 units above the Goomba and gravity plus buoyancy is nonpositive | No ordinary Area-2 water region is provided |
| Walk into quicksand or fall | Neither is a separate trigger in the Goomba's automatic death check | No ordinary passive drop established |
| Be squeezed by a Grindel, Spindel, moving wall or elevator | These handlers move their own collision surfaces; the Goomba's ordinary movement has no Mario-style ceiling-crush death check | No ordinary crush-to-coin mechanism in the reviewed handlers |
| Touch another Goomba or an Amp | Goomba collision resolution separates objects; the Amp's shock interaction concerns Mario | No enemy-to-enemy kill found in these handlers |
| Despawn or unload | Marking for deletion clears the active flags; it does not call the loot routine | Removal itself produces no coin |

There is a misleading nearby case: wall or ground contact can finish a
Goomba's **knockback** death. That requires the Goomba to be in an attacked
action already. Likewise, the squished action follows an attack; an object
visually compressing the Goomba does not automatically choose that action.
The shared handlers distinguish ordinary walking from those death states.
Triplet unloading also does not end the rest of that update immediately, so
the deletion result alone is not a theorem about every later operation in
that frame.

The new [Coq result](../../proofs/Area2GoombaDeath.v) executes the complete
generated US/JP automatic-death helper, using the selected program's actual
Object layout. When the underwater-on-ground, above-lava and entered-water
bits are clear, it returns false with the same memory and no calls or trace.
Other movement bits, including wall contact, are unrestricted. The separate
finite certificate reads all 1,558 static triangles and eight named interior
collision meshes, checks the absence of the burning surface type, and reaches
the exact terrain footer: four special-object records followed by the end
marker, with no water-region command. Deletion's complete generated body is
also checked to be only the active-flag write.

Those are a **local execution result and a finite source-data certificate**,
not a theorem that every reachable Goomba always has dry flags and stock
live floor lists. The movement code uses a missing-water sentinel, so the
absence of water boxes alone must not stand in for a proof about arbitrarily
low or unusual support histories. The moving-object and interaction cases
above are source review, not a completed whole-callgraph preservation proof.
No passive coin-producing counterexample was constructed.

## Can a Goomba get close enough to be defeated?

**No gameplay arrival has been constructed; the ordinary low-ground jump
fails, but a hard-fall rebound is a real unresolved alternative.** Favorable
movement choices remove the need to reject an idea merely because a Goomba
normally turns home. They do not supply an earlier high position, an impact
speed, repeated collision pushes or a live floor result.

The new generated-mesh check enlarges the **whole** elevator base by the
combined Goomba/Mario contact radii, 145 units, giving X=`[-656,657]`,
Z=`[-400,913]`. All 1,558 static faces are considered. There are 53
positive-Y face boxes meeting that rectangle: their support is at or below
Y=`-101`, except for four flat faces on the neighboring roofs at Y=`384`
and Y=`896`. This is wider than the earlier bucket-interior census; those
roofs must not be silently omitted. Getting a stock Goomba onto a roof is
itself an unproved predecessor. Floors outside this rectangle can also be
departure points for airborne approaches.
These are source geometry bounds; they do not establish the live floor
lists or a bound on every rounded floor-height calculation.

| Backward candidate | Checked result | What remains |
| --- | --- | --- |
| Ordinary jump from support at or below -101 | The 66-unit jump puts its feet at most at -35 and its head at 40, below even the nominal bucket jolt at 118 | This particular standing/jumping contact fails |
| Hard landing on floor -101 at vertical speed -76 | The real bounce multiplier gives upward speed 38; isolated gravity updates reach feet 61 and head 136 | Supply the impact near the bucket, then follow actual movement, walls, floor selection and attack |
| Departure from either neighboring roof | The source mesh has roof faces at 384 and 896 beside the north edge | Get a stock Goomba there while Mario remains confined, then show a useful departure |
| Direct approach from the stock 640-height ledges | All 14 flat source faces at 640 lie outside the contact rectangle enlarged by 1866 per axis | A path exceeding that allowance or using another support is not excluded |

The hard-bounce case comes from the real Goomba physics command, whose
coefficient is **-0.5**. The new Coq execution reads the falling vertical
speed, takes the negative-speed branch and writes its product with that
coefficient. For the stated -76 impact this is 38. The following fixed
arithmetic sequence reaches feet 61, high enough both for possible vertical
contact at bottom height 128 and for the base's 78-unit query allowance.
Those are conditional opportunities, not an installed Goomba. The execution
starts after the preceding floor-height copy and flag handling; supplying
that checkpoint, retaining the rebound through the Goomba's action code,
and obtaining the useful live floor are still obligations.

The -101 example uses a favorable height bound, not the floor at every
point beside the bucket. A concrete exterior candidate puts Mario at
`(-410,128,-154)` and the Goomba at X=`-551`, Z=`-187`, where static face
1314 has a loaded floor height between -113 and -112 (about -112.85).
A granted terminal-speed landing at -78 rebounds at 39; the isolated
Float32 sequence then reaches feet between 58 and 59, with its head above
Mario's feet at 128.
Their horizontal separation squared is 20,970, below the combined-radius
square of 21,025. These coordinates respect the nominal 50-unit Mario and
40-unit Goomba wall clearances. The Goomba remains outside the base, so this
is a candidate for an attack **from inside**, rather than a Goomba already
standing on the elevator. Supplying that fall, the live collision record,
the attack and the coin drop is still unproved.

The 1866-unit check grants 55 movements of at most 30 per horizontal axis,
plus total extra displacement of 216 per axis. It is a **stated movement
budget**, not a proved limit on all histories. The companion diagnostic
examines a generous flight from height 1145 with upward speed 39, followed
by one low-ground rebound, to guide that test. These isolated arithmetic
fixtures do not cover intervening supports, repeated pushes, action changes
or partial updates. In particular, the older Rank 11 component graph's
short-transfer edges cannot stand in for complete airborne coverage.

The Goomba's movement checks a wall radius of 40, smaller than its 108-unit
interaction radius. The reviewed attack code also does not add a second,
smaller-hurtbox test before accepting a valid punch: that smaller test sets
an invincibility-delay flag, while the punch branch calls `attack_object`
before consulting the flag. This is source review, not a completed attack
execution. Mario's action and facing, the collision records and the enemy's
death update still need checking. No controller arrival or coin-producing
defeat was constructed.

An accepted attack also needs to be followed through death. A punch selects
horizontal knockback; a grounded kick or trip selects vertical knockback,
with initial vertical speed 50 and a death check once its timer reaches 9,
even while airborne. Earlier ground, wall or water contact can trigger that
check sooner. This gives a concrete death mechanism to investigate after
arrival, but does not establish the coin's birth position or its return to
the elevator.

## Can a stock Goomba reach the west-wall position?

No stock actor starts at X=-551, Z=-187, and no gameplay arrival there has
been constructed. The direct diagnostic places its floor, source face 1314,
in component 66. None of the nine starts reaches that component through the
listed short-step graph, but every start has a path in the deliberately
permissive pair-transfer graph. A graph path does not arrange the second
actor, the collision or the subsequent walking.

The stock western singleton at `(-3638,0,1928)` supplies a concrete next
test. A proposed support outline runs east to X=-2800 at Z=1928, then toward
`(-551,-187)`. Its 8,193 integer-coordinate samples, using the preceding
selected height as the next query Y, encounter the raised rim at Y=72..113
and then a 214-unit drop from `(-3071,113,1928)` to the pit at
`(-3070,-101,1928)`. The samples end on the candidate floor; both generated
US/JP meshes agree. These are ideal-plane floor selections, not execution.
The straight entry-wall check below now blocks that isolated approach;
detours, other actors and changing support still need a gameplay route.

The drop restriction is not a complete obstruction. The generated
`cur_obj_move_xz` checks `ON_GROUND`, whereas `goomba_act_jump` returns to
walking on either `LANDED` or `ON_GROUND`. On an unchanged flat floor, the
isolated normal jump first crosses below the floor at vertical speed -23;
the -0.5 bounce coefficient gives +11.5. The following update can switch to
walking while rising to +7.5 and clearing `LANDED`; the next walking update
can accelerate while `ON_GROUND` remains clear. Thus a timed rebound near
the rim is a concrete candidate for entering the pit without a second
Goomba. This is source review and checked arithmetic, not a reached action
sequence. It corrects any inference that the short-step graph rules out
ordinary arrival. Reaching the low floor would still not supply the
terminal-speed rebound needed for the earlier elevator-contact candidate.

Validation: `analyze_mesh.js --check` checks the new component paths, support
samples and agreement with the generated geometry; the existing approach
diagnostic also checks the normal-landing arithmetic. No Coq theorem or
capstone premise was changed or discharged by this diagnostic tranche.

## What can favorable RNG actually do? (2026-09-12)

**The proposed straight approach fails in the isolated source check, even
with favorable random choices. A complete RNG-only impossibility result
has not been proved.** We grant any individually available random outcome;
finding an RNG schedule is no longer an obligation for this investigation.
This does not grant arbitrary speed, steering, jumps or actor placement.

The western Goomba's home is more than 3000 horizontal units from Mario
throughout the bucket footprint. Its normal walking helper therefore uses
a deliberately large distance value and does not enter the fast chase
branch. Its normal target speed is 2. Random choices turn by 45 degrees with
a timer of 100..199, or start a stationary jump and turn by 135 degrees.
Beyond 1000 units from home it is directed back, except while a collision
avoidance turn is already in progress. That exception is why the home test
alone is not a proof of an absolute movement limit.

The former support outline omitted a wall: at Z=1928, X=-3112 has a vertical
face from Y=0 to 72, before the slope to the 113-high rim. With its 40-unit
wall radius, a low Goomba is pushed to X=-3152. A normal jump clears forward
speed. The new [generated-code proof](../../proofs/Area2WesternGoombaRng.v)
executes the two velocity writes, derives forward speed zero and vertical
speed 25, and frames other cells. It starts after the sound call and action
assignment, under explicit scale, storage and separation conditions. It also
checks the two wall triangles in both generated meshes. This improves the
earlier source-shape check without claiming the full caller has been proved.

The [source diagnostic](../../instrumentation/western-goomba-rng/README.md)
loads all static faces using the actual loading and floor-list routines.
Its 2,457 low wall fixtures push to -3152; 5,320 nearby floor queries return
zero. A separate flat-floor closure grants a jump on every walking update,
even when the real timer forbids it, and speed 2 without drag. Without pauses,
it finds no moving query above Y=11. With arbitrary partial-update pauses,
a moving hop can reach Y=66, but the maximum advance beyond the wall-clearance
position is only 8 units, versus 40 needed to cross. Stationary height alone
does not overcome this obstruction. Both finite state sets are closed under
their stated choices, but their complete refinement to linked Clight and
the live world remains unproved. These are isolated diagnostic results,
not all-controller-history theorems.

A separate branch search retains the actual random timers, turns, home
behavior, wall checks and distance activation. In its static one-actor world,
with Mario fixed at `(-410,128,700)`, a checked sequence reaches
`(-3196.341552734375,0,2895.0380859375)` after 847 updates, still outside
the rim. US and JP replays agree. The bounded search has not found a route
around the southern end. It prunes states and does not cover every random
choice or world history, so this is not a detour impossibility proof.

[Watch this exact path](../media/western-goomba-path-replay.mp4). The video
reconstructs the recorded diagnostic positions against the collision mesh,
with a pause at update 847. It is not emulator footage; nearby stock enemies
are context markers, not participants in this isolated test.

The next useful connection is a detour, a stock-to-stock meeting and useful
push, or a changed support that bypasses the entry wall. A rebound from the
rim still presupposes getting onto it. The earlier contact-producing hard
fall, attack, death and coin delivery remain unconstructed. The overall
Rank 10A estimate stays **2–5%**, a subjective judgment: this weakens one
supplier proposal without settling the other entry and departure ideas.

## The next missing connection

Find a controller-reachable Goomba position, a coin-producing defeat and a path
that brings the live drop into the elevator's footprint at the right height
and time. Work backward from a late-descent catch or from the bottom example
above, checking whether Mario can arrange the enemy and attack without
already leaving the bucket, or identify another concrete death trigger.
For the Goomba proposal, first resolve an arrival through the nearby roofs,
a sufficiently hard landing near the bucket, or another concrete position or
support change. Favorable RNG choices do not supply that arrival or the
death trigger. A prearranged drop needs
its real lifetime and the area-transition/object-reset history; a coin does
not survive such a history merely because its coordinates are useful. Then check live floor
selection, the complete movement update, tangibility, contact and, if this
is the 100th coin, the star's placement and interruption timing.

The current Rank 10A full-route estimate remains **2–5%**, a subjective
judgment rather than a measured probability. The catcher is a conditional
positive result, but the gameplay producer and useful action change are
still missing. The passive-death check weakens that particular supplier idea;
it does not settle the remaining entry and departure possibilities or warrant
a new numerical estimate. This tranche neither installs a coin nor closes Rank 10A.

## Checks

[Area2ElevatorCoins.v](../../proofs/Area2ElevatorCoins.v) and
[Area2GoombaDeath.v](../../proofs/Area2GoombaDeath.v), together with the
[approach check](../../proofs/Area2GoombaApproach.v), are consumed by
`current_rank10a_ground_pound_moving_geometry_boundary`. It reuses the existing
coin census, generated meshes and exact Float32 floor calculations. The coin
execution starts at the floor-height copy after its preceding flag handling;
its guard, callers and earlier floor effects remain separate. The new death
execution covers the whole automatic-death helper from explicit memory reads
and dry flags, including its early return. The approach proof adds the rebound
and a concrete exterior contact position. None of these results supplies its
gameplay predecessor.

Run `node instrumentation/rank9a-coin-producers/check_producers.js` from the
active SSL project to reproduce the US/JP fixed-coin/elevator census. Use
`node --preserve-symlinks-main` on the restricted Windows runtime if its entry
path canonicalization fails. This is an offline diagnostic, not an emulator
run or a controller search. The approach diagnostic is
`instrumentation/rank10a-ground-pound/check_goomba_approach.js`; use both
`--preserve-symlinks --preserve-symlinks-main` with Node on the restricted
Windows runtime because it imports the existing mesh parser.

The earlier death module and Main compiled with Coq 8.16.1 and CompCert 3.15
through the installed `sm64-item-proof` pipeline. The selected audit passed
on 2026-09-11 at `build/audit/20260911-230409-faot3mxu/`: 547 registered
sources, passing proof-hole/link checks and no integration problems. Both
the combined Rank 10A boundary and the death-test execution use seven
existing allowed foundations; the finite terrain certificate uses none.
There is no new axiom. Local links, the atlas's single-paragraph sections and
whitespace checks also passed. This is checked local progress, not a completed
coin installation, universal passive-death exclusion or no-A route.

The approach tranche passed the same pipeline on 2026-09-12, recorded at
`build/audit/20260912-005604-6z3mlcib/`. It checked 548 registered sources,
Main and the new module, proof holes, link hygiene and integration. Main and
the rebound execution use seven existing allowed foundations, the full-mesh
certificate uses none, and the exterior Float32 contact certificate uses
four. No new axiom was added. Both US/JP diagnostics, local links, the
atlas's single-paragraph sections and whitespace checks passed. The checked
result is conditional contact geometry and local execution; the Goomba's
arrival, attack, death and useful coin delivery remain unproved.

The western-RNG tranche passed on 2026-09-12 at
`build/audit/20260912-113103-7h9wg08e/`: 549 registered sources, a successful
Main/new-module build, passing proof-hole and link checks, and no integration
problems. Main and the velocity-tail execution use seven existing allowed
foundations; the wall geometry uses none. No new axiom was added. The US/JP
native wall, floor, vertical-closure and legal-choice replay checks also pass
with undefined-behavior checking. These native results retain the limited
scope stated above; the audit does not turn them into a live route proof.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a)
