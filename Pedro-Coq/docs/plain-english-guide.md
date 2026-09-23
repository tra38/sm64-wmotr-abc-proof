# Pedro-Coq in plain English

This guide is for a reader who knows basic C# programming but does not know
Super Mario 64 or proof assistants. It explains the Rocq/Coq proof system used
by this project, what a Pedro spot is, why dust can matter to the game's random
number generator, and exactly what has been proved about the Tic Tock Clock
spinner Pedro interval and the newer cog work.

Only the North American (`VERSION_US`) and Japanese (`VERSION_JP`) versions of
the original game are covered. Nothing here should be assumed for the European,
Shindou, or iQue versions.

The active task now concerns TTC cogs, which have their own behavior. The cog
work has certified a pair of overlapping surfaces and proved one complete
stock cog update preserves its angle under specified initial conditions.
There is also a conditional execution proof for dust requested during the
sliding phase after a slide kick. That proof shows that two previously
assumed helper paths execute and preserve Mario's position and floor reference.
The sliding-motion and ground-step helpers remain open.

The cloning investigation now proves a separate distinction: floor queries
can select an already published triangle without consulting its parent
object's hitbox or position, but changing the object position does not move
that triangle. The complete partition-clearing function and its following
empty-list query are also checked. See the
[cloning and floor report](notes/ttc-cog-cloning-floor.md) for the TTC candidates
and the remaining gameplay obligations.

The project still has no complete witness of Mario staying in the cog Pedro
spot and controlling RNG there. Some recorded experiments start from a declared
near-cog test placement; they do not establish a route from normal level entry.
See [the cog plan](notes/ttc-cog-plan.md) and
[the latest execution report](notes/ttc-cog-transition-execution.md).

A new [bounded geometry search](notes/ttc-cog-geometry-search.md) finds 987,984
ordinary-air candidates among 35,684,352 sampled position-and-pose combinations
per version. None passes its first-quarter ground-pound preservation filter.
One newly selected position was separately verified in the emulator for 94
successive Pedro updates with the cogs stopped; its extended replay now passes
[1,200 successive game frames](notes/ttc-cog-1200-frame-hold.md), about 40 seconds
at normal speed, in both versions. Ground pound still leaves that spot on its
first descent. These are finite discovery results, not new Coq proofs or a
complete search of reachable states.

The [RANDOM-mode follow-up](notes/ttc-cog-random-1200.md) still finds no
1,200-frame RNG strategy. The same initialization already has nonzero cog
targets in RANDOM mode, so both cogs rotate before Mario's first controlled
action. A smaller stick, a dive followed immediately by a rollout, and an R
camera toggle can preserve the STOPPED spot in the checked windows, but their
ordered RNG draws match the unchanged-input control. Preserving position and
controlling RNG are separate requirements.

## The game ideas first

Super Mario 64 represents Mario's position with three coordinates: X, Y, and Z.
X and Z locate him across the ground, while Y is his height. The game also keeps
references to the floor and ceiling surfaces near him.

A **Pedro spot** is a very cramped collision arrangement. Mario attempts an air
movement and reaches a floor, but the gap between that floor and the ceiling is
at most 160 game units. In the important branch of the movement code, the game:

1. reports that Mario landed;
2. places his Y coordinate at the floor height; but
3. does not accept the attempted X/Z movement or replace his referenced floor
   when the floor-to-ceiling gap is 160 or less.

In simplified C#-style pseudocode, the relevant idea is:

```csharp
if (nextY <= floorHeight)
{
    if (ceilingHeight - floorHeight > 160.0f)
    {
        mario.X = nextX;
        mario.Z = nextZ;
        mario.Floor = newlyFoundFloor;
        mario.FloorHeight = floorHeight;
    }

    mario.Y = floorHeight;
    return AirStepLanded;
}
```

This is unusual because the result says "landed" even when the close ceiling
causes some of the normal landing updates to be skipped. A useful Pedro spot
must also have enough horizontal overlap between the floor and ceiling for
Mario to occupy the cramped region.

Notice that Y is still assigned. This call preserves all three coordinates
only if Mario was already at the returned floor height. Other code can move
Mario or change his action before or after this call. Seeing one such "landed"
return therefore does not establish that he stays in the spot for the whole
frame, or for the next frame.

## How a landing can create dust

The landing return itself does not create dust. The action handling that
return determines what happens next. The common landing action studied in the
original proof changes Mario's forward speed before checking for dust.

There are two important controller cases:

- With analog-stick input, the flat-floor speed calculation multiplies the
  current speed by `0.98f`.
- With no analog input, the game applies a fixed slowdown. Its size depends on
  the floor class.

After that speed update and a ground step, the game requests dust only if the
resulting forward speed is strictly greater than `16.0f`.

The project has exact 32-bit floating-point examples for every relevant flat
floor class. In those examples, the same starting situation can leave the
analog-input result above 16 while the neutral-input result is at or below 16.
This is the basic controllable choice: one input requests dust and the other
does not.

This result is about the calculation itself. A complete proof still needs to
show that both input choices repeatedly preserve a real, reachable stock Pedro
state. It must also show that the landing action reaches this calculation:
the game computes an off-floor input flag from Mario's floor state, and that
flag can cancel the action before its dust-producing code.

### The sliding phase after a slide kick

A slide kick has its own action sequence: an airborne kick, a possible bounce,
and a ground-sliding phase. The sliding phase has a different dust-request
path from the common landing action above. Its dust assignment can run after
the ground step reports a wall stop. The checked cramped-gap branch can return
that stop result even without a wall reference.

The latest proof executes the generated sliding action under explicit conditions
on its starting state and intermediate helper results. These include an already
selected slide animation that has not ended, no intended stick movement, an
off-floor flag, a null wall reference, and readable speed, floor, animation and
sound-queue data. A reachable cog state satisfying all these conditions has not
yet been exhibited.

A **helper** is simply another function called by the action. Two previously
assumed helper paths are now executed in the proof:

- The no-wall reflection requests the hit sound and reverses forward speed,
  using the actual velocity setter and sine/cosine table reads. Its writes
  preserve Mario's position and retained floor reference.
- The action setter changes Mario to backward ground knockback and resets
  the relevant action fields. Its writes also preserve position, floor and
  particle requests.

The proof also corrects the terrain-dependent sound to TTC's stone-terrain
case and executes that sound-selection helper. TTC's terrain category and the
floor Mario still references are separate facts; the retained floor remains
an explicit condition of this proof.

Two helper executions and their position/floor preservation remain assumed:
`update_sliding`, which updates sliding motion, and `perform_ground_step`,
which performs the ground movement and collision queries. Subject to those
conditions, the action requests **dust and vertical stars**, selects backward
ground knockback, and preserves the checked position and floor reference.

Selecting the next action does not execute it. The following knockback update
needs a different animation and more movement code. The airborne entry and
bounce also need their own preserving execution proofs. The current result
therefore identifies a dust candidate; it does not establish dust creation
while Mario remains in the actual cog spot.

Knockback also changes what happens to speed. The transition reverses forward
velocity while retaining position, so it does not itself eject Mario. The next
knockback handler first clamps forward velocity to `[-32, 32]`. On a flat stored
floor, its early animation frames apply 0.9 friction; from animation frame 22
it sets speed to `+0.1` or `-0.1`. It has no ordinary stick acceleration. Slopes
can change the early-frame calculation, and the stored floor is not necessarily
the cog floor found by an attempted movement. Continued confinement still needs
the next ground-step proof. This is not yet a repeatable speed-building loop.

### Could a cloned object supply the missing floor?

An object has several kinds of data. Its interaction hitbox determines things
such as whether Mario can touch or grab it. A platform's collision triangles
are separate data, placed in lists that the floor-search code reads. Removing
ordinary interaction does not automatically remove a triangle already in one
of those lists.

The proof executes a floor search that selects a supplied cog triangle without
reading any parent-object fields. It finds the triangle at its stored location.
Teleporting the object therefore does not, by itself, put a new floor underneath
Mario at the destination.

There is a further obstacle for non-holdable clones: their original behavior is
replaced by a short carry script ending in `BREAK`. The proof executes that
command and the interpreter-loop exit without changing memory. The original
platform's collision-loading behavior is not run by that loop. Other generic
object-update work still needs to be accounted for in a complete frame.

Normal dynamic-surface processing clears the lists before terrain objects load
their current triangles. The checked clearing function sets all 768 list heads
to null, and the checked search finds no floor in those cleared lists before
new triangles are added. Global Time Stop can skip the clear, but this is a
different setting from TTC's clock being stopped. Old triangles before a clear
and global Time Stop are timing qualifications, not established dust witnesses.

The TTC census includes its clockwork platforms, Thwomp, thirteen exclamation
boxes and blue coin switch. None of those behavior scripts sets the holdable
flag. The scripts that do set it belong to the Heave-Ho and two Bob-ombs, whose
normal behaviors do not provide standing platform triangles. TTC has no cork-box
descriptors; its exclamation boxes contain coins or walking 1-Ups.

This does not prove that the listed platforms cannot be cloned. It identifies
why cloning one does not automatically provide collision at its new position.
A reachable cloning sequence, suitable published floor, preserving Mario action
and accepted dust request remain to be established together.

## Why dust can affect random numbers

TTC cogs use the shared 16-bit gameplay random seed. Calling its `random_u16`
function changes that seed. Many unrelated objects can call the same function,
so the order and frame of every call matter. Audio has a separate random
generator; hearing a sound alone does not show that the cog seed changed.

Before counting dust's random calls, three separate questions must be settled:

1. Does the action request dust while preserving the spot?
2. Does the request survive the common cleanup after the action?
3. Does the particle system accept it and run the resulting objects?

The proof now executes the whole moving-action dispatcher around the checked
slide-kick body, under its stated starting-memory and movement-helper
conditions. At the specified dry cog height, healthy Mario with off-floor
input passes the water, stomp, squish and death cancellation checks. The
default-floor quicksand helper briefly sets depth to 1.1 and then resets it
to zero; both writes preserve Mario's position and stored floor. The real
action switch selects slide-kick sliding, and the dry cleanup retains its
dust and star requests. The complete result ends in backward ground knockback
with the same position and stored-floor fields. The two movement helpers and
the existence of that starting state remain conditions of this result.

The separate water-cleanup case removes dust and requests a wave trail
instead; the stars remain. Cancellation and default-floor quicksand processing
are also checked for backward ground knockback, but execution of that next
action's body in the successive cog state is still open.

There is another gate in the particle system. Mario's request flags and his
object's active-particle flags are different fields. If the active dust bit
is already set, the proof executes the complete particle-spawn function and
shows that it returns without allocating anything or changing memory. If the
bit is clear, the existing caller proof still assumes successful execution of
allocation and position copying. A dust request alone does not settle that case.
The allocation path also needs a change in the proof's semantic foundation:
standard CompCert represents pointers symbolically, while the game's address
conversion extracts bits from numeric N64 addresses. The existing model
cannot execute that conversion from a symbolic behavior pointer. This is a
limitation of the current proof model; it does not show that the game cannot
create dust. A proved N64 address connection must resolve it before those
allocation premises can be instantiated.

Once its runtime conditions hold, the checked dust chain is:

```text
Mario requests dust
  -> mist particle spawner
  -> two white-puff particles
  -> random X and Z offsets for each puff
  -> four dust-owned random_u16 calls
```

Thus, under the proved allocation, object-list, active-flag, and timing
conditions, the dust episode contributes four seed advances on its frame. If
other objects make `k` calls during the same window, the total is four plus
`k`, not simply four. The proof deliberately records those outside calls
instead of pretending they do not exist.

Parts of this chain have been executed directly in CompCert's formal Clight
semantics for both supported versions. The complete retail object loop and a
controller-only reachable memory snapshot are still open obligations. For the
slide-kick candidate, the accompanying vertical-star request must also be
followed through its consumers before the complete random-call order is known.

## Tic Tock Clock: spinners and cogs

Tic Tock Clock, usually shortened to **TTC**, is a level containing moving
clockwork platforms. Two relevant families are **spinners** and **cogs**. They
are separate game objects with different shapes and movement rules; "spinner"
is not a general name for every rotating TTC platform.

The proved interval later in this guide concerns only the spinner family. A cog
can still be part of a Pedro spot because the generic landing code does not care
what kind of object supplied the floor or ceiling. It only cares about the
surfaces it found, their overlap, and the gap between them.

### Spinners

The spinners used by the current proof tilt around a horizontal axis. Their
collision surfaces therefore change height as their pitch angle changes.

In the random clock setting, a spinner chooses a direction and a change timer
using the shared random seed. After a direction change, object timers 1 through
5 are stationary. The spinner then moves by 200 angle units at timer 6, another
200 at timer 7, and continues in that direction until its later change time.
The possible change timers are 30, 60, 90, and 120.

Changing the random seed can influence a future direction or timer choice. It
cannot retroactively change a direction that the spinner has already selected.

### Cogs

The game's `bhvTTCCog` object covers two shapes: a hexagonal platform and a
triangular prism. The pinned TTC level data lists eight cog placements: six
hexagons and two triangular prisms. Seven occur before the first spinner in the
object order already checked by the project's RNG census.

Cogs turn around the vertical Y axis, so their yaw changes their horizontal
footprint rather than tilting the whole platform up and down. That can still
create or remove the horizontal overlap needed for a Pedro spot. A lower cog's
top and an upper cog's underside are therefore legitimate floor/ceiling
candidates. The proof now checks the generated cog collision arrays, all eight
placements and their mappings, and one concrete overlapping pair at specified
angles. Its floor is at Y = -2088 and its ceiling at Y = -1934: a 154-unit gap,
within the Pedro branch's 160-unit limit. These calculations use the generated
game data and exact game arithmetic.

This is a certificate for the pair of surfaces. It does not yet prove that
the complete collision search selects that pair from a reachable Mario state,
or that successive action updates keep Mario there.

Cog motion also differs from spinner motion:

- on the slow setting, the cog speed is 200 angle units per frame;
- on the fast setting, it is 400;
- on the random setting, the current speed changes toward a target by 50 per
  frame; and
- after reaching a target, the cog uses the shared RNG to choose a new signed
  target from zero through 1,200 in steps of 200.

Each cog also has a fixed clockwise or counter-clockwise multiplier selected by
its level data. The game multiplies that direction by the current speed and
adds the result to the cog's yaw each frame.

This matters twice. First, dust manipulation could affect a cog's next target
speed and direction. Second, a cog choosing a target consumes random values of
its own, so cogs can change the seed seen later by a spinner or another cog.
The existing RNG census accounts for cog call sites, but it does not yet prove
a complete cog Pedro schedule.

The project also executes one complete generated cog update, including its
speed-approach and random-number helpers. In the checked random-mode example,
speed and target start at zero, the fixed direction multiplier is +1, yaw is
57344, and the seed is 16. The update leaves speed, target and yaw unchanged
while its two random calls advance the seed to 54874. This establishes one
stationary update from the stated memory conditions. Reaching those conditions
and keeping both relevant cogs fixed across successive frames remain open.

The new RANDOM-mode replay exposes a different starting condition: speed and
yaw are zero, but the two targets are already 800 and 200. Both cogs accelerate
to 50 and rotate by 50 before Mario acts. Neither cog requests a new target
on that update. The seed can affect a future target choice; it cannot change
a target already being approached. This failed start is recorded identically
in both US and JP and does not supply a stationary RANDOM-mode window.
The complete generated cog function is also proved to make that transition
from the stated memory conditions, preserving the disjoint RNG seed cell.
This new local execution result is part of the cog capstone; connecting the
retail snapshot to that formal memory and finding a successful starting phase
remain separate obligations.

Recorded RANDOM-mode experiments have reached individual close-gap air
returns, but the checked full paths fail to preserve the required Mario and
cog state across successive updates. The
[successive-update report](notes/ttc-cog-successive-updates.md) records these
limitations. Separate STOPPED-clock diagnostics check 30 successive off-floor
Pedro returns at the earlier position and now 1,200 at a newly searched
position, with both cogs fixed. These are positive finite stationary-geometry
controls; they do not establish a RANDOM-mode entry or RNG-controlled still
interval.

A short stationary window, such as four frames, could be useful if a preserving
action can produce an accepted RNG effect in time. Its length alone does not
establish that. Cogs update before Mario and the dust objects in the checked
object order, so dust cannot change a cog's earlier draw on the same frame.
The remaining argument must connect entry, action preservation, accepted
particles and every intervening RNG draw to the later cog decisions.

The [ground-pound investigation](notes/ttc-cog-ground-pound-successor.md) now
tests Z after four confirmed Pedro updates in that stationary control. In
both US and JP, Mario stays still during 15 startup calls, then loses the
inward floor query on descent. He drops 50 units, is pushed outward by wall
resolution, and enters backward air knockback without a ground-pound landing
or mist request. The following update moves him farther out. Both cogs remain
still, so more still time alone does not rescue this particular continuation.
Ten RANDOM-mode timings also produce no preserving impact and successor;
their mist-producing impacts occur after preservation has failed.

The later [geometry search](notes/ttc-cog-geometry-search.md) samples 64 angles
per cog in four selected pairs. It runs the actual collision routines in an
offline scene containing static TTC terrain and all eight cogs, while omitting
other dynamic objects. Of 35,684,352 position/pair-pose samples per version,
987,984 survive the geometry refresh and an ordinary-air close-gap return.
All are on the pair at macro slots 29 and 32. None retains the same XYZ and
floor through the tested zero-horizontal-speed first quarter of ground-pound
descent. This filters a precise fixed-position family; it does not execute
every candidate's complete game history or cover all positions and angles.

One selected position, `(1308, -2088, -1088)`, is then tested in the full
emulator in both versions. With the clock stopped and a constant stick input,
the first recording checks 94 updates while forward speed rises from zero
to about 41.31. That recording ends at its chosen cutoff, not because Mario
leaves. An [extended recording](notes/ttc-cog-1200-frame-hold.md) now checks
1,200 complete updates at the same XYZ, with forward speed reaching about
205.57. At the normal 30 game updates per second, those durations are about
3.13 seconds and 40 seconds. STOPPED mode already keeps the initialized cogs
still; it does not require or demonstrate RNG control.

The [input comparisons](notes/ttc-cog-random-1200.md) distinguish those two
requirements experimentally. Reducing the raw stick to `(40,15)` at frame 100
preserves the same position for 1,200 complete updates in US and ends at speed
31.25, but all 2,104 RNG draws match the original control. B on frame 4 followed
by A on frame 5 produces a dive and immediate forward rollout; it preserves
224 complete updates in US and JP, with all 391 draws matching the control.
An R camera toggle also preserves that 224-update window in US without changing
RNG. These are particular checked recipes, not all possible controller choices.

B without the following A loses the spot during the next dive-slide update.
The ground step initially retains the position, but the later floor-alignment
code places Mario at his distant floor height, -8191. That update requests
vertical stars while ending outside the Pedro spot. This does not establish
preserving RNG control, and it does not rule out the separate slide-kick path.

Pressing Z after four matched updates in the earlier recording instead gives
fifteen startup calls, then a descent that loses the cog floor and becomes backward
air knockback. The following update carries him farther away. There is no
ground-pound impact or mist request in that failure. Thus the search has found
another valid stationary hold, but still no preserving ground-pound impact.

Unsampled angles, positions and earlier-started descents remain open. The
[source review](notes/ttc-cog-ground-pound-rng.md) explains why an actual impact
could request mist without ordinary landing-dust speed requirements. Particles
advance RNG rather than resetting it; a useful sequence would still need both
cog decisions and all intervening draws accounted for. These are source
analysis and finite observations, not a new Coq proof or normal-entry witness.
The dedicated private
[Pedro-Coq research site](https://pedro-proof-notes.tra38.chatgpt.site) now
includes the geometry search, 1,200-update STOPPED hold, preserving-input
comparisons, local cog-departure proof, alternative-RNG findings and the video
review with exact scalar RNG checks, conditional scheduler-search bounds and
the historical STOPPED-derived and corrected RANDOM-phase seed-sweep results,
the one-cog/two-cog diagnosis, conditional brute-force runtime estimates and
preparation-count audit and local state-reduction checks.
The [publication record](notes/ttc-cog-site-publication.md)
identifies the published version and owner-only access check. Its verdict
agrees with this guide: a preserving
1,200-frame RANDOM-mode RNG strategy remains unproved. The official Sites
bundle was recovered through the connected resource catalog; the earlier
publication blocker is resolved. See the [publication record](notes/ttc-cog-site-publication.md).

## Does the video rule out 1,200 good RNG values?

The [video review and exact sequence checks](notes/ttc-cog-video-rng-sequence.md)
separate two questions. Checking a specified 1,200-update candidate is practical.
Finding a successful reachable setup is still difficult and unresolved. The
video itself correctly explains that the 65,114-value RNG cycle is not the
whole game state: other objects' timers decide which values the cog receives.
Its waiting-time graph describes forward search through simulated game time,
not the cost of checking one candidate.

Each zero-target selection uses a magnitude draw divisible by 7 and a second,
mandatory sign draw. Other objects add variable gaps between selections. A
finite check of the generated RNG function, cross-checked against unchanged
pinned C for all 65,536 seed inputs, finds a maximum of six consecutive good
raw values, also six for an isolated cog taking every other value. Across
fixed spacings of 2–64 draws, the maximum is seven. Those bounds do not apply
to TTC's changing schedule and do not refute the video's 12-frame example.

The new checker can find or exclude seeds for a supplied exact list of draw
indices. It even verifies an arithmetic-only 1,200-selection subsequence when
other consumers are allowed to absorb freely chosen numbers of draws. No
legal TTC schedule is established by that relaxation. A seed search for the
real game must recompute the objects' future decisions for each seed, then
check preservation and entry. A constraint solver over those transitions
could avoid naive enumeration of every state combination, but is not yet
implemented. The [tractability investigation](notes/ttc-cog-scheduler-tractability.md)
sharpens its possible guarantees. For one fully fixed non-RNG state and input
continuation, all 65,536 seeds require at most **78,643,200 frame evaluations**
over a 1,200-update window. Each seed generates its own object schedule; its
later random draws are not new independent search choices. This bound assumes
a faithful terminating update evaluator, includes no wall-clock promise, and
does not establish that the initial states are reachable.

Allowing `K` different preparations multiplies that count by `K`. Freely
varying more initial bits or future inputs can make the search exponential.
SAT/SMT and early rejection offer no general polynomial-time guarantee. A
proved small equivalent-state space or suitable constraint structure could
give a stronger bound, but neither is established for the full TTC search.
The subsequent bounded experiment implements that enumeration under an explicit
external-system model; it does not establish a full N64/Clight refinement.

### Can we estimate how long brute force would take?

**For a specified family, yes; for every possible preparation, not yet.**
Encoding the question as SAT does not prove this TTC family NP-complete, and
NP-completeness would not predict its wall-clock runtime. The existing seed
enumerator already gives a measured baseline: the corrected RANDOM US and JP
sweeps ran together in about **4 minutes 48 seconds** for 131,072 seed cases.
That is the sweep phase only, excluding capture, build, calibration and the
independent longest-seed replays.

If further preparation pairs have the same average cost and use the same
two-job concurrency, 10 pairs project to about **48 minutes**, 100 to **8
hours**, 1,000 to **3.34 days**, and one million to **9.14 years**. These are
conditional extrapolations, not runtime guarantees or estimates of when a
working strategy will be found. The [cost analysis](notes/ttc-cog-scheduler-tractability.md#measured-brute-force-cost-2026-09-23)
records the arithmetic and assumptions.

Every seed in that benchmark failed by its fourth update under the two-cog
ledge predicate, averaging about 2.021 attempted updates including the partial
failure. A full 1,200-update path, the actual spot-preservation predicate, or
different preparations may cost much more. We must benchmark those cases
before extending the timing claim. There is no complete TTC SAT implementation
or measured solver speedup yet. Other objects' initial states add preparations;
their subsequent draws are determined once the complete state, inputs and
seed are fixed. The preserving RANDOM-mode target remains open.

### How many preparations would that mean?

If the **complete state, seed and future inputs are all fixed**, there is one
execution per version. The earlier table fixes them per candidate, then varies
the non-seed state between preparations and the seed within a preparation.
Object timers and activation are already part of the complete state.

The [preparation-count audit](notes/ttc-cog-preparation-count.md) recomputes
the video's 4:00 table. Its approximately `1.0492 * 10^155` total already
includes 65,114 seeds; factoring those out gives about **`1.61 * 10^150`
non-seed combinations**. Applying our conditional full-seed US/JP timing to
that product gives about **`1.47 * 10^145` years**. The product has no proved
reachability or complete-state coverage, so this is not a necessary trial
count, a time lower bound or an impossibility result for a better solver.

A bounded existing family is countable. The matching 845-boundary US/JP
replay prefixes contain **26** distinct boundaries where either selected cog
meets the zero-target pause filter: 10 for the lower, 17 for the upper, with
one overlap. The longer 11,625-boundary **US-only** survey contains **196**:
107 lower, 90 upper, one overlap. At unchanged sweep cost, 26 preparation
pairs project to **2.08 hours** and a hypothetical 196-pair extension to
**15.70 hours**, excluding capture and validation.

Those boundaries are ledge-context pause opportunities, not valid Pedro
states. Only the existing 836-838 boundaries have complete checkpoints;
other phases need recapture, geometry, entry and preservation checks. JP's
longer prefix remains unverified, and the actual in-spot predicate may cost
more. This gives a bounded pilot size, not the number of all reachable
preparations needed to settle the target. One reachable preserving witness
could establish possibility without exhausting them all.

### Can we reduce the states we have to search?

**Yes for some local RNG schedules; a full Pedro-preservation reduction is
still open.** The [state-reduction audit](notes/ttc-cog-state-reduction.md)
implements exhaustive finite checks against the generated US/JP code and
independently compiled pinned C. A spinner's timer, threshold and direction
can become one countdown: **608 recurrent combinations become 121 states**.
Including an explicit broader family with timer-zero and initial-zero fields
gives **930 combinations and 122 states**. Those counts assume the stated
native-call and timer-increment boundary, not arbitrary gameplay resets.

For a cog, retain the signed target and number of updates until its next RNG
draw: **637 numeric speed/target pairs become 480 scheduling states**.
The 447,296 US/JP output comparisons pass. Partition refinement finds these
keys minimal for the checked local domains with arbitrary RNG input classes.
This is finite host evidence, not a new Coq theorem or full-game state count.

Discarding target sign is unsafe: with the same seed 38, starts at
speed/target `(+200,+200)` and `(-200,-200)` both draw twice, then consume
different numbers of RNG words on the second update. The video's 259 cog
states therefore cannot be justified simply by merging absolute values;
its table alone does not specify the simulator's full equivalence rule.

Matching RNG schedules also does not mean matching motion. Speeds 100 and
300 toward target 200 share our cog key but produce yaw increments 150 and
250. A solver must retain the motion needed for collision and Mario
preservation, and establish that dropped state cannot change activation or
other RNG consumers. The video already uses 121 spinner states, so that
local reduction cannot be applied again to shrink its huge product. No
certified total preparation count or new runtime bound follows yet, and
the preserving 1,200-update RANDOM target remains open.

### Why did both sweeps report only three updates?

**The video and the sweeps use different success conditions.** The video
counts one cog staying still; our sweeps require both selected cogs to keep
their yaws fixed. The [diagnostic comparison](notes/ttc-cog-sweep-diagnosis.md)
confirms this matters: from the same captured RANDOM phase, seed 13372 keeps
the lower cog still for four complete updates, and seed 48274 keeps the upper
cog still for five, while the other cog moves. Both were rejected after three
updates by the original two-cog condition. These examples agree in US/JP;
they do not establish that Mario remains in the spot when the other cog moves.

The video is also right that other objects' states create more combinations.
Changing their timers, phases or activation changes which RNG values reach
the cog. We varied seeds within very few starting configurations. For any
one fixed configuration and input continuation, each seed determines all
later draws and object decisions; extra calls are not freely selectable
independent choices. The seed sweep includes them, but does not enumerate
all the other initial-state combinations.

The repeated maximum is therefore not evidence for a universal three-frame
limit. The counts differ: 37 seeds reach three updates in the earlier family,
versus 25 in the corrected family. A rough independent-uniform estimate also
makes two simultaneous zero targets much rarer than one (`1/49` versus `1/7`
per extension), but this is intuition, not a proved probability model.
We need to identify the necessary cog constraint and check the actual spot
under the other cog's motion before comparing with the video's longer streaks.

### What happened when we actually swept the seeds?

**The first sweep used the wrong preparation family for the request:** it
changed STOPPED snapshots to RANDOM offline. The
[corrected experiment](notes/ttc-cog-random-seed-sweep.md) instead captures an
already-RANDOM phase, preserving its cog angles, speeds, targets and object
timers, and varies only the seed. It checks **all 65,536 seeds in each of US
and JP: 131,072 cases**. All fail by cog movement; the longest **two-cog** stationary
prefix is **three complete updates**, with zero unknown cases. Per version,
64,185 seeds last one update, 1,326 last two and 25 last three. The two
versions agree, and enumeration took about 4 minutes 48 seconds with two
concurrent jobs, excluding capture and validation.

That starting state occurs after 836 ordinary updates in RANDOM mode from
the authorized near-cog test placement. It was the only pause opportunity
for the original cog pair in an 11,625-frame survey. The captured yaws are
45,000 and -21,800; the upper cog's incoming speed 50 approaches zero during
its next update. The mode and cog fields are never rewritten by this sweep.
Alternative seed combinations are still hypothetical, and normal-entry
reachability has not been established.

**Mario remains on the ledge in this scheduling test, not in a Pedro spot.**
A separate geometry filter at the recorded angles finds 319 sampled close-gap
returns, of which 257 survive immediate geometry refresh. Those are local
candidates, not completed preserving actions or reachable entries. Moving
Mario into one of them changes object activity and needs a new complete-state
sweep. The current result does not exclude other RANDOM preparations.

The corrected evaluator includes a narrowly bounded animation-ROM transfer
adapter and matches the recorded one-, two- and three-update US/JP continuations,
including gameplay state, animation data and ordered RNG draws. OS/audio/device
effects are not fully modeled or proved irrelevant. This remains a finite
experiment under explicit assumptions; no Coq theorem or capstone premise
was discharged.

The **historical** [STOPPED-derived sweep](notes/ttc-cog-seed-sweep.md) tested **all 65,536 seeds for
three snapshots in each of US and JP: 393,216 cases**. None lasted four complete
preserving updates. The maximum was **three**; every rejection was caused by
a cog actually moving. There were no unknown or resource-limited cases within
this sweep. Enumeration took about 8 minutes 40 seconds with six concurrent
jobs, excluding setup and validation; that is a measurement, not a guarantee.

The snapshots come from updates 0, 30 and 100 of the same STOPPED hold. Only in
the offline evaluator, we set the clock to RANDOM and vary the seed while keeping
stick `(75, 28)` and no buttons. **These are hypothetical starting conditions,
not a demonstrated way to enter RANDOM mode with those states.** The three
different Mario speeds produced identical short RNG schedules and results, so
they add no observed scheduling diversity. Other RANDOM preparations, object
timers, cog angles and future input choices remain open.

The evaluator executes the compiled object scheduler, Mario, camera and
rendering separately for each seed. Its game-thread state and ordered RNG
draws were calibrated against 102 recorded STOPPED updates in each version.
In that earlier evaluator, audio, OS and hardware execution between updates are modeled only through the
declared boundary operations. A separate RANDOM calibration matches its first
frame; its next two frames in each version require unsupported device I/O and
remain unknown. Those four calibration cases are outside the exhaustive family.
This is a bounded experimental exclusion, not a Coq impossibility proof or a
proof against all ways to keep RANDOM-mode cogs still for 1,200 frames.

The video's `7^-1200` estimate assumes independent uniform selections. Its
state count and waiting-time extrapolation are not an exact impossibility
proof. Conversely, these new finite checks supply no successful RANDOM-mode
hold or in-spot RNG control. No Coq theorem or proof assumption changes.

## The proved TTC Pedro interval

This section is specifically about two **spinners**, not the TTC cogs.

The collision proof found one concrete cramped region shared by two spinners:

- floor: spinner 7, triangle 12;
- ceiling: spinner 0, triangle 4;
- common horizontal point: X = 1045, Z = 1603;
- certified pitch values: 15,664 through 16,031, inclusive.

There are 368 integer pitch values in that interval, or roughly two degrees of
a full rotation. At every certified pitch, for both US and JP:

- the point is strictly inside both triangles when viewed from above;
- the lower triangle is classified as a floor;
- the upper triangle is classified as a ceiling; and
- the computed vertical gap is greater than zero and at most 160.

These are not measurements copied from a video. The proof reconstructs the
triangles from the generated game data, applies the game's 32-bit floating-point
transformations and 16-bit terrain conversion, and lets Coq check every angle
table entry in the interval.

The widened interval contains one carefully chosen change of platform angle.
From pitch 15,864, direction `-1` moves the spinner by 200 units to pitch 15,664,
which is still certified.

It is not large enough for the next movement in the same direction. Two moving
frames produce a total change of 400 units. Starting anywhere in the certified
interval, either `pitch + 400` or `pitch - 400` is outside it. Coq proves this
for every possible random observation, because no random observation can alter
the already-selected direction between those two frames.

This checks the geometry at those angles; it does not execute Mario's actions
across the movement. Extending this spinner result would need other valid
intervals, a moving horizontal witness, or another preserving game effect.
Leaving this particular interval does not rule out other spinner arrangements
or the separate cog target.

## What Coq and Clight contribute

Ordinary tests run a few selected inputs. A Coq theorem instead describes all
values satisfying its stated conditions, and its proof is checked by a small
proof kernel. A rough C# analogy is the difference between a unit test and a
compiler-checked contract, except the contract itself must have a complete
mathematical proof.

The project uses three layers:

1. The decompiled C source is pinned to one exact revision.
2. CompCert's `clightgen` converts selected C files into Clight syntax trees.
   This is similar to inspecting a compiler AST rather than searching source
   text.
3. Coq definitions and theorems inspect those trees, calculate exact game
   arithmetic, and, where completed, execute functions according to CompCert's
   formal C semantics.

A **source receipt** proves that an expected branch, constant, field write, or
function call really occurs in the generated program. An **execution theorem**
is stronger: it proves how that code runs from a specified memory state. The
project labels these boundaries explicitly so a source-shape check is never
presented as a complete gameplay proof.

The build also rejects unfinished proof commands such as `Admitted` and checks
the important theorems for undeclared assumptions. Generated Clight files are
reproducible and are not edited by hand.

An explicit condition of a theorem can still be a substantial unfinished task.
For example, a theorem saying "if the sliding and ground helpers execute and
preserve these fields, then the caller does too" does not prove those helpers
or show that gameplay reaches their starting state. A successful build and
assumption audit do not remove conditions written into the theorem itself.

Two remaining boundaries also concern how the formal model represents the
retail game. Sliding calls the external square-root function `sqrtf`; checking
the retail instruction alone does not supply its formal execution contract.
Particle allocation reaches an address-conversion helper that performs integer
operations on an N64 address. CompCert normally represents a pointer as a memory
block plus an offset. The new local address proof now executes the original
helper numerically and proves that its result decodes to the same generated
dust script and byte offset. It uses the authenticated US/JP script addresses
and sizes, checks all their initializer words and relocations, and connects
the decoded result to the real allocation-header read. The loader's current
memory image and the complete allocator's use of this representation bridge
still need proof. The ordinary symbolic-pointer call remains unsupported in
standard Clight; the new result keeps the encode/execute/decode boundary
explicit. See the [address-refinement report](notes/ttc-cog-n64-address-refinement.md).

## What the all-RNG inventory establishes

### Bob-ombs, coins and the camera

A [reference video](https://www.youtube.com/watch?v=qoc4i4S4N5Q) demonstrates
switching a Bob-omb's activity by slightly changing Mario's height at a
red-coin **spinner** Pedro spot. The Bob-omb updates inside a 4,000-unit
radius, so crossing that boundary can change RNG consumption. The check uses
Mario's graphical root position; in the ordinary air-step path this is copied
from his actual position. Blinking does not necessarily draw RNG on every
active frame: an ongoing blink advances its timer without a new draw.

The known stationary-cog control keeps Mario at a fixed height on the same
flat cog top. Its repeated Pedro returns therefore do not supply the video's
height switch. The spinner demonstration does not establish the same control
at the cogs. Different actions or selected surfaces remain open candidates
whose whole preserving paths need checking.

Coin collection has a separate qualification. The ordinary coin-interaction
handler does not need a landing or move Mario. A live coin's own behavior then
creates sparkles, which consume RNG. But the standard non-holdable cloning
path replaces that coin behavior with a carry script. Such a coin can remain
collectible without running the sparkle-creation code. Hands-free holding
alone therefore does not establish a preserving coin-sparkle RNG source.
The 100-coin-star threshold is a separate branch, not covered by this ordinary
collection conclusion.

TTC does not enable snow or the proposed camera-dependent environmental
particles. Moving the camera does not change its environmental mode from NONE.
The existing NONE-mode execution theorem is described below. Other camera
shake paths must still be accounted for separately. These source findings add
no new Coq theorem or complete preserving gameplay witness; see the
[three-method investigation](notes/ttc-cog-alternative-rng.md) for the exact
conditions and remaining tests.

### The inventory and its execution boundary

The source inventory now covers 41 generated C compilation units per version,
including every Mario action group, interactions, camera and environmental
effects. Its structural checks account for 282 direct RNG call sites, 16
functions containing computed calls, 53 functions that write particle-request
fields, and all 18 entries in Mario's particle table. These are source-code
counts, not the number of random draws in a frame.

That inventory provides a checked list of places requiring analysis. A computed
call chooses its target at runtime, much like invoking a C# delegate, so listing
it does not identify which function runs in the cog state. Likewise, finding
every particle writer does not prove which writers Mario can reach while
staying in the spot.

One exclusion is fully executed under its stated starting conditions: the
environmental-particle update in its NONE mode returns with all memory unchanged,
including the gameplay seed. Connecting those starting conditions to normal TTC
entry still needs proof. The remaining action, particle, object and camera paths
must either be executed in a preserving state or excluded by proved conditions.
The exhaustive claim about all available RNG control in the cog spot remains
open. See [the all-RNG report](notes/ttc-cog-all-rng.md).

## What is known, and what is not

The project currently establishes that:

- the relevant Pedro landing branch exists in the generated US and JP code;
- the landing-speed calculation has input-dependent examples on opposite sides
  of the dust threshold for each flat-floor slowdown class;
- a concrete cog surface pair has a certified 154-unit gap, and one complete
  cog update preserves its angle under explicit starting conditions;
- the slide-kick sliding caller requests dust and stars while preserving its
  checked position/floor fields, conditional on two remaining helper executions
  and their preservation conditions;
- the complete dry moving dispatcher selects that slide body, preserves its
  position/floor result and keeps those requests; its separate water-tail case clears dust,
  and an already active dust bit makes the spawn function skip allocation;
- the checked dust path owns four random-seed advances under explicit runtime
  conditions;
- the broader RNG and particle source inventory is checked; and
- the earlier spinner geometry spans pitches 15,664--16,031, with one selected
  200-unit angle change inside it and two successive changes in the same
  direction leaving that fixed interval.

The project has **not** yet proved the final gameplay claims. In particular, it
still needs:

- a controller-only route into the cog Pedro state in both supported versions,
  followed by actual successive updates that preserve Mario and the relevant cogs;
- execution and preservation proofs for `update_sliding` and the full
  `perform_ground_step`, including the actual surface selections;
- a reachable state satisfying the complete dispatcher's entry conditions,
  airborne slide-kick entry/bounce and the following knockback update;
- accepted particle allocation, integration of the proved local N64 address
  connection into the full caller path, and the complete
  dust/star behavior chain in a reachable object-pool and object-list state; and
- preserving input choices or proved exclusions for all relevant RNG sources,
  with their ordered draws connected to future cog decisions.

The current proofs leave both the sustained cog entry and preserving RNG
control unresolved. The [checklist](checklist.md) tracks the individual remaining
obligations.
