# Higher enemies, cloned enemies, and what the bounce actually buys

The earlier Y=768 limit was a condition of one local proof. It was never a
requirement for an enemy to activate the warp, and it is not a bound on every
enemy in SSL. Two fire Fly Guys start at Y=800 and Y=1160; one Klepto placement
starts at Y=1174. Cloning also makes a stock spawn position an inadequate
all-history bound. We keep the earlier theorem, with its conditions, rather
than extending it to actors it does not cover.

A high bounce and a large position gap are different things. Mario can fly
far above an enemy while his displayed position follows him. Ink needs the
right records to disagree at the checks; altitude alone does not supply that.
Original's example uses a 1170.864868-unit display/movement gap. Variant uses
a 1093-unit movement/collision gap. Neither is a universal minimum.

“Fresh bounce” means a new enemy bounce without an inherited position gap;
it does not mean simultaneous warp activation. In the ordinary interaction
pass, the warp handler precedes the enemy-bounce handlers. A successful upper
warp stops that loop before they run, even if both objects are in contact.
The bounce would have to happen earlier and leave useful separation alive
until the later warp check. Its purpose would be to create the split before
warp acceptance; we cannot rely on stored upward speed producing ordinary
flight afterward. The later disappearance/geometry work is a separate
sequence, not continued bouncing. This is the existing accepted-warp short-circuit,
not a newly proved all-history timing exclusion.

## What legitimate cloning changes

The source explicitly describes a pickup animation outliving its used
object's unloading. The pickup then reads the same pool slot, which can now
be vacant or occupied by a different object. The held-state helper changes
the parent and, for a non-holdable replacement, installs an inert carrying
script. It does not copy Mario into another Mario or manufacture arbitrary
enemy dimensions. The enemy can keep the interaction type, scale and hitbox
already present in that reused slot while its normal behavior is frozen.

Dropping uses the held-object position for X/Z and Mario's movement Y for
height. Throwing uses the held-object position, with a horizontal offset.
That makes relocation relevant, but it still needs a legitimate pickup-slot
history, the appropriate live dimensions and tangibility, an accessible drop
or throw position, and an actual later contact. We have not constructed such
a clean no-A enemy placement at the pyramid top. The concrete native SSL
callbacks spawn Pokey parts, while the named Goomba/Fly Guy/Klepto examples
are normally level-entry actors. A chosen replacement species needs its own
slot-filling explanation. Arbitrary placement is not an accepted assumption.

These are pinned-source findings, not a completed Coq classification of
cloning. The relevant code is `mario_actions_object.c`'s pickup comment and
action, `interaction.c`'s `mario_grab_used_object`, `mario_drop_held_object`
and `mario_throw_held_object`, and `object_helpers.c`'s `obj_set_held_state`.
The carrying scripts are `bhvCarrySomething3/4/5` in `behavior_data.c`.

## A bound which does not depend on the enemy's spawn height

The actual hit-from-above branch compares movement Y with the enemy's raw Y.
Mario must be above that enemy. The bounce then snaps movement to enemy Y
plus the live hitbox height. Consequently, making the enemy higher does not
give an equally large newly created split: Mario already had to be higher
before the contact.

[InkBounceApproachGap.v](../../proofs/InkBounceApproachGap.v) connects that
generated US/JP branch to the real bounce height store. With finite movement
Y in [-32768,32768], actor Y at least -32768, and finite live hitbox height in
[-32768,250], the upward change is at most **251 units**, including a
conservative one-unit binary32 rounding allowance. There is no actor Y≤768
condition and no assumption that the actor is not cloned. The actual compared
movement/actor values must still match those read at bounce entry. If display
initially equals movement, the other-block frame carries that old display
into the snap, giving the same bound on the newly created upward
movement/display gap. An inherited split is not bounded by that claim.
When collision also starts at that compared movement height, the additional
three-record corollary protects its real raw-Y cell and gives the same 251
bound on newly created movement/collision separation. This bounded fresh
snap alone cannot create Variant's 1093-unit split from synchronized records.
This is a signed upward bound, not a bound on every gap direction.

The live height limit is still a condition. Nominal regular Goomba, Pokey,
Fly Guy and Klepto heights are 75, 60, 90 and 250. Fire Fly Guy's temporary
growth and repeated shrinking mean its dimensions need their own history
argument; an inert held clone can retain an earlier dimension. The template
list alone does not discharge that argument. Negative dimensions also affect
contact eligibility. The earlier passed contact-height result separately
prevents a snap below the compared collision bottom when its actor-top reads
match; a negative-height numerical example alone is not a working contact.

## The later air step

[InkAirCallBackward.v](../../proofs/InkAirCallBackward.v) follows a completed
real air-step call through its quarter loop, terrain helper, gravity and wind
to its mandatory real display copy. The actual prefix is retained as one
execution; we do not assume its calls harmless or replace it with a sampled
flight. A quarter-step break does not return from the outer function before
this copy; a completed call also reaches it after a missing-floor outcome.

[InkAirReturnFrame.v](../../proofs/InkAirReturnFrame.v) completes that copy,
the real angle setter, return and local free. Under the ordinary readable,
separate MarioState/Object-pool storage conditions, display Y equals movement
Y when the air-step call returns. The collision Y at the copy cut is
preserved. This works independently of enemy position, velocity, floor-query
success and whether the enemy was cloned. It rules out carrying an old
movement/display gap through this completed call. It does **not** make all
three records agree or frame the action's later calls, the later raw copy,
the prior bounce sound call, or the next update's contact checks.

## Flight height is not the surviving gap

[InkBounceClearAscent.v](../../proofs/InkBounceClearAscent.v) checks clear-air
calculations using four binary32 quarter additions per update,
followed by subtracting four from vertical speed. A 30-speed unchanged
default-gravity ascent adds **128** over eight positive-motion updates. An
80-speed normal twirling ascent adds **840** over twenty. Starting from the
earlier bounded snap Y=1018 would give peaks 1146 and 1858 respectively;
starting from 1250, the latter gives 2090. These specified arithmetic profiles
are not runtime witnesses or general flight maxima. Actual floor snaps,
wind, action changes and additional contacts can change them.

The 30-speed bounce retains the prior action, so different gravity can matter.
Requesting twirling can also be converted to ordinary jump when Mario is
squished or depth is at least one, setting a different speed. We have not
proved a universal peak for every allowed bounce history. More importantly,
the completed air step follows movement with display: a large rise is not
an equally large surviving movement/display gap. No new gameplay-created
bounce gap has been measured here. The previously reviewed conditional
dialog gap of 1834 remains a different, supplied-seed result which refreshes
on release and gives no Ink.

## Verdict and the remaining producer question

The fresh bounded snap and completed air-step refresh are scoped local
exclusions. They make the earlier “enemy Y≤768” restriction unnecessary for
those claims. The complete bounce/knockback family remains open: establish
legitimate enemy placement and dimensions, contact-to-handler read continuity,
the actual action/copy sequence, and whether a later writer or interruption
preserves a useful collision split before the next warp check. Walking off
a ledge gives a no-A way to fall, and a Fly Guy can request twirling without A;
neither fact constructs the useful installation pose. We have no new clean
Ink witness, no all-history exclusion, and no revised counterexample estimate.

Validation: selected pipeline audit `20261004-205950-f1u_292y` passes
compilation, proof-hole/link discipline and all 21 selected assumption checks
across 638 registered sources. The main backward boundary has nine allowed
foundations, the new execution boundary and individual execution claims have
seven, and the finite ascent certificate has four. Integration reports
466/560 proof modules in the main import closure, with 94 standalone and no
problems. These checks do not discharge the explicit gameplay premises.
No emulator search was run in this tranche.
