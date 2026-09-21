# Ground-pound mist as a cog Pedro RNG candidate

Source review on 2026-09-20, for `VERSION_US` and `VERSION_JP` at
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. This note adds no Coq theorem.
The later [impact-and-successor investigation](ttc-cog-ground-pound-successor.md)
tests the candidate from a verified stationary-cog Pedro hold and records a
finite failure, independently reproduced in US and JP.

**Verdict: candidate, not demonstrated and not generally disproved.** A
ground-pound landing can request gameplay-RNG-consuming mist without the
ordinary landing-dust speed threshold. It remains unproved that Mario can
reach that branch while staying in the off-floor cog Pedro state, keep the
cogs in the required poses, and obtain a useful subsequent RNG history.

The direct tested continuation now fails even with the ordinary STOPPED clock
setting: after four matching Pedro updates, 15 startup calls hold Mario still,
then the first descent loses the cog floor query and enters backward air
knockback without a landing. The following update moves farther out. The
control holds for 30 updates; ten RANDOM-mode Z timings also produce no
preserving impact/successor. This isolates a geometric failure at that
placement, not an impossibility theorem for other poses or earlier descents.

## What can produce the particles

In `act_ground_pound`, the descending phase calls `perform_air_step`. Its
`AIR_STEP_LANDED` branch can request `PARTICLE_MIST_CIRCLE`: the stuck branch
requests mist, and the ordinary non-damaging branch requests mist plus
`PARTICLE_HORIZONTAL_STAR` and selects `ACT_GROUND_POUND_LAND`. Unlike
ordinary landing dust, these requests have no forward-speed-above-16 test.
The request is in the air action itself; cancellation of a later landing
action does not prevent this earlier request.

Consequently a close-gap return could, in principle, supply the landing
result even without a supporting floor beneath Mario's retained X/Z. The
question is whether the preceding ground-pound path can still produce that
query. Neither a mist request nor one `AIR_STEP_LANDED` return proves this
preserving path exists.

The generated US/JP particle catalogue maps mist circle to
`bhvMistCircParticleSpawner`. Its initializer, `bhv_pound_white_puffs_init`,
calls `spawn_mist_from_global`, which calls `cur_obj_spawn_particles` with
`sGlobalMistParticles`. That helper contains gameplay RNG calls for particle
scale, angle and velocities. Its requested count is reduced or suppressed
when the preceding object count is high. The spawner must also be accepted
and executed. This is a source-level chain, not a newly discharged allocator,
scheduler or whole-frame execution proof. The slide-kick dust draw count
must not be substituted for this different particle path. Ground-pound
impact also starts a camera-shake effect, whose execution belongs in any
complete count of the resulting RNG draws.

## Why losing speed can lose the mechanism

The cog Pedro return uses the floor and ceiling at the wall-resolved
**attempted** position. A gap of at most 160 makes the landing branch retain
the old X/Z and floor reference while setting Y to the queried floor height.
The actual retained position can still be off that floor on the next update.

Ground-pound startup repeatedly sets forward velocity to zero and calls no
air-step routine. During its first ten timer values it can also raise Y if
the ceiling test allows it; a close ceiling can prevent that rise. Removing
the inward displacement can make the later floor query fall outside the cog,
so the loss of speed can remove the collision mechanism, not merely reduce
the amount of dust. Wall resolution or a different authenticated geometry
could change this outcome; zero speed alone is not a universal impossibility
proof. A stationary startup snapshot also does not establish that the later
descending and landing updates preserve the spot.

With the normal `loopEnd = 11` animation descriptor and a fresh timer,
startup takes 15 action updates (`loopEnd + 4`). The air-step branch starts
on a following action update. A fresh, uninterrupted normal ground pound
therefore cannot generate its landing mist within four startup updates.
Entering the spot after an earlier startup, or arranging a longer still
interval, would require a separate preserving history. The
[new paired replay](ttc-cog-ground-pound-successor.md) also observes these
15 startup calls directly in the cog setup.

After an ordinary impact, `act_ground_pound_land` can return to freefall on
`INPUT_OFF_FLOOR`. That does not restore the former inward speed or establish
that another ground pound can be triggered while preserving the spot.

## What the existing trials actually show

The [US/JP detour trial](ttc-cog-detour-followup.md#ground-pound-reaches-the-branch-but-fails-preservation)
does produce mist and horizontal stars after a 154-unit-gap return. However,
the moving cog has already carried Mario, and the selected floor is already
his supporting floor at impact. It fails preservation before the particles.
The earlier [inner-rim continuation](ttc-cog-floor-actions.md) produces mist
only after falling to a lower platform. Neither trial disproves every other
ground-pound setup, and neither supplies in-spot RNG control.

## What a useful RNG search would need

Particles **advance** the shared deterministic gameplay RNG; they do not
reset it or select an arbitrary seed. A search over ordinary input timing
could still find a useful sequence, but first it needs a preserving impact
and the exact accepted particle/object/camera executions. Both cogs' RNG
decisions and intervening draws must be counted in their actual order; the
cog updates precede these particle effects, so a later effect cannot change
a cog decision already made that frame. See the [cog plan](ttc-cog-plan.md).

One successful preserving impact would justify searching its reachable RNG
continuations, including any naturally long still interval it produces.
Repeated ground pounds are not automatically required if one reachable
continuation already lasts long enough, but repeatable controller control
must be proved separately if the proposed strategy needs it. The next
concrete witness is a complete entry/startup/descent/impact/following-update
path with retained and attempted positions, selected surfaces, both cog
poses, action transitions, accepted particles and ordered RNG draws.
