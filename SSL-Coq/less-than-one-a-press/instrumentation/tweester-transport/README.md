# Tweester transport toward the upper SSL warp

24 September 2026. **Finite native source diagnostic, not a controller replay
or a Coq impossibility proof.** This tests the rapid-home-oscillation lead
described in the user's [video reference](https://www.youtube.com/watch?v=P-Hy6zzWiE4).
The video could not be fetched here; its supplied description was checked
against the pinned source instead. No claim to have watched it is made.

## What the stock code supports

`tweester_act_chase` chooses between turning toward Mario and turning toward
home. The first choice requires Mario's horizontal distance from home to be
below the activation radius, and the chasing subaction to remain selected.
The stock radii are 1,800 for the western Tweester at `(-3600,-200,2940)` and
2,500 for the two at `(1017,-200,3832)` and `(3066,-200,400)`. The latter two
are selected only in acts 4–6. Steering changes by at most `0x200` per update;
movement uses speed 20 before the scaling helper sets the stored speed to 14.
That limited turn rate is why rapidly changing the target is interesting.

Returning within 200 horizontal units of home selects hiding. A full
three-dimensional Mario distance **greater than 3,000** also selects hiding,
which subsequently shrinks the Tweester; it is not an immediate object
deletion. The chase branch additionally watches for Mario's `ACT_TWIRLING`
action after ejection and increments its subaction, committing it to the
return-home branch. This is distinct from Mario's captured
`ACT_TORNADO_TWIRLING` action. Ignoring capture/ejection can therefore invent a
transport path that ordinary play cannot follow unchanged.

## What was tested

The builder extracts 46 unchanged C functions from source revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`: real Tweester chase/scaling,
turning, floor/wall and object-movement helpers, static surface loading and
hitbox overlap. It verifies each body against the decomp repository's pinned
revision. It decodes the identical generated US/JP Area-1 mesh: 962 loaded
surfaces and 4,346 list nodes. The manifest also records the generated US/JP
Tweester function slices. Running native C is not executing those Clight
bodies, and the slice hashes are not an execution proof.

The driver supplies Mario on one fixed ray from home, at radius R−2 or R+2.
An initial inside-range chase lasts 15, 20, 45, 60 or 90 updates; then each
inside/outside phase lasts 1–8 updates. It checks 128 ray angles for all three
actors. A finer western pass uses 1,024 angles and a 30-update initial chase.
Each trial stops at hiding, the first reported hitbox overlap, or 9,000
updates. This is **188,416 prescribed schedules per version**, not that many
valid controller histories. US and JP produced identical receipts.

Important grants and omissions:

- The actor starts in the chasing subaction at its home floor. Its initial
  heading is supplied along the chosen ray, and a supplied full-size scale
  phase is used. The growth/spawn/controller predecessor is not constructed.
- Mario's position is supplied directly to this isolated diagnostic. His
  movement, action physics, safe footing and ability to alternate those
  positions are not simulated. Even a four-unit switch is not automatically
  a valid controller input sequence.
- The stock hitbox-overlap function is used to **reject** a prescribed path
  once contact occurs. This does not implement Mario's capture or the full
  collision scheduler, intangible-state rules or other interactions.
- Only static Area-1 terrain is loaded. Water regions, dynamic top and other
  actors, particles, sound and the complete object scheduler are omitted.
  Presentation/particle calls are stubbed explicitly. No gameplay memory is
  modified: this is a separate source-mechanics executable.

## Results

The nearest sampled Tweester centers before the stopping conditions, measured
horizontally from upper-warp center `(-2048,-1024)`, were:

| Actor | Nearest distance | Position (X,Y,Z) | Initial chase / ray / inside / outside |
| --- | ---: | --- | --- |
| West | 1980.45911 | (-3270.7168,256,533.94165) | 15 / 40960 / 3 / 5 |
| Southeast | 1993.03235 | (-934.729126,256,629.120178) | 15 / 30720 / 3 / 4 |
| Northeast | 1670.98633 | (-377.072693,107,-1009.94574) | 15 / 37888 / 3 / 4 |

None reaches useful warp proximity in this tested family. This is not a
coverage argument about changing rays, moving around the home circle,
different starting headings/phases, airborne Mario, interruptions or all
controller histories. The exact output is in [expected-results.txt](expected-results.txt).

An exploratory pass which **ignored capture** appeared to bring the western
Tweester within 798.338379 units of the warp center, at
`(-1498.14001,1199,-445.209686)` on update 703. Its prescribed Mario trajectory
cannot be accepted as a route: overlap already occurs on update 57, and it reaches
the 3,000-distance hide trigger shortly afterward. The contact-aware passes
above replace that attractive result as gameplay evidence.

## A conditional ledge contact survives the size test

A separate `terrain 1` diagnostic grants direct heading control, first toward
`(-4200,-1024)` and then toward the upper warp. It runs the real wall/floor
and movement helpers, but bypasses home steering and the Mario-distance
trigger. The western actor reaches the upper western approach and is blocked
near `(-2979.89648,880.013916,-1022.63019)`. This is a relaxed terrain result,
**not a successful oscillation route** or proof of a stable gameplay jam.

At that supplied pose, the widest regular scale gives hitbox radius 780 and
height 800. Mario at the supplied Ink contact position `(-2200,768,-1024)`,
with radius 37 and height 160, overlaps it: Mario's top is Y=928, above the
Tweester's base Y≈880. He also overlaps the radius-150 upper warp. The
`contact` fixture executes the unchanged overlap function for both contacts
and asserts success in both versions. It grants the two poses and the scale
phase, does not make Mario's low pose reachable, and creates no display gap.

Thus the Tweester need not have its center exactly on the warp for contact
to matter. But we still need an actual oscillation route to such a position,
with Mario avoiding unwanted capture and the distance-triggered hide.

## Does capture or a later action supply Ink?

The existing [TweesterGap proof](../../proofs/TweesterGap.v) still applies to
its normal continuation regardless of the Tweester's location: either floor
result reaches the real movement-to-display copy. The new source review
checks the ordinary exit as well: ejection occurs before the position-update
branches and returns `set_mario_action(...ACT_TWIRLING,1)`. The setter returns
true, so the ordinary action loop continues. If common cancellations do not
intervene and `ACT_TWIRLING` is retained, `act_twirling` calls `perform_air_step`,
which copies movement to display after its quarter steps. Its landing case
changes the action after that copy and returns false. Simply being ejected,
falling or landing is not an identified large-gap producer.

Those exit observations are **source analysis**, not a newly completed Clight
callee-frame theorem. Earlier interactions, water/squish cancellations,
star/dialog interruption and a separate later position writer remain outside
the old normal-copy proof. The automatic dispatcher also clears quicksand
depth before the normal Tweester action, so carrying a negative seed through
that dispatch cannot be silently assumed.

There is also a timing obstacle to using simultaneous warp/Tweester contact:
the interaction table checks the upper nonfading warp first. If that handler
accepts Mario, its successful return breaks the handler loop before the
Tweester handler runs. A lift caused by this same contact cannot retroactively
create the gap at the accepted-warp checkpoint. An earlier producer is still
needed. Neither the conditional overlap nor these source observations close
all later-action histories or establish Ink installation.

## Reproduce

Run from the active project in the established WSL environment:

```sh
bash instrumentation/tweester-transport/check.sh
PROBE_VERSION=JP bash instrumentation/tweester-transport/check.sh
bash instrumentation/tweester-transport/run.sh terrain 1
bash instrumentation/tweester-transport/run.sh contact
```

The checker prints results for comparison with `expected-results.txt`.
The source extraction, binaries and manifests remain under
`build/instrumentation/tweester-transport/`. A trace can be reproduced with
`HORIZON=9000 ANGLE_STEP=64` and arguments `0 20608 6 5`; without
`AVOID_CONTACT=1`, this intentionally keeps running after contact and must
not be presented as a gameplay route. All atlas estimates are unchanged.
