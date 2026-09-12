# Rank 11 clean Goomba installer audit

## Result

No clean stock Goomba installation was found. The finite graph gives no path from any of Area 2's nine damaging Goombas to the second-pole ring under its listed short-transfer rules. It does **not** prove that those rules cover every ordinary gameplay approach. The later [elevator approach check](rank10a-elevator-coins.md#can-a-goomba-get-close-enough-to-be-defeated) confirms that hard falls can give Goombas rebounds stronger than their normal jump; long airborne transfers and repeated collision pushes need their own coverage. The Goomba H/F/R partial-update glitch and other position or support changes also remain separate.

## Why a correctly installed Goomba would work

The existing relocated-Goomba experiment established the damage payoff but did not establish installation. The source facts sharpen that result:

- A regular Goomba has radius `108` and height `75` after its `1.5` scale is applied.
- Mario's relevant hitbox radius is `37`.
- The nearest ring edge is `102` units from the pole centre, less than the combined horizontal radius `145`.
- A Goomba standing on the ring at Y=`3942` reaches only Y=`4017`, three units below holding Mario at Y=`4020`; standing contact is therefore insufficient.
- `goomba_begin_jump` gives a regular Goomba Y speed `25`, and its first standard movement applies gravity `-4`, placing its base at Y=`3963` and its top at Y=`4038`. That one ordinary jump update is sufficient for vertical overlap.
- Pole holding is not classified as Mario attacking from above, so this contact can select ordinary damage rather than a stomp. The previously authenticated retail fixture then crosses the opening and lands on the ring with zero A presses.

Handstand height is therefore optional. A clean counterexample needs only to install a regular Goomba on the ring, make it begin a normal jump while Mario holds the pole, and connect the already-checked damage departure to the target-star continuation.

## Complete stock Goomba census

The generated US and JP macro arrays agree. Area 2 contains six singleton regular Goombas and one triplet spawner. Expanding the triplet with the pinned sine table gives nine damaging actors in total:

| Origin | Initial position | Initial static floor/component |
|---|---:|---:|
| Singleton 1 | `(3263, 778, 3157)` | Y `640`, component `47` |
| Singleton 2 | `(3389, 0, -1978)` | Y `0`, component `0` |
| Singleton 3 | `(-3638, 0, 1928)` | Y `0`, component `0` |
| Singleton 4 | `(3263, 652, 2200)` | Y `640`, component `46` |
| Singleton 5 | `(3431, 673, -1373)` | Y `640`, component `45` |
| Singleton 6 | `(-2100, 0, 3316)` | Y `0`, component `0` |
| Triplet child 0 | `(3681, 0, 3587)` | Y `0`, component `0` |
| Triplet child 1 | `(2932, 0, 4020)` | Y `0`, component `0` |
| Triplet child 2 | `(2931, 0, 3155)` | Y `0`, component `0` |

There are no huge- or tiny-Goomba macro presets in Area 2. The triplet's default behavior parameter also produces regular Goombas. This corrects the first diagnostic pass, which used the non-damaging spawner's centre as a seventh placeholder instead of expanding its three children.

## Static movement audit

The reproducible analyzer reads the pinned Area-2 collision source directly. It finds `1080` vertices, `1558` triangles, `534` upward faces classified by the engine as floors, and `81` shared-edge floor components. The target ring is component `74` at Y=`3942`.

The transition graph intentionally favors finding a route:

- grounded chase movement may bridge `30` horizontal units while accepting the source floor tolerances;
- jump-floor selection may snap to an overlapping floor as much as `144` units above the departure floor—the exact jump reaches `66`, and `find_floor_from_list` admits another `78`;
- the separate pair graph grants a full `216`-unit horizontal transfer, twice the scaled Goomba radius, without requiring the two actors, yaw, collision order, or controller timing actually to realize it;
- walls, native-room restrictions, and controller feasibility are omitted where omission makes movement easier.

Even under those allowances, no start component reaches component `74`. The Y=`0` family reaches only components `0, 56, 58, 59, 60, 61, 62, 63`, with maximum source-vertex Y=`113`. The two eastern Y=`640` starts reach components `46, 47`, with maximum Y=`640`. The remaining Y=`640` start reaches `20–26, 45, 48, 49, 51–53`, again with maximum Y=`640`. The independent `216`-unit pair graph also returns no path for all nine actors.

This graph does not assume that a Goomba stays near home. The source's chase-extension bug may permit enormous **horizontal** travel, so the audit permits component travel without a home leash. What it does not provide is a vertical connector between the low components and the ring.

## Moving-support audit

The reviewed low-tier lift is the vertical Grindel at `(3297, 0, 95)`. Its collision top spans X=`3073..3521`, Z=`-129..319`, and local Y=`450`. Granting the favorable case in which pair separation places a Y=`640` Goomba on it as the top passes that height, the stock raise reaches base Y=`695`, so the highest top is Y=`1145`. Every static floor component within `250` horizontal units of that footprint is at Y=`-101`, `0`, `72`, or `640`; there is no upper discharge floor. The `250` search radius exceeds both ordinary movement (`30`) and the deliberately generous single pair transfer (`216`). This excludes a nearby discharge in the checked graph; it does not cover every airborne departure from the lift.

The lower horizontal Grindel begins with its top too high for a Y=`0` Goomba's ordinary jump plus `78`-unit query allowance, while the upper horizontal Grindel, Spindel, moving walls, and elevator belong to higher tiers that the finite static/pair graph never reaches. The elevator moves downward only after Mario is already on it. No stock low-to-ring chain was found in this graph.

## What is proved, and what is not

`Area2Rank11GoombaInstaller.v` mechanically checks the selected US/JP roster, absence of huge/tiny variants, regular hitbox initializer, regular property prefix, jump source constants, the `78`-unit floor-query constant, and that Goomba pair resolution does not directly assign Y. It also checks the contact arithmetic and the reviewed finite mesh/lift receipt. `analyze_mesh.js --check` recomputes that receipt from the pinned collision source and fails if any reviewed count, component, spawn floor, reachable set, or path result changes.

The negative result applies to paths in the stated finite graph. Coverage of actual ordinary updates remains unproved: an airborne Goomba can cross more than one short-transfer radius before its next landing, and a hard landing can produce a stronger rebound than the normal jump. Even an ordinary jump can resume walking during its small landing rebound, before the `ON_GROUND` edge restriction applies; the [stock western approach check](rank10a-elevator-coins.md#can-a-stock-goomba-reach-the-west-wall-position) identifies a concrete rim to investigate. The checked constants and graph receipt remain useful, but proving that all relevant live trajectories map to graph edges is a separate obligation. A missing graph edge is not a gameplay impossibility result.

The following remain outside this verdict:

- long airborne departures, hard-fall rebounds and repeated collision pushes not represented by the graph's transfer rules;
- H/F/R raising, which needs a same-frame cached collision followed by a clean raw-Mario departure of more than `4000` units and can add `21` units per successful cycle;
- a stale, relocated, forged, or type-confused object or floor owner;
- an in-bounds alias or specified outside call that writes actor position, velocity, floor, action, or collision state;
- OOB writes, DMA, or ACE, which are outside the selected CompCert model;
- a non-Goomba shove, clip, changing support, or outside effect;
- a live trace that falsifies one of the source-to-mesh premises.

There is no ordinary lower-entry-to-star input movie to connect. A surviving counterexample must first supply a real actor approach, including any fall, rebound or support transfer absent from the graph; after that, it must carry that actor through contact, damage, every collision quarter, ring landing and star collection without staging writes.
