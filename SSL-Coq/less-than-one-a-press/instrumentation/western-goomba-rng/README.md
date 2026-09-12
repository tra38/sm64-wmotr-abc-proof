# Western Goomba with favorable RNG outcomes

This offline source-mechanics diagnostic checks the route from the stock
singleton `(-3638,0,1928)` toward `(-3071,113,1928)`. It neither modifies nor
runs a ROM. It is not the selected Clight program or a full gameplay witness.

From the active SSL project in Ubuntu/WSL:

```sh
bash instrumentation/western-goomba-rng/check.sh
```

Outputs remain in the active project's ignored
`build/instrumentation/western-goomba-rng/` directory. The script extracts
57 C functions unchanged, compares each slice with the revision pinned by
`pipeline/generate-clight.sh`, and records a manifest. Both generated US/JP
collision initializers must agree. The real static loading, cell insertion,
floor selection, wall correction, walking, jumping and movement functions
are used. Native headers, pointers and libm do not replace CompCert semantics.
The check runs both versions with GCC's undefined-behavior checking.

## Granted random choices

No RNG schedule is required. The branch search grants independent favorable
outcomes and verifies in the actual RNG cycle that both signs, the turn/jump
alternatives and all normal walk durations occur. Normal choices are a
45-degree turn with timer 100..199, or a jump with a 135-degree turn. The
source's turn limit, collision responses, home behavior and jump speed reset
remain in effect. Outside the home radius the search chooses the legal
timer 20; it does not enumerate all 20..49 choices there.

While Mario stays inside the bucket, this western Goomba cannot enter the
normal fast-chase branch. Its normal target speed is 2, and the 1000-unit
home test can override random wandering. Wall/object avoidance can delay
returning home: this is not a claimed 1000-unit position bound.

## Straight-wall checks

At Z=1928 a wall rises from Y=0 to 72 at X=-3112. The 40-unit wall radius
pushes the Goomba's center to X=-3152 before movement. The wall query uses
integer position plus a Y offset of 10. The diagnostic checks 2,457 low wall
poses and 5,320 floor queries over X=-3152..-3113, Y=0..132 at Z=1928. In
these static lists the wall pushes to -3152 and the floor is zero. A Y=63
wall fixture clears the wall. These are finite static-list checks.

The vertical checker explores a finite **closed state set**, rather than a
fixed number of frames. It grants a jump on any walking update, even when
the real timer would forbid it, and horizontal speed 2 without drag when
walking can move. It allows optional integer Y correction at low wall
passes. The extracted jump and vertical movement routines are used; the
driver supplies the flat floor and conservative horizontal advance counter.
Other actors and changing supports are absent.

| Granted case | States / edges | Highest moving query Y | Advance beyond wall clearance |
| --- | --- | --- | --- |
| Full updates | 215 / 487 | 11 | 2 |
| Arbitrary full/partial updates | 845 / 2696 | 66 | 8 |

The second case grants arbitrary pauses instead of deriving them from the
elevator. Its stationary jumps can reach Y=132, but it cannot advance the
40 units needed to cross the wall. The first case can reach Y=77 while
stationary. This is the stated isolated flat-floor abstraction: its complete
refinement to linked Clight execution is unproved. It is not a whole-game
impossibility theorem.

## An approach that stays outside

The replay starts the stock singleton with Mario fixed inside the bottom
bucket at `(-410,128,700)`, static terrain and no other actors. At successive
random decisions it chooses:

```text
turn -45, timer 130
turn +45, timer 197
turn +45, timer 199
turn +45, timer 173
jump, turn -135
jump, turn -135
jump, turn -135
turn -45, timer 100
```

At update 847 it passes `(-3196.341552734375,0,2895.0380859375)` outside
the rim. The US/JP CSV replays agree. This is a reproducible native trajectory,
**not rim arrival**. Earlier elevator descent, the fixed Mario pose, other
actors and dynamic surfaces still need connection to a gameplay history.

```sh
bash instrumentation/western-goomba-rng/run.sh --replay-west
bash instrumentation/western-goomba-rng/run.sh --choices -3200 2925 10 west 1
```

The search keeps a 1024-state beam and removes quantized duplicates. Failure
is inconclusive. `south` instead of `west` selects the stock singleton
`(-2100,0,3316)`. Final argument `1` enables fixed-Mario distance activation;
`0` forces full updates. Activation uses the pre-movement distance and the
source's end-of-update timing.

Before the favorable-outcome clarification, a finite sweep of 65,536 initial
seeds for 10,000 updates each reached no rim, with or without activation, at
Mario `(-410,128,-154)`. That sample is not a coverage argument.

## Separate Coq result

[Area2WesternGoombaRng.v](../../proofs/Area2WesternGoombaRng.v) executes the
actual generated US/JP velocity tail. Starting after the sound call and
action assignment, with the regular scale and explicit valid storage, it
derives forward speed zero and vertical speed 25, and frames cells outside
those stores. It also checks the two entry-wall triangles from both generated
meshes. Main consumes these results. The native closure and search are not
Coq execution proofs.

A detour, a stock-to-stock meeting and useful push, or a changed support
remains open. No route to the rim, pit, elevator contact or defeat is proved.

## Watch the recorded path

[The path replay](../../docs/media/western-goomba-path-replay.mp4) reconstructs
the existing diagnostic's 901 recorded positions against the actual generated
Area-2 collision mesh. It is not emulator footage. It runs at 30 updates per
second, pauses for three seconds at update 847, then shows the rest of the
trace and holds its final frame for two seconds. The Goomba artwork and foot
motion are schematic; its feet position and jump height come from the CSV.
The clipped mesh hides upper floors and ceilings to make the path visible.
The two context markers are stock starting positions for the southern Goomba
and western Grindel, not additional actors participating in this replay.

`export_video_data.js` checks that the US/JP meshes and CSVs agree, restores
the CSV coordinates to Float32, checks all 901 consecutive update numbers
and the exact update-847 waypoint, and records the CSV's SHA-256. After
`check.sh`, run it from this project directory with Node. On the restricted
Windows runtime use `node --preserve-symlinks --preserve-symlinks-main`.
Then run `render_video.py` with a Python installation containing Pillow;
`--preview` generates five stills instead. The bundled desktop Python has
Pillow. All intermediate files stay under the ignored diagnostic build folder.

Encode the numbered frames with the installed WSL FFmpeg:

```sh
ffmpeg -nostdin -n -framerate 30 \
  -i build/instrumentation/western-goomba-rng/video/frames/%04d.png \
  -c:v libx264 -crf 18 -preset medium -pix_fmt yuv420p -movflags +faststart \
  build/instrumentation/western-goomba-rng/video/western-goomba-path-replay.mp4
```

The saved video is 1280 by 800, with 1,051 frames at 30 fps and duration
35.033333 seconds. Both existing native replay binaries were rerun and their
outputs matched the original CSVs byte for byte. The shared CSV SHA-256 is
`8cac5f724f89efa1ea725342853f6637547f54bf672a1b1092f6715450ad3763`.
Encoded frames were inspected. This is a presentation of the existing result;
it adds no gameplay reachability or impossibility theorem.

The [home-range guide](../../docs/media/western-goomba-home-range.png) and
[overlaid replay](../../docs/media/western-goomba-home-range.mp4) add the
1,000-unit home threshold and the direct bearing to the original rim target.
The helper measures distance in all three coordinates; the drawn circle is
its Y=0 cross-section, not a hard movement boundary. The target is 567 units
away horizontally and about 578 including Y, inside that threshold. The old
replay searched toward X=-3200, Z=2925 near the wall's southern end, not for
a shortest route to the rim. `export_video_data.js` checks the threshold's
actual generated US/JP call and the helper's three squared coordinate terms.
Run `render_video.py --home-range` to write these frames into the separate
`video/home-range/` output directory, then encode as above.

## All actors and the elevator clock

Run the new comparison with:

```sh
bash instrumentation/western-goomba-rng/check_elevator.sh
```

It checks the six singleton placements, triplet parent, two poles and elevator
from matching generated US/JP initializers, including the actual preset table.
The new native slices are `find_floor_height`, `bhv_pole_init` and the complete
`bhv_pyramid_elevator_loop`. The loop uses the source timer-reset convention;
it first detects Mario's platform pointer at frame 0. Its 901-row trace includes
both jolts and parking. The caller, live platform attachment and collision
loading are not a linked execution proof. The stock actor fixtures implement
the declared post-initialization fields: the real floor call at placement
Y+200 supplies the floor, home is set afterward, and `ON_GROUND` is set.
The older outside replay keeps its original initialization fixture unchanged.

Each singleton search grants favorable individual RNG outcomes, retains a
128-state beam for eight decisions, and stops each branch after at most 900
updates. It aims at the nearest point of the full base rectangle. Mario's X/Z
are fixed at the interior corner facing that actor, and his Y follows the
source elevator trace. The source's distance activation still applies;
partial updates may become full updates as the elevator descends. Pose and
carriage are conditions, and the world contains static terrain and one Goomba.
No other actor or dynamic collision surface is silently declared harmless.
No searched sample enters even the base rectangle expanded by 145 units.
That is finite search evidence, not an all-RNG impossibility theorem.

The separate western test aims at the original rim target, with four
decisions, a 256-state beam, and Mario fixed at `(-410,128,667)`. It produces
the [direct-rim replay](../../docs/media/western-goomba-direct-rim.mp4), whose
353 saved updates are displayed once each, with a 90-frame pause at update
271 and a 60-frame final hold. The result stops outside the entry wall.
Neither distance-based beam pruning nor the selected trace proves global
shortest-path optimality. The source geometry and prior wall closure explain
the direct obstruction without that claim.

The stock triplet parent is more than 3,000 horizontal units from every point
in the full bucket footprint. A fresh parent remaining there cannot load its
children while Mario is confined. Those three are inventoried but not treated
as existing actors in the new searches. Previously loaded children or a
changed parent position remain different conditions.

The [readable result](../../docs/notes/goomba-elevator-timing.md) includes all
nine height comparisons, the pit arrivals and the elevator timing. Reproduce
the presentation after both checks above with:

```sh
node instrumentation/western-goomba-rng/export_video_data.js
python instrumentation/western-goomba-rng/export_elevator_analysis.py
python instrumentation/western-goomba-rng/render_elevator_analysis.py
python instrumentation/western-goomba-rng/render_video.py --direct-rim --home-range
```

On the restricted Windows runtime use the Node flags documented above and
the bundled Python with Pillow. The exporter requires identical US/JP logs
and CSVs, restores Float32 coordinates and checks the scene height for every
recorded update. All intermediate files remain in the ignored
`build/instrumentation/western-goomba-rng/elevator-analysis/` directory.
Encode `video-direct/frames/%04d.png` there at 30 fps. The new replay is 503
frames, 16.766667 seconds, at 1280 by 800. No Coq result or capstone premise
changes in this diagnostic/presentation tranche.
