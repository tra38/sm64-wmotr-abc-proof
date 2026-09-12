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
54 C functions unchanged, compares each slice with the revision pinned by
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
