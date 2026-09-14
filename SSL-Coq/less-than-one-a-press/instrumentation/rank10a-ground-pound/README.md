# Rank 10A offline startup check

Run from the active SSL project:

```sh
node instrumentation/rank10a-ground-pound/check.js
```

This reads the pinned decompile and computes conditional Float32 gameplay
samples. It does not start an emulator, edit game state or produce a clean
controller route. The ordinary fifteen-update startup reaches relative Y=260;
its unimpeded first falling quarters are 257.5, 245, 232.5, 220. All 1,024
headroom masks stay below that envelope. Two asset descriptors and 128,004
floor-following samples are checked as additional controls.

The [notes](../../docs/notes/rank10a-ground-pound-moving-geometry.md) explain
the missing clean entry and useful departure. The companion
[Coq proof](../../proofs/Area2Rank10AGroundPound.v) checks the selected source
and Y-store and gives a general binary32 startup bound; this finite offline
checker is not a replacement for a live execution projection.

`node instrumentation/rank10a-ground-pound/check_entries.js` checks the
nominal 504-sample elevator cycle in both generated versions, including the
start/stop jolts, integer-base and one-unit-margin controls, and all six
hangable static triangles against the full outer bucket footprint. It also
checks that the four stock moving meshes contain no hangable triangles.
The [entry note](../../docs/notes/rank10a-elevator-entry-checks.md) states the
remaining timing, selected-base and ceiling-history obligations.

`node instrumentation/rank10a-ground-pound/check_blocked_steps.js` checks
all static ceiling candidates over the interior and the elevator underside.
It also checks the underside rejection at every integer base height from
128 through 4966. The [blocked-step note](../../docs/notes/rank10a-blocked-steps.md)
separates these finite checks from the actual Coq branch executions and the
remaining live-query and frame-preservation obligations. No stalled Mario
run or ground-pound entry is produced by this checker.
