# Rank 11 Goomba installer mesh audit

This diagnostic checks whether any stock Area-2 regular Goomba can reach the second-pole ring through a deliberately permissive static-floor model. It reads the pinned decomp collision source; it does not modify a ROM, save state, or emulator.

Run the reviewed receipt check from the repository root:

```sh
node SSL-Coq/less-than-one-a-press/instrumentation/rank11-goomba-installer/analyze_mesh.js --check
```

Use `--compact` to print the reviewed pole fields, `--elevator` for the west-wall candidate, or omit both for the full component/frontier report. An optional final positional argument selects another `collision.inc.c` file; its vertices and triangles must agree with both generated US/JP arrays. `--check` also checks the elevator component paths and the western support samples.

The graph includes every upward face that `surface_load.c` classifies as a floor (`normalY > 0.01`). It grants the listed short walking transfers, the `66 + 78 = 144` jump/query rise, and a separate `216`-unit pair transfer. It expands the triplet spawner into its three pinned-table children. It has no proved coverage of all ordinary movement: a normal landing can resume walking during a rebound, and the grounded edge restriction then need not apply. Long flights, repeated pushes, walls, dynamic surfaces, action timing and live floor selection require separate checks. The elevator report is a component graph and finite ideal-plane support sample, not a controller route.
