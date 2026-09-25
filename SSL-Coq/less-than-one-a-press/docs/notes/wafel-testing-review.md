# Wafel: the first bounded replay pilot passed

Updated 25 September 2026. We installed an isolated **Wafel 0.8.5 / Python
3.9.13** runtime, reproduced the existing JP replay, branched three seconds
of controller inputs, and checked a changed branch in the original emulator.
This is a finite runtime result, not a new Coq proof or a no-Ink theorem.
All atlas estimates stay unchanged.

## What worked

The known four-pillar replay passes its original exact warp-acceptance
checks. Wafel matches 2,483 Area-1 snapshots of the three position vectors,
action/action timer, input flags, floor height/nullness/owner, platform and
Mario slots, and original top-slot fields. There are 2,852 input polls and
no A-down frames. Wafel's global timer is consistently one ahead at the
paired observation boundary; the checker requires that mapping explicitly.
This does not establish raw timer equality or every timer-dependent history.

At one reached late approach, we save the state and try five 90-update input
choices: unchanged, briefly neutral, holding Z, reversed stick X, and a
single B press. Across all 450 after-update samples, movement, collision
and display match and the stored floor is non-null. Some input choices
produce the same trajectory. This is not an exhaustive input search or
evidence about every intermediate lookup.

The neutral choice changes Mario's movement. Replaying its full input
sequence in the original emulator matches 2,442 Area-1 snapshots under the
same timer mapping. All 90 restored-state outputs match too. No useful gap
was found. The interval begins with the original top slot at timer 150,
so it is not a fresh search for the earlier timer-131 installation. The
existing baseline still reaches the accepted warp with all three records
equal and no live top; the short branch stops before acceptance.

The [pilot instructions and compact receipt](../../instrumentation/wafel-jp-pilot/README.md)
give the versions, hashes, fields, exact inputs recipe, checked local output
paths and reproduction commands. The comparison rejects a changed position
bit and a shifted timer. ROMs, libraries and full captures are not published.

## Where it helps next

| Family | Useful test | Limit |
| --- | --- | --- |
| F02 position order | Restore a reached checkpoint and vary controller inputs while observing all three position records. | A failed finite batch is not an all-history exclusion. |
| F08 collision/contact | Inspect actual hitboxes, actors and terrain beside a replay. | Overlap alone is not warp acceptance or installation. |
| F01 support / 10A | Follow the selected floor and next copies during controller variations. | A flat list of surfaces is not proof of live selection order. |
| Tweester transport | Test stick inputs with Mario, capture and hiding actually running. | This pilot did not solve rapid home oscillation or produce a Tweester gap. |

Wafel runs a compiled game library rather than the N64 or our generated
Clight semantics. The tested release is pinned; the earlier API review
used main revision `5b808b60af15d316a5e2b0f87db34421d6225b57`. Those are not
the same source state. In particular, the release lacks main's `set_input`
helper, so the adapter uses only the three controller-pad writes during
gameplay. The accepted level-select startup is the sole pre-entry setup
write. Saved states come from the reproduced controller prefix, not an
injected gameplay pose or emulator-state conversion.

The observed event logs include action changes, speed, movement steps and
wall pushes. They do not provide the collision/display vectors or the exact
successful warp return in these runs. Keep the existing accepted-warp
debugger observer for those checks. Reading only after an update may miss
a temporary useful split. The convenience surface and hitbox records also
do not establish every owner, list selection or actor lifetime.

US, other library versions and other gameplay histories remain untested.
No robust performance benchmark or universal synchronization claim is made.
The completed deliverable is a checked adapter and one reproducible bounded
experiment; a future candidate still needs the exact installation checks.

Tool sources: [Wafel repository](https://github.com/branpk/wafel),
[tested release 0.8.5](https://github.com/branpk/wafel/releases/tag/v0.8.5),
[reviewed main Python interface](https://github.com/branpk/wafel/blob/5b808b60af15d316a5e2b0f87db34421d6225b57/wafel_python/__init__.pyi),
[frame-log reader](https://github.com/branpk/wafel/blob/5b808b60af15d316a5e2b0f87db34421d6225b57/wafel_sm64/src/frame_log.rs).
