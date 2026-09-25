# Wafel: a useful testing tool, not a new proof

Reviewed 25 September 2026. **Recommendation: try one replay-validation pilot
before using Wafel for searches.** This is a source/API review, not an
installation, benchmark or gameplay result. No route estimate, insufficient-case
classification or proof verdict changes.

## What it offers

[Wafel](https://github.com/branpk/wafel) combines an SM64 TAS application with
Rust code and Python bindings. It runs a compiled game library rather than
emulating the N64. Its README lists original US and JP support, Windows
distribution and a requirement for a vanilla ROM. EU and Shindou support are
experimental. The reviewed source revision is
`5b808b60af15d316a5e2b0f87db34421d6225b57`.

The [Python interface](https://github.com/branpk/wafel/blob/5b808b60af15d316a5e2b0f87db34421d6225b57/wafel_python/__init__.pyi)
has controller input, frame advance, named variable reads, saved states,
M64 input import/export, a frame event log, loaded surfaces and active-object
hitboxes. The [API guide](https://branpk.com/wafel/docs/dev/wafel_api/)
recommends `Game` for brute-force work. Its higher-level `Timeline` manages
rewinding for the application; that API is not exposed in the reviewed
Python stub. Rewinding a known history does not solve unknown predecessors.

## Where it could help this project

| Current question | Proposed use | What a result would mean |
| --- | --- | --- |
| F02: can a useful gap be created and retained? | Log movement, raw collision and stored display positions, action, depth, support and top timer; restore a reached state and vary controller inputs. | A replayable candidate or a failure within the tested inputs, not a universal exclusion. |
| Tweester transport | Search actual stick/button continuations with Mario, capture, hiding and other game updates present. | Could replace the supplied-Mario-position assumption in the existing isolated sweep, after replay synchronization is validated. It does not itself produce the gap. |
| F01: contact near the warp, walls or elevator | Inspect active hitboxes and terrain alongside the actors' identities and poses. | Helps explain why a candidate collides or misses. Hitbox overlap alone is not warp acceptance or installation. |
| F03 / 10A: support and elevator motion | Reuse a reached checkpoint to vary inputs and trace the selected floor and next position copies. | Targets one proposed exception to the existing conditional result; no new ground-pound closure follows from using the tool. |

The main expected benefit is less bespoke experiment code: Python can branch
from a saved game state and record named fields. Speed and synchronization
have not been measured here. A failed search stays a finite negative result.
A candidate still needs replay validation and the relevant proof connection.

## Details that matter for Ink

The [frame-log reader](https://github.com/branpk/wafel/blob/5b808b60af15d316a5e2b0f87db34421d6225b57/wafel_sm64/src/frame_log.rs)
does expose events within a frame. However, this review does not establish
that the distributed game's event schema records both floor calls, all three
position vectors, or the exact successful `interact_warp` return. Reading
only after `advance()` could miss a temporary split. Retain the existing
[accepted-warp observer](../../instrumentation/jp-warp-acceptance/README.md)
for that exact endpoint unless equivalent event coverage is demonstrated.

The Python `Surface` convenience object exposes normals and vertices, not
the full owner/type/list-selection evidence we need. `ObjectHitbox` exposes
position and dimensions, not persistent actor identity. Named reads may
provide the other fields, subject to checking the loaded layout. A terrain
picture or flat surface collection is not a live-floor selection proof.

The [Game implementation](https://github.com/branpk/wafel/blob/5b808b60af15d316a5e2b0f87db34421d6225b57/wafel_api/src/game.rs)
restricts its saved states to the same Game instance. Our emulator checkpoint
is not automatically a Wafel saved state. The compiled game library also
needs its own version, source and replay checks; it is not the project's
generated US/JP Clight program. The release history includes a desynchronization
fix, so agreement with retail execution must be tested rather than presumed.

The latest published release found was
[v0.8.5, 27 June 2022](https://github.com/branpk/wafel/releases/tag/v0.8.5).
The README advertises Python 3.7–3.9 prebuilt bindings, while the main source
has later changes. Confirm a compatible isolated Python/runtime/library
combination before adoption; no installation was attempted in this review.

## A bounded first trial

1. Select and record one Wafel/library version and reproduce the agreed normal
   JP startup and an existing controller replay. Keep the starting boundary
   and input-poll mapping explicit; do not manufacture the useful pose.
2. Compare actions, all nine position values, floor/support identity and key
   timer milestones against the existing JP observer. Check what the subframe
   log actually records. An unexplained divergence stops the pilot.
3. Once that baseline agrees, branch one short interval with controller inputs
   only, preserve its input sequence and replay any promising candidate in
   the existing emulator. Check the accepted-warp endpoint and later top
   capture separately. Use the appropriate no-new-A or A-never-pressed rule
   for the selected investigation.

Controller inputs and inspection are enough for this pilot. Changing depth,
actions, actor poses or RNG directly would not establish a gameplay route;
the previously agreed conditional grants remain separately labeled.
Completion means a checked replay adapter and one reproducible bounded
experiment, not an attempt to settle every family at once.
