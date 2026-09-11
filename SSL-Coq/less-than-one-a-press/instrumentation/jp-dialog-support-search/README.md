# Three-second search after a conditional dialog release

This experiment asks whether moving support, or an ordinary action immediately
after it, can bring Mario toward `(-2200,768,-1024)` while a raised display
survives. It runs the authenticated original JP ROM. Each trial follows **90
game updates after dialog release**, nominally three seconds. The earlier
dialog wait is preparation and can last much longer than three seconds.

The first checked moving-top trial supplies a useful distinction: platform
movement really can change actual Mario while the raised display stays in
place. Its first floor query nevertheless succeeds, and the following action
refreshes the display in the same update. Moving support is therefore a real
local mechanism, but this trial does not produce the failed-query installer.

## Recorded result

All 68 trials completed and passed receipt validation: **6,120 continuation
updates, no A input, and no pre-action failed floor query**. All refreshed the
display on the first update after dialog release. In 56 trials, platform
displacement changed actual position before that refresh while the raised
display remained unchanged.

| Starting support | Trials | Movement before display refresh | First-query misses |
| --- | ---: | ---: | ---: |
| Static warp centre or roof | 8 | 0 | 0 |
| Pyramid top, four selected phases | 48 | 44 | 0 |
| Three sampled Tox Box faces | 12 | 12 | 0 |

No installation candidate was recorded. This rules out the listed
continuations from their supplied checkpoints, not other poses or histories.
The game genuinely produced and briefly transported the raised display in
these tests; the missing step is making that transport also lose the first
floor result near a usable warp contact. The full run is preserved locally
at `build/instrumentation/jp-dialog-support-search/search.7w1bsiyl/`; the
committed archive rechecks every trial without requiring the emulator.

## Diagnostic starting assumptions

These are conditional mechanics tests, not controller routes from level entry.
In addition to the accepted level-select bootstrap and a negative depth seed,
the experiment explicitly supplies a candidate position and an automatic-dialog
checkpoint. **That checkpoint is an extra diagnostic assumption**, beyond the
agreed valid coin/star-opportunity allowance. No star collection or gameplay
reachability is claimed for it. A positive result would still require recovering
that history; a negative result excludes only the tested continuation.

The existing pillar-completion fixture starts the top. At the selected spinning
phase, the new fixture sets actual, raw and displayed positions equal, clears
velocity and remembered platforms, and supplies depth `-0.5`, automatic-dialog
state 1, previous action `ACT_STAR_DANCE_NO_EXIT`, and dialog 144 (the actual
30-star milestone message). It supplies **no height gap, floor pointer, surface
owner, floor list, warp outcome or later position change**. Moving-support
positions are proposed from live floor planes, then checked against the actual
game's first query. Tox cases first place Mario near the selected box so its
normal terrain pass loads its collision mesh. Both placements precede the
declared diagnostic boundary.

After that boundary, the plugin supplies only controller input and observes
the game. The real dialog enables time stop; real sinking calls raise the
display; periodic B inputs dismiss the message. The checker verifies the rise
against the number of actual sinking calls. It then checks all 90 updates,
their inputs, floor returns, early movement and the first display refresh.
No A press or held A is allowed. Each trial starts a fresh emulator process.

## Finite search space

`search.py:cases` defines exactly 68 trials. The nine starts are the static
warp centre, the static roof at `(-2200,1280,-1024)`, the top at spinning phases
41, 60, 100 and 130, and one sampled live face of each of the three Tox Boxes at
phase 41. Phase means the last executed top behavior timer when the dialog
fixture begins; the stored object timer has already advanced by one.

For the phase-130 top, all 36 policies combine neutral/eight compass stick
directions with four button choices: neither button, held Z, B every eight
updates, or both. For each other start, the four tested policies are neutral,
left stick, left stick with Z, and left stick with Z plus periodic B. Stick
directions are controller axes, not asserted world-space directions. Each
policy stays fixed for the full 90-update continuation.

This is forward testing of candidate predecessors chosen by working backward
from the successful boundary. It is not symbolic inversion of the game and
not enumeration of all controller histories, support positions, object phases,
dialog timings, seeds, or floor-alignment histories. The supplied checkpoint
also leaves earlier star/contact reachability entirely open.

## Observation points and existing proofs

The two original query-return sites are `0x802538a0` and `0x802538e4` in
`update_mario_geometry_inputs`. Both preceding JAL instructions are checked
against the call to `find_floor` at `0x80381900`. Queries are observed after
the two wall corrections. The returned floor pointer and owner come from the
game. The legacy `height` column is the **previous cached floor height before
the caller assigns the new result**, not the callee's returned height.

Platform displacement is observed at its real dispatcher entry and return.
A read-only write watchpoint on Mario's display X identifies the first store
of `vec3f_copy` at `0x8037880c`, with destination equal to Mario's display and
source equal to MarioState position. The instruction word and live arguments
are checked. This identifies ordinary position-to-display copies; it is not
claimed as a census of all conceivable display writers. The dialog handler
at `0x80257838` and sink helper at `0x80254164` establish the release and rise.
The matching JP symbol map and disassembly supply these addresses; the runner
authenticates the entire original ROM before loading it.

The interpretation reuses `InkPlatformDeparture.v` for the actual US/JP null
dispatcher, `InkRetryCallCompletion.v` for query position preservation,
`InkRetryQuery.v` for the actual retry call, and `InkPostDialogGroundReset.v`
and `InkWarpStop.v` for ordinary resets. Those modules refer to generated
Clight. This new experiment does not replace them with a handwritten game
model and does not claim a full Clight execution or MIPS-to-Clight simulation.

## Reproduce

From the active project in the installed Ubuntu-24.04 emulator environment:

```sh
bash instrumentation/jp-dialog-support-search/run.sh /path/to/baserom.jp.z64 2 130 0
python3 instrumentation/jp-dialog-support-search/search.py /path/to/baserom.jp.z64
python3 instrumentation/jp-dialog-support-search/test_check.py
python3 instrumentation/jp-dialog-support-search/archive.py
```

The accepted ROM SHA-256 is
`9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317`;
MD5 is `85d61f5525af708c9f1e84dce6dc10e9`. No ROM is included. The runner uses
the same established level-select bootstrap as the previous JP experiments.
Every run creates a new output directory and preserves earlier build output.
The compressed receipt archive contains only this experiment's text observations,
not a ROM, emulator state or conversation export. Its checker revalidates every
trial and demands exact coverage of the declared finite case list.
It also checks the experiment source hashes with line endings normalized to
LF. The 12 mutation tests reject changes to initial gaps, selected owners,
dialog completion, update coverage, inputs, sink counts and early movement.
