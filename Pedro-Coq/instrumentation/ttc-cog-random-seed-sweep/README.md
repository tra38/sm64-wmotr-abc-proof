# Seed sweep from an observed RANDOM phase

This corrects the earlier STOPPED-derived family. The starting clock mode,
cog angles, angular speeds, targets, object timers and Mario state are captured
after RANDOM has already run for 836 updates. The offline constructor changes
**only the seed**. It never writes to a running game, ROM or savestate.

This first family tests **cog stillness with Mario on the ledge**, not Pedro
preservation. Geometry sampling is separate. Moving Mario into a sampled point
changes object activation and needs a new full-state experiment. Even here,
only the original seed is observed with this non-seed state; arbitrary seed
substitutions do not establish reachable combinations.

## Capture and family selection

Use the existing `ttc-cog-placement` preparation/build workflow for the declared
`ledge` setup in RANDOM mode, pinned to
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. This uses the previously authorized
near-cog initialization `(1742,-2088,-125)` and ordinary neutral controller
input. It is not a normal-entry replay. In Ubuntu-24.04, from the proof repo:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-placement/run.py us random_phase_survey_us \
  --setup ledge --clock-mode random --video-frames 12000 --timeout-seconds 900
python3 Pedro-Coq/instrumentation/ttc-cog-placement/run.py us random_phase_snapshot_us \
  --setup ledge --clock-mode random --snapshot-frames 836,837,838 \
  --trace-cogs --video-frames 1220 --timeout-seconds 360
python3 Pedro-Coq/instrumentation/ttc-cog-placement/run.py jp random_phase_snapshot_jp \
  --setup ledge --clock-mode random --snapshot-frames 836,837,838 \
  --trace-cogs --video-frames 1220 --timeout-seconds 360
```

Trial directories must be unused. Captured RAM stays in ignored build output.
Do not publish it or ROM data. The observer is read-only, verifies loaded
instructions, and requires cheats disabled.

The 11,625 observed input boundaries contain one incoming frame where both
cogs 29/32 have target zero and absolute speed at most 50: frame 836. The
next speed-approach step makes both speeds zero. The upper cog still has
speed 50 in the entry snapshot; neither yaw moves during that next update.
This selection tests a one-update pause opportunity, not a sustained hold.
`report.py` recomputes selection, confirms all observations remain RANDOM
without time stop, checks the capture against the survey, and compares the
845-frame logical US/JP capture prefixes (ignoring recorded pointer addresses).

## Offline execution

Use the same authenticated Unicorn 2.1.4 dependency as the
[earlier evaluator](../ttc-cog-seed-sweep/README.md). The shared C engine executes
the compiled game-thread and per-seed object continuations. This variant
requires the captured clock setting already equal RANDOM and never changes it.
It checks exactly one update of each relevant cog and unchanged yaw at the
cog return and complete frame boundary. It omits the previous Mario/close-gap
predicate, because this is explicitly a scheduling test on the ledge.

Each candidate receives a fresh complete RAM copy and entry registers. The
fixed controller is neutral. Frame-boundary operations, CPU assumptions,
instruction budgets and `unknown` handling remain as documented for the shared
engine. Unsupported execution must never be treated as a rejected seed.

The new phase loads a Mario animation during its first update. The old engine
stopped as unknown at the MI interrupt-mask register while an OS thread yielded.
An opt-in **animation DMA external adapter** now implements the ROM-to-animation
buffer copy specified by pinned `memory.c:dma_read`: length rounded to 16 bytes,
read from the authenticated ROM into Mario's allocated 16 KiB animation buffer.
The adapter checks the caller, destination, ROM animation segment, size and
RAM bounds. All table selection, `currentAddr` changes and animation/gameplay
code still execute normally. Any other DMA request is unknown.

This is an external execution contract, not a proved faithful OS/device model.
It omits cache, message-queue and thread-scheduling side effects. Audio and
display/device work between frames remains omitted. Full RAM differences,
including OS/audio/profiler state, are retained in calibration reports. No
noninterference theorem or N64-to-Clight refinement is claimed.

## Run and verify

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-random-seed-sweep/run.py validate
python3 Pedro-Coq/instrumentation/ttc-cog-random-seed-sweep/run.py sweep
python3 Pedro-Coq/instrumentation/ttc-cog-random-seed-sweep/geometry.py
python3 Pedro-Coq/instrumentation/ttc-cog-random-seed-sweep/report.py
```

Validation compares one, two and three successive original-seed updates with
the independent emulator capture in each version: complete object pool,
Mario, camera, controller and graphics structures; animation buffer; ordered
RNG draws and final seed. It checks the original seed's first still update,
explicit resource exhaustion as unknown, and batch/isolated seed agreement.
The sweep covers 0..65535 exactly once per version, at a 1,200-update horizon,
and independently replays all longest cases. Output files use exclusive
creation so a completed sweep is not silently overwritten.

`geometry.py` authenticates the pinned collision source and reuses the earlier
host geometry filter at all eight recorded cog angles. For the lower cog's
top perimeter it samples 33 fractions per edge, 11 offsets and up to five
inward quarter-step strides. It checks the close-gap return and immediate
geometry refresh. It does not run a complete action or place Mario in the game;
sampling is not exhaustive geometry coverage.

The metadata-only committed receipt is
`docs/notes/ttc-cog-random-seed-sweep-results.json`. Results and limitations are
explained in the adjacent Markdown note. The previous sweep's historical
receipt remains unchanged and clearly labeled STOPPED-derived.
