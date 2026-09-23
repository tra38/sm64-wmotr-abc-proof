# Bounded TTC seed sweep

This is an **offline finite experiment**, not a Coq theorem or a complete N64
emulator. It executes captured, compiled US/JP game-thread code with Unicorn
2.1.4. It never connects to a running game and never writes a ROM or savestate.
The placement observer only reads receipts. Do not check its RAM images into
Git or publish them; they contain game data and instructions.

## Explicit family

The three starting states are entry to `level_script_execute` at relative
updates **0, 30 and 100** of the existing `search_edge_a` STOPPED placement,
independently recorded in US and JP. The anchor is `(1308, -2088, -1088)`, with
cog slots 29 and 32 at yaw, speed and target zero. The controller is the
existing `control-a-1200.csv`: stick `(75, 28)`, no buttons.

Every case starts with its own complete 8 MiB RAM copy and recorded function
entry registers. In that offline copy only, initialize the clock setting to
RANDOM and the seed to each integer in **0..65535**. Object timers, lists,
camera, Mario and other state are retained from that case, not copied from
another seed's future trajectory. These STOPPED-derived RANDOM states are
**hypothetical initial conditions**. No permitted gameplay transition to them
has been established. They are three times at one geometry, not three distinct
geometries or coverage of arbitrary preparations.

The maximum horizon is 1,200 complete updates. Seed enumeration uses early
rejection, not a fixed RNG call schedule or a probability assumption.

## Execution and acceptance

Each update runs the actual `level_script_execute`, including the object
command loop/list scheduler, Mario, camera and rendering. No C reimplementation
of individual object transitions is substituted. The only frame-boundary
model increments `gGlobalTimer`, advances the two framebuffer indices, toggles
the game profiler index and executes the actual `select_gfx_pool`. It retains
the fixed controller data and restores function-entry registers.

This model omits audio/OS/device threads, controller polling and display/vsync
execution. It assumes default floating-point control and no live HI/LO at the
function boundary. It accepts only an unchanged level-script continuation
pointer. These are explicit modeling limits, not discharged noninterference or
N64-to-Clight refinement obligations. Supported baseline comparisons do not
prove all possible continuations faithful.

The checked preservation predicate requires:

1. Mario's three position bit patterns remain equal to the anchor at every
   observed `execute_mario_action` return and complete frame return.
2. His retained floor pointer remains unchanged and `gMarioPlatform` stays null
   at the complete frame boundary.
3. Each relevant cog completes exactly one observed update; neither its update
   return nor the complete frame return changes its yaw.
4. The frame includes an actual close-gap air-quarter-step return, with the
   attempted Y at/below the selected floor, a positive gap no greater than 160,
   and floor/ceiling owned by slots 29/32 respectively.

This is an observation-boundary predicate, not a claim that every intermediate
machine instruction leaves all Mario fields unchanged. It is deliberately
narrower than every possible way of remaining in some Pedro geometry. A
nonzero *target* on the last update is allowed if it has not moved the cog.

`rejected` means a predicate violation was observed in this model. `survived`
means all requested updates completed with the predicate. Neither label proves
normal-entry reachability. `unknown` means unsupported execution, an unexpected
boundary or a resource cutoff; it must never be counted as rejection.

A translated-block budget of 5,000,000 units bounds each game-thread/helper
invocation (block size/4 + 1 per block visit). Budget exhaustion is unknown.
Executed block bytes are compared with the starting image. The driver also
has a two-hour supervisory limit per case; an interrupted case fails coverage
validation. No timeout is converted into an unsuccessful seed.

## Reproduction

Use the existing placement preparation/build workflow, pinned to
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, with the already declared near-cog
initialization. From the proof repository, in Ubuntu-24.04, capture each version:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-placement/run.py us seed_snapshot_us \
  --setup search_edge_a --clock-mode stopped \
  --inputs Pedro-Coq/instrumentation/ttc-cog-geometry/control-a-1200.csv \
  --trace-ground-pound --trace-cogs --snapshot-frames 0,1,2,30,31,100,101 \
  --video-frames 500 --timeout-seconds 360
```

Repeat with `jp seed_snapshot_jp`. Trial names must be unused. Capture is opt-in
and is never loaded back into the emulator. All replay inputs remain ordinary
controller inputs; cheats must be disabled.

Download the official binary wheel `unicorn==2.1.4` for
`manylinux2014_x86_64` with `pip download --no-deps --only-binary=:all:` into
`Pedro-Coq/build/cog-seed-sweep/packages`. Its SHA-256 must be:

```text
9d6e6dea140560de4ebd8446661f7ef84a357d428c14a3ef09dacd306ec8c239
```

Extract it with Python `zipfile` into `Pedro-Coq/build/cog-seed-sweep/python`.
Nothing is installed into the system Python. The native executable uses that
same wheel's headers and `libunicorn.so.2`; GCC and `mips-linux-gnu-nm` are needed.

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/prepare.py us
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/prepare.py jp
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/validate.py us
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/validate.py jp
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/run.py --jobs 6
```

`prepare.py` checks the source pin, ELF, controller input, observer receipt,
cheats/errors, snapshot shape and the observer's loaded routine hashes. It
records snapshot, config, library and executable hashes. `validate.py` checks
single and successive STOPPED frames against the independent emulator receipts,
including all ordered gameplay RNG draws, then checks positive preservation,
seed isolation, last-update target selection and explicit fuel exhaustion.

For additional RANDOM-branch calibration, record both versions using trial
names `seed_random_calibration_us/jp`, `--clock-mode random`,
`--snapshot-frames 0,1,2` and `--video-frames 400`. Then run:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-seed-sweep/calibrate_random.py
```

The first RANDOM frame matches the recorded RAM except profiler timestamps and
matches its 39 ordered RNG draws. The later two frames in each version reach
the unmapped MI interrupt-mask register during OS yielding; those reference
continuations are **unknown**, explicitly recorded. Eight hypothetical seed
samples per version also cross-check native hooks against the Python driver.

## Output and limits

Ignored build output contains one CSV/log/summary per version and starting
frame, plus `results.json`, `build.json`, `validation.json` and
`random-calibration.json`. Every CSV contains exactly one row per initial seed,
including complete-preserving-update counts, draw counts, final seed, rejection
reason and a 64-bit ordered-draw fingerprint. The fingerprint folds each seed
before a call and its object-pool index; it is a diagnostic checksum, not a
collision-free certificate. CSV files receive SHA-256 hashes in the summary.

The committed report contains only metadata, aggregate counts and selected
cases. Whole-memory calibration differences are retained by symbol, including
audio/OS/profiler differences; they are not silently hidden. This experiment
does not discharge a CompCert execution premise, establish a reachable RANDOM
setup, test variable controller policies, or exclude other cog geometries.

During development an optional Unicorn memory-write tracing hook caused an
emulation exception in an ordinary MIPS branch-delay path. Removing that hook
restored baseline agreement. The published evaluator uses full RAM reset per
seed and does not contain the faulty optimization.
