# Rank 1: why the 146 earlier proposals missed, and what happens afterward

3 October 2026. **All 146 saved earlier proposals were reproduced, then allowed
to finish their actual continuous suffix. None produced the checked Ink payoff.**
Dot was right that an unequal parent checkpoint is a narrower failure than
failure to reach Ink. However, the suggested raw-controller explanation does
not account for these attempts: none mismatches the recorded pad or button
fields, and all 146 differ in at least one Y position record.

This is a finite diagnostic of the existing stopped pilot. It supplies the
same earliest conditional poses and does not discover a gameplay gap producer,
add a Coq result, change a route estimate or exclude an entire move family.
Rank 1 remains at the subjective 1–2%.

## What actually differs at the parent

The source ledger's default full-history audit verifies 293 records, including
the final incomplete budget attempt. We select only its 146 completed,
rejected earlier proposals: 72 ground, 51 freefall and 23 final-message moves.
Every saved first-checkpoint mismatch dictionary is reproduced exactly in
the native replay. The original ledger HEAD stays unchanged.

| Parent field | Attempts with a mismatch |
| --- | ---: |
| Cached floor height | 146 |
| RNG | 146 |
| Collision position | 136 |
| Display position | 124 |
| Action | 124 |
| Movement position | 96 |
| MarioState input flags | 90 |
| Floor owner | 69 |
| Missing-floor flag | 65 |
| Platform | 54 |
| Quicksand depth | 44 |
| Vertical speed | 24 |
| OS pad, held buttons or pressed buttons | 0 |

These counts overlap. They are observations, not independent causes or
probabilities. The full receipt also records action argument (123), used-object
slot (123) and action state (1). All 146 have a Y mismatch in movement, collision
or display; removing only RNG or cached-floor equality would not make any of
them reproduce its supplied parent.

The supplied parent cache says floor height **38** in every attempt. The next
actual update instead records the earlier top at **1899.650390625** in 69 cases,
the missing-floor sentinel **−11000** in 65, and the static floor at **1280** in
12. The cached 38 is inherited context, not the actual floor height required
by the target. Expected/actual RNG is **56027/50242** in every attempt.
Those two universal differences explain universal exact-checkpoint failures,
but neither by itself proves the installation impossible.

Of the 124 action mismatches, 123 are `ACT_DISAPPEARED` and one remains in the
automatic message action. In other words, many proposals trigger the upper
warp a frame earlier than the intended supplied idle parent. Requiring idle
at that checkpoint rejects that different timing.

## The controller suspicion does not explain these 146

The saved `pad` observer reads the OS pad buffer. It does not read
`gControllers[0].rawStickX/Y`. A zero OS-buffer observation therefore is not
evidence that the requested stick failed to reach Mario's controller.

The new diagnostic checks actual native raw stick X/Y and held buttons after
every advance. All **3,650** readbacks match the requested controls. The saved
pad, held-button and pressed-button comparisons have **zero** mismatches.
Every replay keeps A released and checks that no new A edge occurs. We do not
delete those checks or infer that controller history is irrelevant.

## Let the different parent continue

Each diagnostic restores the same earlier full-state context and applies
**one earliest pose patch**. It advances the recorded two-input suffix and
then the same 23 neutral retention updates. It never patches or restores at
the unequal parent. The actual result, including its RNG, floor cache,
controller history and action, continues into the next update.

| Checked outcome | Attempts |
| --- | ---: |
| Completed continuous 25-update replays | 146 |
| Entered the disappeared warp state on update 1 | 123 |
| Observed that action execute on update 1 | 59 |
| Captured the top at the early warp transition | 47 |
| Kept that top pointer at all following Area-1 observations | 47 |
| Entered Area 2 | 59 |
| Matched the selected last-update target and payoff | 0 |
| Produced the checked known Ink displacement | 0 |

The other 64 early warp-state changes do not have a first-update action-entry
event. Setting the action and observing it execute are separate checks;
pre-action geometry can return before the action loop. The diagnostic accepts
both end arguments `0x40002` and `0x40001` when identifying entry into the warp
state, because executing the action can decrement its argument.

All 59 first Area-2 action entries and end positions are the ordinary spawn
**(0, 5500, 200)**. None matches the known displaced point
**(365.5927734375, 5500, −1096.8026123046875)**. Ten earliest proposals start with
all three position records synchronized and depth zero; none produces that
payoff either.

**The retained pointer did not vanish in Area 1.** All 47 captured cases still
have platform slot 61 at their last Area-1 observation. The top remains active
(`257`), with action `2` and timer `0`: it has just entered its explosion
action. These proposals enter the warp one update before the supplied
successful timer-131 setup. In the stock top code, the spinning phase switches
to explosion at timer 150; explosion clears its active flag on the next
behavior invocation. That timing difference is visible here.

This does not identify every effect between the last Area-1 observation and
the first Area-2 action. In particular, we do not claim to have proved or
observed the exact unload/reuse/residual-payload mechanism inside those calls.
The checked result is an active retained top just before departure followed
by an ordinary first Area-2 spawn. Another timing or later input suffix needs
its own test. A fixed 25-update continuation failing is not a permanent
impossibility statement about its initial pose.

## Which parent fields need equality?

All actual fields still influence execution. The question is whether they
must equal one particular archived parent, which is stronger than whether
their actual state can continue into a useful installation.

| Fields | What the diagnostic keeps, and what equality means |
| --- | --- |
| Movement, collision and display | Keep all three actual records. Inspect the useful query/contact relationship and final payoff. Exact equality to a saved parent rejects other usable positions as well. |
| Action, timer, argument and vertical speed | Keep actual values and execute their real branch. They can change warp timing and which copies run; they cannot be silently substituted from the archive. |
| Cached floor, owner and platform | Keep actual values. A completed query may refresh them, while an early return may preserve them. An arbitrary fixed cache value is not a general Ink requirement. |
| RNG and surrounding objects | Keep actual resulting RNG and world state throughout the suffix. They may affect callbacks and top lifetime. A different RNG need not invalidate a goal replay, but it prevents claiming exact parent reproduction. |
| Raw stick, held/pressed buttons and A history | Check native readback and enforce the allowed A history. Button edges matter. OS pad-buffer equality is not the same observation as Controller raw stick equality. |

The strict search and its retained archive are unchanged. The new diagnostic
is a separate mode: it can assess a goal from an unequal parent without
calling that parent equal or joining two different states. A future search
that retains such a successful continuation must archive its **actual**
context, full input suffix and provenance, then validate every extension
continuously from its earliest patch. It cannot merge states just because
their displayed positions agree.

Raw/display preservation at the within-update accepted return remains the
existing explicit, unproved per-input prefix contract. The Wafel action event
directly observes movement there; the start records are not independent
accepted-return reads. Native top retention and first Area-2 positions are
checked separately. Nothing in this diagnostic weakens that reporting boundary.

## What the existing Coq proofs can say

[`InkRawCopyHeight.v`](../../proofs/InkRawCopyHeight.v) identifies the exact
checkpoint immediately after the collision-height store inside a completed
real Object-copy call (`irc_completed_copy_has_exact_height_cut`). Movement
and collision Y agree at that cut, while display Y is unchanged. Five of the
six retained supplied recipes disagree between movement and collision and
therefore cannot describe that cut under its conditions. Excluding them at
the later parent boundary also requires preservation through the remaining
copy and intervening calls. The sixth has both at 768 and a raised display,
so it needs a separate argument.

[`InkPostDialogGroundReset.v`](../../proofs/InkPostDialogGroundReset.v) proves
that its completed ground refresh followed by finite nonnegative sinking
cannot retain the old upward gap
(`ipg_reset_then_sink_cannot_retain_an_upward_gap`). Its nonnegative-depth and
call-framing conditions matter; some earlier proposal recipes grant negative
depth. Neither local result is a complete-update classification of all these
conditional states, much less every controller history. No proof source was
changed and no complete-update obstruction is promoted here.

## Runtime, limits and saved evidence

The runtime is Windows AMD64 Python **3.9.13**, Wafel **0.8.5**, and the pinned JP
DLL with SHA-256
`960fe979068b78e6733b3ddb87741833fbf4eb29b2a21a2bba871977427c2d0f`.
The source ledger and context recipes are pinned to the stopped pilot at
`634f52bddca909b9f743166afe33cc8011cf8f84`. The receipt includes the source,
runtime, capture and reviewed-proof hashes.

The declared native search ceiling is **5,000** updates; all 146 saved suffixes
finish in **3,650**, plus **495** preparation advances recorded separately.
Setup, verification and search each allow 30 seconds, with a cooperative
90-second overall limit and a hard 100-second child-process ceiling. Search
time checks occur between complete 25-update diagnostic replays; the native
update ceiling checks before each advance. No new inverse proposals were
sampled.

| Phase | Seconds |
| --- | ---: |
| Preparation | 1.7874914 |
| Full source-ledger verification | 0.3115592 |
| Actual continuous replay | 0.6673785 |
| Checkpoint | 0 |
| Measured in-process finalization | 0.0017230 |
| In-process total | 2.7681521 |
| Startup, receipt writing and exit overhead | 0.3955024 |
| External process total | **3.1636545** |

The external clock includes startup, report writing and process exit. These
fixed saved continuations do not price new sampling or longer backward trees.

**85 code tests pass**: 70 application tests and 15 original freefall-pilot
tests. Seven new diagnostic controls cover overlapping histograms, a scripted
unequal-parent goal success, exact saved-mismatch reproduction, one earliest
patch with continuous replay, decremented warp arguments, input/A rejection,
native budget interruption and verification exhaustion before game creation.
The scripted success is an application control, not a gameplay witness.

From the SSL project directory:

```powershell
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/concrete-ink-backward -p 'test_*.py'
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/wafel-jp-pilot -p 'test_backward_validation.py'
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/benchmark_parent_diagnostics.py --ledger build/concrete-ink-backward/20261003-rss-final-report/scattershot.ledger --output build/concrete-ink-backward/NEW-parent-diagnostic
```

Use a new output directory. The completed local run is
`build/concrete-ink-backward/20261003-rss-parent-delivery/`: `report.json`
records every update, `attempt.json` records the external clock and source-HEAD
check, and `stdout.log`/`stderr.log` preserve process output. Build output is
left in place and is not committed.

The compact committed
[`expected-parent-diagnostics.json`](../../instrumentation/concrete-ink-backward/expected-parent-diagnostics.json)
contains all 146 mismatch dictionaries, proposal/input-suffix records, shared
pose/checkpoint references, observed outcomes and the final Area-1 evidence.
It contains no ROM, DLL, full native snapshots or conversation export.
