# Ground pound from a verified stationary-cog Pedro hold

Investigation on 2026-09-20, limited to `VERSION_US` and `VERSION_JP`, at source
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

**The tested continuation fails before impact.** A control preserves the
off-floor cog Pedro return for 30 successive updates. Pressing Z after four
matching updates holds Mario through ground-pound startup, but the first
descent loses the cog floor query, moves him out, and enters backward air
knockback. The following complete action update moves him farther out. Both
cogs stay still throughout. US and JP agree.

This is a finite emulator result, not a Coq impossibility theorem. The control
uses the ordinary **STOPPED clock setting** to isolate stationary geometry.
It does not supply a RANDOM-mode entry, a naturally occurring still interval,
or preserving RNG control. The ten additional RANDOM-mode timing trials below
also produce no preserving impact and successor. Other positions, cog angles,
and entries begun during an earlier ground-pound descent remain open.

## Setup and control

The existing user-authorized `inner_rim` initialization places Mario at
`(1313, -2088, -1098)`, yaw 90 degrees. A separate prepared copy selects the
game's STOPPED clock setting; both relevant cogs initialize at yaw/speed zero.
The only source changes are still the three declared initialization files.
Cog, collision, action, particle and RNG behavior functions are unchanged.
After initialization, recorded controller inputs provide all control and the
observer only reads state. Fresh emulator configuration reports cheats disabled.
The initialization patch hash is
`71f2c3bf6ec55e70e237f9815f72d1336b822e9c8f6da0fb65ff9b02e8d8c537`.

`inner-rim-recorded-inward-us.csv` reproduces the actual inputs of the prior
inward-steering experiment, without consulting the steering policy at runtime.
On the stopped clock, `check-preservation.py` accepts updates **0 through 29**:

- Mario stays at the same XYZ across complete action updates, internal
  observations, and bracketing input-poll snapshots; no platform reference is set.
- Actual geometry selects the floor at **-8191**, over 100 units below Mario.
- Each air query attempts a nonzero inward displacement and selects the lower
  cog floor at **-2088** and upper cog ceiling at **-1934**, a **154-unit gap**.
- The close-gap landing return rejects that displacement and retains the old
  far-below floor reference. Both cog poses remain fixed.

For example, update 0 intends and queries approximately
`(1313.24011, -2089, -1096.07971)` but returns to `(1313, -2088, -1098)`.
This is an actual positive diagnostic for the ordinary-air preservation
checker, unlike a stationary ground-pound startup snapshot. Normal level-entry
provenance and a corresponding RANDOM-mode history are separate missing facts.

## One Z press after four Pedro updates

The second replay changes only controller frame 4 to press Z. Its complete
normalized observations through frame 3 are identical to the control. The
32 ordered RNG calls before descent at frame 19 also agree between the two
continuations; that equality is a trace comparison, not a proof that all other
game state is identical after the controller inputs diverge.

| Relative update | Observed action and position | Result |
| --- | --- | --- |
| 0–3 | Four off-floor close-gap returns at `(1313, -2088, -1098)` | Same confirmed Pedro prefix as the control. |
| 4–18 | Fifteen ground-pound startup calls at the same position | Forward speed becomes zero. No air-step calls occur in startup. |
| 19 | First descent ends at approximately `(1270.37805, -2138, -1122.60815)` | Wall return; backward air knockback, forward speed -16, vertical speed -54. No ground-pound landing or mist request. |
| 20 | Following full action update ends at approximately `(1254.37805, -2192, -1122.60815)` | Still backward air knockback, vertical speed -58. Preservation has failed. |

Both relevant cog yaws and speeds are zero at every recorded action boundary
through update 20. A longer still interval therefore does not rescue this
particular direct ground pound: the failure occurs even with the cogs stopped.

The first descent's four quarter steps explain the loss:

| Quarter | Resulting position, approximately | Selected floor | Return |
| --- | --- | --- | --- |
| 1 | `(1313, -2100.5, -1098)` | -8191 | None (0) |
| 2 | `(1313, -2113, -1098)` | -8191 | None (0) |
| 3 | `(1270.37805, -2125.5, -1122.60815)` | -8191 | Wall (2) |
| 4 | `(1270.37805, -2138, -1122.60815)` | -8191 | None (0) |

Zero forward speed removes the inward displacement which selected the cog top
in the control. Mario descends instead. At the third quarter, wall resolution
changes X/Z. The aggregate air-step return retains the wall result even though
the fourth quarter returns zero. `act_ground_pound` therefore takes its wall
branch, requests vertical stars (`00000002`) and enters `ACT_BACKWARD_AIR_KB`
(`010208b0`). It does not take the landed branch or request mist circle
(`00010000`). No mist initializer is observed in updates 19–20. The two RNG
calls recorded in that window are retained in the receipt; they are not
evidence of in-spot mist control because Mario has already left the spot.

## Bounded RANDOM-mode timing search

The corrected ledge detour uses `ledge-rim-turn-133-us.csv`; the inner-rim
trials use the recorded inward inputs above. Each listed trial replaces one
controller frame with Z, and the observer verifies exactly that Z press.

| Setup | Z frame | Ground-pound calls | Impact | Why it is not a preserving witness |
| --- | ---: | --- | ---: | --- |
| Ledge | 128 | None | None | Does not enter ground pound. |
| Ledge | 130 | None | None | Does not enter ground pound. |
| Ledge | 132 | None | None | Does not enter ground pound. |
| Ledge | 134 | 134–149 | 149 | Mario moves before impact and has supporting cog geometry. |
| Ledge | 136 | 136–151 | None | Startup raises Mario; descent ends against a wall. |
| Ledge | 138 | 138–153 | 153 | Cog support/carry begins before impact; impact and successor do not preserve position. |
| Ledge | 140 | None | None | Does not enter ground pound. |
| Inner rim | 0 | 0–15 | 15 | Movement/support precede the mist-producing impact. |
| Inner rim | 1 | 1–53 | 53 | Falls to a lower platform before impact. |
| Inner rim | 2 | None | None | Does not enter ground pound. |

The four actual impacts request mist and execute its initializer, but fail
the position/support checks. The ledge Z138 case was independently replayed
in JP. Its full 6,117 normalized observations match US. This timing sweep is
finite, not an enumeration of every action history or geometric state.

## Evidence and checks

The tracked [receipt](../../instrumentation/ttc-cog-placement/results/ground-pound-successor.json)
contains input, trace, initialization, observer and build hashes; selected
surfaces; complete descent and successor boundaries; per-trial rejection
reasons; and cross-version comparisons. Raw logs remain in the ignored
`Pedro-Coq/build/cog-placement/` tree. No ROM or extracted asset is published.

| Pair checked in US and JP | All normalized observations agree |
| --- | ---: |
| RANDOM ledge, Z138 | 6,117 |
| STOPPED inner-rim control | 2,971 |
| STOPPED inner rim, Z4 | 2,954 |

All runs pass the existing consistency checker: balanced helper entries and
returns, matching selected triangles, complete observed input frames, and the
ordered RNG recurrence. Address normalization removes version-specific
addresses and compares object slots instead. Whole-trace RNG counts can
include ending-transition calls and are not automatically TTC-only counts.

The augmented observer's no-Z control reproduces the earlier detour through
frame 164 after projecting out the new helper observations and sequence
indices. That control has the legacy name `gp_successor_z138_us`, but contains
**no Z press** and is not counted in the ten timing trials. The actual Z138
trials are `gp2_z138_us` and `gp2_z138_jp`. The sweep now expands compressed
controller intervals before replacing a single frame and checks the observed
Z frames, avoiding the initial recipe-generation mistake.

A deliberately incomplete copy of an impact log, with the following action
update removed, is rejected for the missing complete successor. It is a
checker fixture, not game evidence. The ordinary-air checker now has a
positive STOPPED diagnostic; the ground-pound impact checker still has no
successful preserving example. Its observations cannot replace a Clight proof.

## Reproduction

From the proof repository, prepare and build the separate diagnostic:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-placement/prepare.py --setup inner_rim --clock-mode stopped
make -C Pedro-Coq/build/cog-placement/inner_rim_stopped/source VERSION=us COMPARE=0 -j2
make -C Pedro-Coq/build/cog-placement/inner_rim_stopped/source VERSION=jp COMPARE=0 -j2
```

Then use fresh trial names with `run.py` for each version. For the control,
pass `--setup inner_rim --clock-mode stopped --trace-ground-pound
--video-frames 470 --inputs
Pedro-Coq/instrumentation/ttc-cog-placement/inputs/inner-rim-recorded-inward-us.csv`.
For the Z4 continuation, use `inputs/inner-rim-ground-pound-z4.csv` in that
same instrumentation directory. Run `check-preservation.py TRIAL` on the
control and `report-ground-pound.py TRIAL` on the continuation; use
`check-trace.py US_TRIAL --compare JP_TRIAL` for the full comparison.

`sweep-ground-pound.py FRESH_NAME --suite ledge` runs the seven ledge timings;
`--suite inner` runs the three inner-rim timings. These use the existing RANDOM
placement builds, not the stopped diagnostic. Re-run a selected timing in JP
with `--version jp --z-frames FRAME`.

## What remains open

We have a verified hold and a checked failure of one ground-pound continuation
from it. We do **not** have one complete ground-pound impact followed by an
update preserving the spot. A positive result now needs different geometry
or an earlier-started descent, with its entire entry, impact and successor
checked. Only after that would accepted particles, camera effects and the
ordered draws supply evidence for preserving RNG control. This investigation
changes no Coq theorem and discharges no capstone execution premise.
