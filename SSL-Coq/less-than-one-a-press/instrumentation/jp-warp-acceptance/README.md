# JP upper-warp acceptance: all three position records

This read-only observer extends the existing clean mode-12 four-pillar
replay. It records the user's chosen checkpoint: successful nonfading
`interact_warp` return, still in Area 1, after selecting `ACT_DISAPPEARED`
with argument `0x00040002`, before that action executes.

The checked run has **no position disagreement and no captured top**.
Movement, collision and display are all
`(-2033.87939453125, 768, -1037.05859375)` at acceptance. Their binary32
words are `c4fe3c24:44400000:c481a1e0`. All seven observations have the same
three vectors. The floor is non-null (`80195db0`, height 768) with no Object
owner; the final platform is null. These are different facts.

The original top was identified by its stock behavior and pool slot 61 at
timer 348. At acceptance (timer 2807) there are zero active objects with
that top behavior. The original slot is inactive and contains behavior
`800e90d4`; it is not treated as the original actor merely because its
address survives. The inherited controller's position-based `gTop` hint
can identify a fragment, so this observer does not use that hint for its
top census.

## Reproduce

Use the project's original-JP emulator environment (Ubuntu-24.04 on the
checked machine), with an independently supplied authentic ROM:

```sh
bash instrumentation/jp-warp-acceptance/run.sh /path/to/baserom.jp.z64
python3 instrumentation/jp-warp-acceptance/test_check.py
```

The runner gates the ROM hash and instruction windows using the existing
Rank-5 and Rank-13 checks, compiles with warnings as errors, and keeps their
debugger observations and expected receipts. The only cheat enabled is the
existing level-select startup allowed by the project's entry boundary.
There are no post-entry game-memory writes in this input observer. The
route reports zero A presses, zero A-down frames and zero controller-A
frames. Its four pillar milestones are timers 848, 1065, 2390 and 2548.

The added checkpoints are handler entry, accepted nonfading branch,
successful handler return, disappearing-action entry and return, ordinary
copy return, and final Area-1 platform-query return. Their program counters
come from the existing authenticated Rank-13 and copy/platform audits.
The wrapper observes before forwarding each callback to the original audit.
The disappearing action changes the argument from `0x00040002` to
`0x00040001`, distinguishing acceptance from its later execution.

`check.py` checks the checkpoint, ordering, identities and clean provenance;
it reports a position split if present instead of filtering one out.
`test_check.py` verifies that shifted or incomplete checkpoints and broken
provenance fail, while a supplied test-only different display is reported.
The runner additionally compares the exact expected receipt. The compact
`expected-route.txt` preserves the relevant provenance lines, not a second
controller schedule. No ROM or conversation export is included.

The checked live output is under
`build/instrumentation/jp-warp-acceptance/run.hNkR0W/`. The initial comparison
stopped on the old observer's top fields; the saved expectation was then
updated to the inspected behavior-based census and all receipt checks passed.
The gameplay trajectory and older Rank-5/Rank-13 receipts were unchanged.

## What this settles

This closes this particular clean JP replay as an Ink candidate at the
selected checkpoint. It is not a universal controller-history exclusion,
a US runtime replay or a verified MIPS-to-Clight simulation. It does not
re-record the separate supplied vertical Ink fixture. The separate
[US/JP proof](../../proofs/InkWarpAcceptance.v) establishes that the real
final action-setting call and return cannot create or erase a split;
its frame begins after `mario_stop_riding_object`, not at handler entry.
