# Conditional JP vertical retry

The recorded test succeeds with both actual and raw collision position at
`(-2200,768,-1024)` and display at `(-2200,1938.8648681640625,-1024)`.
The game performs the first failed query, the successful retry, warp
interaction, platform capture, retention and Area-2 displacement.

This is a supplied-state mechanics test, **not a controller route to its
starting state**. It does not establish a negative-depth seed, a dialog
producer, either target star, or the outcome of every possible continuation.

## What is supplied

The wrapper reuses `jp-lifecycle`'s existing conditional fixture: retail
level select, the pillar-completion field set to four, a wait for top timer
131, the three Mario positions, and a cleared remembered platform. Before
the next game instruction it replaces the inherited raw warp-centre point
and midpoint display with the vertical-only coordinates above. The initial
action is the game's idle action; observed depth is zero. It does not set
the action, a floor, floor-list contents, a surface owner, or the Area-2
result. The alternative post-owner fixture in the included source is off.

After this boundary the probe only observes state and supplies ordinary
controller input. Area 1 uses neutral input. After Area-2 arrival it reuses
the existing 60-frame stick input `(-127,-96)`, then neutral input; there is
no A input. The ROM hash checks precede emulator loading. No ROM is included.

## What is observed

`expected-trace.txt` is the relevant text output from the original JP ROM
under Mupen64Plus 2.5.9, pure-interpreter mode, recorded 2026-09-11. The full
local run remains in `build/instrumentation/jp-vertical-retry/run.Ein2LC/`.
The first `TRACE_A1` line is the inherited fixture before the wrapper's
replacement; `VERTICAL_SETUP` is the completed supplied boundary.

The floor-return breakpoints record query arguments and selected pointers.
The first two returns also record the complete ordered lists for cell
`(5,7)`, with every link checked against the live allocated pools and a null
terminator required. Their four dynamic and 26 static surfaces agree across
the two queries. These are snapshots at returns, not an all-frame audit of
every surface-store instruction.

| Checkpoint | Result |
| --- | --- |
| First geometry query, timer 492 | Low coordinates unchanged by the wall calls; null floor |
| Retry in the same update | Exact high coordinates; floor `0x8019ba80`, owner `0x803451f8` |
| Final platform query | Same high coordinates and top owner; action is now disappeared |
| Polls 493–513 | All 21 retain the top; poll 513 finds it inactive and first in the free list |
| First actual Area-2 apply, timer 515 | Retired top remains the platform, still in the free list at depth 47 |
| That call's return | Actual position changes from `(0,5500,256)` to `(365.5927734375,5500,-1096.8026123046875)` |

The last movement is the useful sideways displacement past the elevator.
The later short stick continuation records one puzzle secret. It is not a
target-star collection. The true first apply is observed at entry and return,
rather than inferred from the later controller poll.

## Reproduce and check

Use the installed Ubuntu-24.04 emulator environment, from the active project:

```sh
bash instrumentation/jp-vertical-retry/run.sh /path/to/baserom.jp.z64
python3 instrumentation/jp-vertical-retry/check.py instrumentation/jp-vertical-retry/expected-trace.txt
python3 instrumentation/jp-vertical-retry/test_check.py
```

The accepted SHA-256 is
`9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317`;
MD5 is `85d61f5525af708c9f1e84dce6dc10e9`. Each replay creates a new output
directory and preserves previous outputs. The checker also verifies that
the committed Coq data block exactly matches the decoded ordered lists.

`InkVerticalLiveSelection.v` checks the finite snapshot using scalar cuts
extracted from the actual generated US/JP floor bodies, with CompCert
arithmetic and an expression-evaluation soundness theorem. It proves the
recorded meshes match the existing mesh certificates, the first accepted
surfaces at the two heights, and the real comparison choosing the higher
dynamic result. This is **not** a proof of the complete live list traversal
or an emulator-to-Clight simulation. The conditional JP runtime outcome and
the Coq snapshot certificate are separate evidence.
