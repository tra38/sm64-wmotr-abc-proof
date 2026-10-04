# Rank 1: scalable checkpoints, honest resume costs

Follow-up: [compact storage and the stopped Reverse Scattershot pilot](rank1-reverse-scattershot-pilot.md) separates setup/verification/search budgets and measures the new compressed format. The measurements and raw-chunk format below are the preserved earlier benchmark, not the current format's footprint or clock policy.

3 October 2026. This repairs the concrete counter's bookkeeping; it adds no
Coq result or gameplay gap producer. The original 5,000-case ledger remains
unchanged. A fresh, bounded benchmark stops at 80,000 supplied-scene trials:
28,000 selected-field matches, 28,000 end-field nonmatches and 24,000
entry-height nonmatches. Those last nonmatches are not failed warps. No full
input product or earlier multi-update chain has been completed. Rank 1's
subjective estimate remains 1–2%.

## What changed

Previously, every thousand cases flushed and reread the entire JSONL ledger
to hash it. Checkpoint reads therefore grew roughly quadratically, and resume
hashing/scanning happened before the reported trial clock. The replacement
hashes bytes as they are appended. Each chunk has at most 1,000 records and
4 MiB of trial data; a record is limited to 64 KiB, metadata to 256 KiB.
Counters, checksums and the twelve diagnostic samples have fixed bounds.
There is no growing in-memory list of trials, accepted candidates or chunks.
Chunks are bucketed into directories of at most 1,000 ordinary chunk names.

Each transaction stores `trials.jsonl`, `retained.jsonl` and checked commit
metadata. The retained file is exactly the accepted trial subsequence. Its
records identify the input and patched predecessor recipe in the pinned
manifest, not a portable Wafel memory dump. Reconstructing that state still
requires the pinned scene preparation and replay; this is not new reachability
evidence. Both files are flushed and fsynced before the chunk is sealed.
Replacing `HEAD.json` is the sole commit point for their hashes, counts,
cursor and sampling state. The adjacent report is a convenience receipt:
losing it does not lose or reset the committed cursor.

The sampling order is deterministic, not a random sampler: the input ordinal
and pose index are derived from the cursor. There is no hidden RNG-generator
state to restore. The game's RNG/world state is recreated from the pinned
DLL, capture, context and preparation. Source hashes, Python/Wafel versions,
architecture, A mode/history, input alphabet/order/stride, pose recipes,
product size and chunk settings reject incompatible resumes. Case/time
limits may change between compatible batches.

## Exactly what resume verifies

**Normal resume defaults to full verification.** It streams and hashes every
committed trial and retained file once, checks their lengths and record
counts, follows the commit chain to HEAD, and recomputes the exact enumeration,
status counts, accepted subsequence and next sampling cursor. This keeps the
old corruption-detection coverage, including old chunks, with bounded memory.
The time is included in the new batch clock. This is linear in stored history;
many tiny full-verify batches can still incur roughly quadratic cumulative
resume reading. Chunking removes the repeated *checkpoint* rereads, not the
cost of asking to verify every historical byte afresh.

`--resume-verify latest` is an **explicit narrower contract**. It checks the
manifest/HEAD, final chunk and predecessor metadata, trusting older payloads.
Its receipt sets `historicalContentVerified=false` and records the warning.
A test deliberately corrupts an older chunk: latest passes, while normal full
resume rejects it. Full historical corruption detection requires normal full
resume or `--audit`; it is never claimed for latest mode. SHA-256 checks detect
changed data against the recorded digests, not an attacker rewriting the
entire ledger and its trust anchors.

`--audit` independently repeats the full stored-data checks without creating
a game, changing coverage or replaying gameplay. It does not classify pending
or quarantined data as accepted history. Legacy v1 JSONL is still readable by
this audit; new code refuses to append to its incompatible fingerprint rather
than silently migrating it or overwriting the old result.

## Interruption and corruption checks

Before HEAD replacement, an interrupted chunk is uncommitted. On resume it is
preserved in `recovery/`, and enumeration restarts at the last committed case.
After replacement, the entire transaction is retained. Completed-but-uncommitted
attempts may be executed again; **committed IDs are neither skipped nor counted
twice**. A poisoned append cannot be checkpointed. The OS releases the writer
lock after process death. Windows file-sharing errors get eight bounded rename
attempts; persistent errors still stop the writer.

There are 47 counter/search tests plus the 15 original pilot tests: **62 pass**.
They cover partial writes, truncated and corrupted trial/archive bytes, wrong
enumeration even under resealed envelopes, broken checksums/chains/counters/
sampling, missing files, stale temporary HEAD, incompatible settings, archive
membership, interrupted checkpoints, real child-process exits before and after
the commit point, writer locking and resume with a missing convenience report.
File fsync and atomic replacement support the tested process-interruption
model. Windows lacks portable directory fsync; sudden hardware/power-loss
durability is not established by these tests.

The first real growth attempt encountered a Windows directory-rename denial.
Its audit verified 47,000 committed cases and 16,450 retained recipes. An
unchanged-code resume quarantined the uncommitted chunk and advanced exactly
100 more cases to 47,100. The cause of that denial was not established. The
completed timing table below is a fresh run after adding bounded retries.
The initial failed attempt's duration was not saved by the first benchmark
driver, so it is not folded into the repeatable table; the driver now saves
attempt wall time, exit status and diagnostics before propagating a failure.

## Real runtime benchmark

Windows x64 Python 3.9.13 and Wafel 0.8.5, the existing authenticated JP DLL,
A released, mixed exact ordering, L/D-pad gated by the user's selected scope.
Each of three processes repeats preparation and 80 cached/reference controls;
resumed processes use normal full verification. A separate full audit follows
each size. The external clock includes interpreter startup/shutdown, setup,
source/runtime hashing, resume, trials, writes, durable checkpoints and final
report writing. The phase breakdown is saved in the linked receipt.

| Stored trials after batch | New trials in batch | Whole process seconds | New trials/second | Ledger + archive MiB | Peak game-process MiB |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 5,000 | 5,000 | 10.276 | 487 | 2.99 | 967.78 |
| 20,000 | 15,000 | 19.497 | 769 | 11.96 | 968.16 |
| 80,000 | 60,000 | 63.542 | 944 | 47.86 | 968.62 |

The three batch processes total **93.315 seconds**, or **857 new trials/second**.
Including three additional full-audit processes and benchmark bookkeeping,
the entire completed benchmark takes **99.801 seconds**. Audit processes take
0.818, 1.492 and 3.929 seconds and peak at about 22 MiB; the game process's
roughly 968 MiB is its fixed runtime/cached-state cost. Checkpoints spend
0.110/0.283/1.185 seconds per batch and reread **zero historical payload bytes**.
Normal resumes read 3.14/12.54 MB of prior history. A separate latest-only
80,000-case check reads 636,029 bytes in 0.042 seconds inside the process,
explicitly without verifying older payloads. That is not a full-resume timing.

**Withdraw the old 2.9-day estimate.** Constant-rate arithmetic at the observed
whole-batch rates would give roughly 4.1–4.5 days for 335,544,320 cases, but
that is not a measured multi-day prediction. The measured log growth would
also imply roughly 196 GiB at that size if the outcome/record-size mix stayed
similar. Large-volume filesystem behavior and the number/size of future batches
are unmeasured. A cost model must add preparation for each process and full
validation of each accumulated prefix; frequent small full-verify resumes can
dominate. Latest mode can reduce that cost only by accepting its explicitly
weaker historical corruption check. This does not price a 30/90/150-update tree.

## Reproduce and inspect

From the SSL project:

```powershell
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/concrete-ink-backward -p 'test_*.py' -v
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/wafel-jp-pilot -p 'test_backward_validation.py' -v
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/benchmark_chunks.py --sizes 5000 20000 80000 --process-timeout 180 --output build/concrete-ink-backward/NEW-growth
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/product_sweep.py --audit --output build/concrete-ink-backward/20261003-chunk-ledger/growth-retry/report.json
```

The compact [benchmark receipt](../../instrumentation/concrete-ink-backward/expected-chunk-ledger-benchmark.json)
pins measurements, code/runtime hashes, bounds and limitations. Full ledgers,
accepted recipes, recovery data, phase reports and per-attempt stdout/stderr
remain under `build/concrete-ink-backward/20261003-chunk-ledger/`. Both the failed
`growth/` attempt and completed `growth-retry/` are preserved. No full save
states, ROM, DLL or conversation exports are committed or published.
