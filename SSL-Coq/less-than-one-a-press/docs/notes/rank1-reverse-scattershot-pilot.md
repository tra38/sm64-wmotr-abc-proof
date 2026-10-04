# Rank 1: compact storage and a small Reverse Scattershot pilot

Follow-up: the [146-parent audit](rank1-parent-mismatch-audit.md) now reports
the exact overlapping mismatch counts and continuously replays every actual
suffix past its unequal parent. None produces the checked Ink payoff; the
source ledger and strict archive stay unchanged. The counts below remain the
original stopped pilot's results, not a claim that parent inequality alone
rules out a useful continuation.

3 October 2026. **The backward pilot runs, but it has not found how gameplay
makes the gap.** Its 2,000 native-update allowance completed 292 distinct
context/pose/input-suffix combinations: 74 passed the selected conditional
installation checks and 218 failed. The 146 earlier-step proposals all failed
their first parent checkpoint. The deepest validated Ink chain remains one
update. Twelve retained entries represent six pose recipes and twelve different
input suffixes, rather than twelve newly discovered gap mechanisms. We stopped
both comparison arms and the resume controls; no long search is running.

This is application work and finite conditional evidence. No Coq source,
impossibility result or atlas estimate changes. Rank 1 remains at the subjective
1–2%. A reachable Ink result still needs an uninterrupted, patch-free controller
replay from the accepted starting state under the allowed A-button history.

## What storage now costs

The old 80,000-trial dataset is preserved. A compatibility reader audits legacy
version-1 JSONL, version-2 raw chunks and the new version-3 compressed chunks.
The migration tool writes to a new directory; it never changes the source.
Changed code/configuration cannot silently append to an incompatible old run.

New product rows store a case ID, shared pose-recipe ID, controller index,
status code and any diagnostic detail. The manifest supplies the complete
recipes and input alphabet. Accepted files contain references to those trial
IDs, not another copy of each accepted record. Each bounded chunk is compressed
independently with deterministic gzip settings. The bounded reverse archive
also keeps its live reconstruction recipes in checkpoint metadata; that small
cache is deliberately separate from an ever-growing duplicate accepted log.

These are measurements on actual existing records, with no new game trials:

| Source prefix | Old payload bytes | Whole compact ledger bytes | External total seconds |
| --- | ---: | ---: | ---: |
| 5,000 | 3,124,036 | 52,824 | 4.849 |
| 20,000 | 12,514,546 | 188,415 | 9.386 |
| 80,000 | 50,106,205 | 732,752 | 24.402 |

Every row includes a full audit of the original 80,000-row source, migration,
checkpoints, a full compact audit, an explicitly weaker latest audit and process
startup/finalization. The conservative 80,000-row reduction is **98.54%**.
Multiplying this observed compact size by 335,544,320/80,000 gives about
**3.07 GB**, replacing the old format's roughly 210 GB arithmetic. That is a
same-record-mix projection, not measured capacity: larger IDs, different
diagnostics, metadata, recovery files and filesystem allocation can change it.
It does not project storage for an expanding reverse tree.

At 80,000 rows, source verification took 2.636 s, initialization 0.018 s,
migration including checkpoints 14.999 s, full compact audit 6.193 s and latest
audit 0.062 s. Checkpoints account for 6.630 s *within* migration, not another
additive phase. Their raw/compressed payload read and write counters each total
26,436,549 bytes; they do not include metadata IO. Full audit read counters total
732,751 bytes and latest 18,126 bytes. Peak process memory was 26,599,424 bytes
(25.37 MiB); new native game processes peaked near 153 MiB after preparation was
changed to retain only the requested recent contexts. Filesystem byte totals
are logical lengths, not allocated-block measurements.

Compression saves space, **not the work of checking every record**. The full
compact audit was slower than the source audit in this measurement because
decoding and semantic validation still cost CPU. No new multi-day completion
forecast is warranted.

## What integrity and resume mean

Normal resume still verifies the entire committed history. It checks compressed
size/SHA-256, gzip integrity, bounded decompressed size, original-byte SHA-256,
record ordering and semantics, accepted references, counts, the commit chain,
cursor and scheduler/archive replay. Chunk hashes are computed only for new
bounded data at checkpoints; historical payloads are never reread to checkpoint.
Full resume is linear in history and repeated full resumes repeat that work.

`--resume-verify latest` is explicitly weaker. It checks the manifest, HEAD,
last chunk and predecessor metadata, trusting earlier payloads. Its receipt
labels that trust. Old-chunk corruption tests pass latest and fail full audit.
Use default full resume or `--audit` for full-history corruption detection.
Checksums detect changed bytes against stored metadata; they do not authenticate
an adversary rewriting the entire dataset and all its checksums.

HEAD replacement remains the sole commit point. Compressed trial data,
accepted references, counts, attempt cursor, sampler and retained archive are
sealed together. Partial writes or interrupted compression/checkpoints leave
uncommitted material in recovery, without advancing that commit. An unfinished
candidate consumes actual updates but gets `incomplete-budget`, no gameplay
verdict and no sampler advance. Resume retries that proposal, with a new attempt
ID; complete proposals are not skipped or counted twice. Receipts are convenient
summaries, not the authority for progress. Process-crash recovery tests do not
establish hardware power-loss durability on Windows/OneDrive.

## Separate budgets

`--setup-seconds`, `--verification-seconds` and `--search-seconds` are separate;
`--wall-seconds` optionally caps overall elapsed time. In the product counter,
`--seconds` remains a compatibility alias for **search work only**. Search work
includes native validation and bounded candidate bookkeeping, but excludes
explicit checkpoint phases. Sixty seconds of search can therefore take more
than sixty seconds overall.

Time limits are cooperative. Setup/verification check between native updates or
bounded IO operations; search checks between whole candidate replays. An
in-flight native update/IO cannot be preempted. Safe checkpoint/close operations
can exceed a wall limit. The native `--game-updates` allowance is stricter: it is
checked before every advance, including suffix and retention replay. A partial
replay is recorded separately from candidate failures.

If verification cannot finish, the run reports **verification incomplete**,
tests zero new candidates and preserves the old HEAD and receipt. It does not
search on partly verified history. Receipts separate preparation, verification,
search, checkpoints and cleanup. External benchmark clocks additionally include
Python startup, final disk enumeration, receipt writing and exit, which are
outside the in-process phase clock.

## How the backward pilot chooses and validates moves

Seed **20261003**, depth ceiling **3**, archive **12**, at most **5,000** attempt
records. Each comparison arm received **2,000 actual search-game updates**,
including suffix and retention updates, with setup/verification/search limits
of 30 s each and an overall cooperative limit of 90 s. These budgets were fixed
before the final run. Both also used the same 495 preparation advances, timed
separately. A released was checked without a new A edge in every tested suffix.
The scene and four-pillar completion are still supplied conditionally.

Fresh sampling cycles across twelve unique complete-context/patch recipes, seven
button classes (none, B, Z, B+Z, camera, R, Start) and nine disjoint stick regions.
Seeded affine permutations sample each declared stratum without replacement,
without materializing the product. The L/D-pad gate remains the user's selected
scope. Identical complete context, patch and input are executed once, then the
Original, Variant and Hybrid predicates are evaluated separately. Their distinct
movement and raw/display requirements are retained.

Once an archive exists, fresh trials and earlier-step proposals alternate.
Longer chains get priority, with every fourth expansion reserved for shorter
branches. Coarse buckets only influence scheduling and retention: entries retain
their own velocities, timers, support, RNG/controller observations, exact suffix
and provenance. Matching display heights never merges states. Passing counts
are not a diversity measure; eligibility is not evidence of reachability.

The implemented earlier moves propose ground copy/sinking, four-quarter freefall
arithmetic and the final automatic-message update. Their candidate values are
derived from each target parent. The game, not an SMT solver, validates them.
Horizontal approaches, moving-support/rotation inverses, other action/writer
families, RNG/context variations and controller-reached earlier contexts are
still missing generators. More sampling cannot cover those absent moves.

Native full snapshots are retained in memory. Wafel's opaque SaveState cannot be
exported as a portable file, so disk stores an exact reconstruction recipe:
pinned DLL/capture/source/version, initialization/controller prefix, context
frame, earliest patch, all earlier inputs and the shared 23-update neutral
retention suffix. Resume recreates the context and checks every stored
observation before searching. Deterministic reconstruction is required; no
full-memory equality theorem is claimed.

For each extension, the validator restores only the earliest context, applies
one earliest patch and replays the entire suffix continuously. It checks every
named parent observation, exact movement at disappeared-action entry, endpoint
fields, Area-1 top retention and the first Area-2 action-entry displacement.
The platform can clear later in that first Area-2 update; demanding that it
remain set at the *end* of that update was an erroneous gate, corrected before
the final comparison. The earlier diagnostics remain in ignored build output.

**One checkpoint condition is still explicit and unproved per input.** Wafel's
within-update action log exposes movement, but not raw collision/display at the
accepted warp return. The three targets retain separate raw/display requirements
under the declared installation-prefix preservation condition. Earlier proposals
are not required to inherit those final records. Existing exact emulator fixtures
check the named controls, not every sampled input. Thus “passed” below means
selected conditional checks and the continuous native payoff, not independently
observed agreement on all nine accepted-return position words.

## Equal native-update comparison

The baseline uses installation-menu-first scheduling with the **same new
validator, compact storage and execution reuse**. It is not the old product
executable: that executable did not replay retention for every candidate, so its
trial count would not be an equal validation workload.

| Metric | Menu first | Reverse Scattershot |
| --- | ---: | ---: |
| Native search updates | 2,000 | 2,000 |
| Distinct completed combinations | 158 | 292 |
| Selected conditional passes | 80 | 74 |
| Rejected complete combinations | 78 | 218 |
| Incomplete final attempts | 1 | 1 |
| Earlier-step proposals | 0 | 146 |
| Archive entries / coarse buckets | 12 / 12 | 12 / 12 |
| Retained pose recipes / input suffixes | 6 / 12 | 6 / 12 |
| Deepest validated chain | 1 | 1 |
| Preparation seconds | 1.366 | 1.170 |
| Verification seconds | 0.014 | 0.014 |
| Search work seconds | 1.022 | 1.327 |
| Checkpoint seconds | 0.238 | 0.273 |
| Cleanup phase seconds | 0.014 | 0.007 |
| Other process/receipt overhead seconds | 0.238 | 0.207 |
| **External total seconds** | **2.892** | **2.998** |
| Whole ledger bytes | 93,921 | 138,599 |
| Peak process bytes | 159,879,168 | 160,063,488 |

The measured inclusive rates are 54.63 and 97.40 completed combinations/s, or
691.53 and 667.10 native search updates/s. The mix differs: earlier rejections
often finish after one update, while an installation pass consumes 24. These
rates price this small comparison only, not exhaustive 30/90/150-update trees.

The 146 earlier proposals comprise 72 ground, 51 freefall and 23 final-message
attempts. All fail their parent checkpoint. Fresh trials cover all seven button
classes and all nine stick regions. The 74 conditional passes divide into
Original 50, Variant 12 and Hybrid 12; logical predicate evaluations are kept
separate from distinct native executions. None starts with synchronized
movement/collision/display records. The supplied useful disagreements remain
open for further backward exploration, rather than being called contradictions
or newly created gaps.

## Checks, commands and saved records

**78 tests pass:** 63 application tests plus 15 original freefall-pilot tests.
Coverage includes legacy/compact readers, compressed corruption/truncation and
expansion limits, eight interrupted transaction stages, partial tails, full vs
latest verification, incompatible settings, deterministic sampling/archive
replay, verification/setup exhaustion, shared-execution predicate distinctions,
an incomplete-update retry and continuous two-edge replay without intermediate
patching. The positive two-edge Ink test uses a scripted backend; the real Ink
sample still has depth one.

The real Wafel stop/resume control gives identical records, sampler and archive
for 8+8 versus 16 complete trials, each consuming 154 search updates. Full audits
pass. A zero verification budget tests zero candidates and leaves HEAD and the
prior receipt byte-identical. That control took 6.044 external seconds. A
mid-audit interruption is separately tested in code.

Runtime: Windows AMD64, Python **3.9.13**, Wafel **0.8.5**, authenticated JP DLL.
The checked receipt includes actual DLL/capture/source hashes, full recipes,
archive, counts, budget policy, IO and phase measurements:
[expected-reverse-scattershot-pilot.json](../../instrumentation/concrete-ink-backward/expected-reverse-scattershot-pilot.json).

From the SSL project directory, the exact final commands were:

```powershell
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/concrete-ink-backward -p 'test_*.py'
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/wafel-jp-pilot -p 'test_backward_validation.py'
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/benchmark_scattershot.py --output build/concrete-ink-backward/20261003-rss-final-report --seed 20261003 --game-updates 2000
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/runtime_resume_check.py --output build/concrete-ink-backward/20261003-rss-final-report-resume
```

Full per-attempt ledgers/stdout/stderr and comparison receipts remain under
`build/concrete-ink-backward/20261003-rss-final-report/` and
`20261003-rss-final-report-resume/`. Storage measurements are under
`20261003-storage-delivery/`. Supplied full states, DLLs, captures and other private
artifacts are not committed. The earlier 5,000- and 80,000-trial logs remain
unchanged. Missing producer mechanisms and the per-input accepted-return record
condition remain precise limits; no finite exhausted sample becomes an
impossibility proof.
