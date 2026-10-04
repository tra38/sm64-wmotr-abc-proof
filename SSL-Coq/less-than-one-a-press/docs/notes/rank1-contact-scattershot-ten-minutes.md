# Ten-minute contact predecessor search

The corrected run tests **41,540 distinct combinations**, including **20,770
earlier-step proposals**. None of the earlier proposals passes the selected Ink
installation and retention checks. The deepest validated chain is still the
supplied installation update. This is finite conditional evidence, not an
impossibility proof or a new reachable gap producer. The batch is stopped.

## What was actually tried

Seed **20261004**, depth ceiling **8**, archive **24**, A released. The search
alternates fresh supplied installation trials and attempts to extend their
chains one update earlier. It uses Windows AMD64 / Python **3.9.13** / Wafel
**0.8.5** with the authenticated JP DLL. Actual C and the generated US/JP Mario,
moving, airborne, cutscene and interaction modules are hashed in the receipt;
native trials themselves are JP, not a US runtime result or a verified
Clight-to-Wafel simulation.

| Earlier proposal family | Completed trials |
| --- | ---: |
| contact | 11,875 |
| dialog | 40 |
| freefall | 310 |
| ground | 207 |
| horizontal | 7,840 |
| interaction | 498 |

These proposals span **6,433 distinct patched poses** and **20,770 distinct
patch/input-suffix combinations**. The 2,090 move labels are descriptive, not
identifiers: rounded labels can coincide for different exact recipes. The
actual earlier inputs include all seven button classes and nine encoded-stick
regions. These strata schedule samples; untested inputs are not counted as
equivalent. L and D-pad remain excluded by the user's chosen scope.

The fresh half contains **20,770 supplied installation trials**: **10,386** pass
their selected predicates and **10,384** do not. Original has 6,924 selected
passes, Variant 1,731 and Hybrid 1,731. Identical complete patch/input/context
executions are reused while evaluating distinct target requirements; predicate
counts therefore should not be read as independent gameplay routes. The
retained archive has 24 entries, 6 exact pose recipes and
24 input suffixes, all at depth one. These passing rows inherit the gap.

**1,311 earlier proposals start with movement, collision and display records
equal.** None produces a checked Ink continuation. No transition that creates
the useful split was found in this sample. Equality at one boundary is not an
all-history invariant, and no generic gap threshold was proved.

## What changed in the application

The expanded menu adds earlier collision offsets, horizontal walking/freefall
approaches, and automatic-message states 23/24 with several timer values.
Horizontal recipes derive earlier X/Z from the target and proposed speed/yaw;
the real game tests acceleration, walls, rounding and the complete suffix.
The proposal is not assumed to be an exact inverse or a reachable pose.

An unequal saved parent now records its differences and continues the actual
suffix. Every attempt uses one earliest restore/patch, then uninterrupted
controller replay. There is no intermediate patch or restore. A successful
extension would archive actual intermediate observations, not the saved parent
it failed to reproduce.

All 20,770 extensions miss the selected installation goal. Floor height and RNG
differ from the saved parent in every extension, but those differences are
diagnostics, not the stopping test. The receipt includes overlapping position,
action, controller and final-goal mismatch counts, plus one exact example per
family. Those counts do not identify a single universal obstruction.

The validator still requires the selected within-update movement at
disappeared-action entry, the target's distinct collision/display requirements,
original-top retention and first Area-2 displacement. Wafel does not separately
observe collision/display at accepted warp return for every input: those words
remain conditional on the explicit per-input installation-prefix frame.
Named exact emulator controls check the known fixtures, not all sampled inputs.

## The preliminary pass and its repair

The first ten-minute pass completes **40,075** trials and **290,572**
native search updates, with no earlier accepted suffix. Inspection finds menu
starvation: new archive parents replace old ones before later recipes are tried,
and their attempt counters keep restarting near the menu prefix. That pass is
preserved but is not reported as broad menu coverage.

The corrected `seeded-menu-per-parent-v2` scheduler permutes the full move menu
per parent and spreads input classes using the global expansion count. Each
parent visits each exact pose once per menu cycle. Old signatures keep the
original schedule for audit; incompatible configurations refuse resume. Tests
check archive turnover, a complete menu cycle and deterministic resumed records.
The preliminary full-audit attempt stops at its 120-second verification cap
with **verification incomplete**; it creates no gameplay verdict. The corrected
run's separate full audit below passes.

## Time, storage and checks

**600.008 seconds of search work** consume **301,188 native game updates**,
including whole suffix and retention replay. The complete native process takes
**660.322 seconds**. Setup/verification allowances are 60 seconds each, search
600, overall 970, and runner hard cap 1000. Search excludes explicit checkpoint
time. Limits are cooperative, and safe finalization can exceed them. The trial
and update ceilings (one million / three million) are not reached.

| Search-process phase | Seconds |
| --- | ---: |
| checkpoint | 53.748 |
| finalization | 0.024 |
| preparation | 4.461 |
| search | 600.008 |
| verification | 0.029 |
| External complete process | 660.322 |
| Separate full audit | 121.319 |
| Full audit plus diagnostic summary | 132.680 |

Inclusive throughput is **62.91 completed combinations/second**,
or **456.12 native search updates/second**. Search-only throughput
is **69.23 combinations/second**. These measure this sampled mixture;
they do not forecast exhaustive longer trees or revive the retired 2.9-day estimate.

The corrected compressed ledger occupies **17,981,517 bytes** at search
finalization; native peak working set is **287.44 MiB**. The
separate summary/audit reports and process logs add storage outside that ledger.
Full audit checks every chunk hash, record, count, retained reference, cursor
and deterministic archive/sampler transition. All **41,540** records pass; the
summary also matches the search receipt's counts, archive and update accounting.
This is corruption/recovery bookkeeping, not a proof of gameplay reachability.
**91 code tests pass**: 76 concrete-search tests and 15 original freefall tests.
The 256-trial native smoke check also passes full audit.

## Boundaries and commands

Every earliest pose, completed-pillar scene and omitted surrounding context is
supplied conditionally. Original starts with Y=768/768/1938.864868, Variant with
1861/768/768, and Hybrid with 1861/768/1938.864868, in movement/collision/display
order. All use X=-2200, Z=-1024. The original top is checked at timer 131; this
does not cover all live phases. Moving support/rotation, other action/writer
inverses and controller-reached earlier contexts remain absent.

No Coq source or proof verdict changes; all atlas estimates remain unchanged.
A reachable Ink result still needs continuous patch-free controller replay
from the accepted start under the allowed A history. Failed finite samples
cannot rule out mechanisms the generator never supplies.

From the SSL project directory:

```powershell
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/bounded_scattershot_run.py --output build/concrete-ink-backward/20261004-contact-ten-minutes-v2
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/concrete-ink-backward/summarize_contact_run.py --report build/concrete-ink-backward/20261004-contact-ten-minutes-v2/report.json --output build/concrete-ink-backward/20261004-contact-ten-minutes-v2/full-audit-summary.json --seconds 300
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/concrete-ink-backward -p 'test*.py'
& './build/wafel-pilot/python/python.exe' -X utf8 -m unittest discover -s instrumentation/wafel-jp-pilot -p test_backward_validation.py
```

The first command intentionally refuses an existing directory; use a new path
for a separate run. No long search is scheduled. Full ledgers, `report.json`,
`process.json`, `plan.json`, stdout/stderr and `full-audit-summary.json` are
preserved under `build/concrete-ink-backward/20261004-contact-ten-minutes-v2/`;
the preliminary directory is `20261004-contact-ten-minutes/`. The committed
[compact receipt](../../instrumentation/concrete-ink-backward/expected-contact-ten-minutes.json)
pins source/runtime/capture hashes and exact example recipes. DLLs, captures,
snapshots, credentials and conversation exports are not published.
