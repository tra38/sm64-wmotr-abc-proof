# Active SSL proof audit

This is the SSL replacement for the legacy repository audit. It uses the
installed `sm64-item-proof` toolchain and the `LessThanOneAPress` namespace.
It does not require installing the legacy `sm64-proof` switch or building the
separate WMotR project. The old audit is retained for that project.

From `SSL-Coq/less-than-one-a-press`, in Ubuntu/WSL:

```sh
bash pipeline/discipline-check.sh
```

The normal run builds `MainTheorem` and its dependencies, then checks three
entry points: the evidence/collection reduction, the current Ink backward
boundary, and the conditional evidence-bearing whole-run theorem. To replace
that assumption list with particular theorems, pass module/name pairs:

```sh
bash pipeline/discipline-check.sh \
  LessThanOneAPress.Proofs.InkLandingLateClosure \
  ilt_checked_late_calls_exclude_first_negative_final_depth \
  LessThanOneAPress.Proofs.MainTheorem \
  conditional_evidence_bearing_clight_run_impossibility
```

The main theorem is still built when a different theorem list is supplied.
For a build of **every** module in `_CoqProject`, including standalone work:

```sh
bash pipeline/discipline-check.sh --full-build --build-timeout 1800
```

The default build limit is 600 seconds; each assumption query has a separate
180-second limit (`--assumption-timeout`). A timeout stops the build process
group and fails the audit. The existing memory limit defaults to 6.5 GiB.
An explicit `SM64_PROOF_SWITCH` override is supported, but a missing switch
fails immediately: it never falls back silently to another compiler.

## What it checks

The build must succeed before compiled theorem assumptions or the dependency
graph can be trusted. Failed builds therefore skip those checks and fail the
overall audit. The source checks still run, including proof files that have
not been added to Git. Every generated/proof source must be listed exactly
once in `_CoqProject`; missing and unlisted files are failures. The existing
proof-hole scan and generated link-hygiene checks are also run.

Each requested assumption command must both succeed and produce a recognized
Coq report. Empty output, a missing theorem, a failed compiler, and an unknown
axiom all fail. The allowed list is exactly the nine existing Coq/CompCert
foundations inherited from the legacy audit. This fixes the legacy behavior
that could print an assumption check as successful after a toolchain error.

Integration is checked using Coq's generated dependency rules, with full
module paths. The report distinguishes the main theorem's import closure
from intentionally retained standalone results. Existing Makefile assumption
recipes identify standalone audit roots; two documented results not named
there are registered with reasons in
[`discipline-kept.json`](../pipeline/discipline-kept.json). Neither mechanism
claims that a standalone result is used by the main theorem, or that every
Makefile theorem was assumption-audited in this run. A new unregistered
orphan, missing dependency rule, stale registry entry, or import across an
`Unwired/` boundary fails. An unreferenced `Unwired/` file is reported as staged.

## What passing does not mean

Passing establishes mechanical checks for the recorded scope, **not that the
two stars require an A press**. Import reachability is not evidence that a
particular lemma is consumed. `Print Assumptions` lists foundational axioms;
it does not list explicit premises in theorem statements. The remaining
whole-run refinement, route coverage, live storage, and runtime-effect
conditions still need review and proof.

Once toolchain startup succeeds, each audit saves its commands and full output in a unique directory under
`build/audit/`. `summary.txt` is the short verdict; `report.json` records the
scope, theorem list, foundations, and integration categories. `interfaces.txt`
is a source index of proposition-valued interfaces for manual review. It is
heuristic, includes already-proved interfaces, and is deliberately **not**
labelled a complete list of open obligations. Generated reports are ignored
by Git and retained for diagnosis.

## Testing the audit

```sh
bash pipeline/build.sh test-discipline-audit
```

The regression suite covers failed and empty assumption commands, unexpected
axioms, stale-build handling, unlisted files, missing dependency rules,
orphan/standalone distinctions, `Unwired/` imports, and command timeouts.
These fixtures test the audit's verdict logic; they do not replace a real
Coq audit run.

Validation of this addition passed the real default audit and all 26 regression
tests with Coq 8.16.1 and CompCert 3.15. Separate real invocations requesting
a nonexistent theorem or a nonexistent toolchain both correctly failed.
The default report accounts for 496 source files: 76 generated modules and
420 proof modules, of which 326 are in the main theorem's import closure and
94 are standalone-only. The full-build option is covered by the regression
suite, but the all-module build was not the validation run for this addition.
