# Rank 10A: elevator jolts and ceiling-hanging entry

## Result

Two ordinary entry proposals fail in the checked cases. The elevator's
start/stop jolts do not leave a floor-following Mario far enough above its
base to create freefall. There is also no hangable ceiling above the stock
bucket footprint. Neither result rules out a different selected support,
a skipped reanchor, a retained ceiling from elsewhere, an interaction, or
another moving object. Rank 10A remains open, with low counterexample promise.

The conditional ground-pound height window remains unchanged: granting the
move at the elevator floor can yield a relative height of 260. These entry
checks do not supply that grant or a sideways departure.

## The full nominal elevator cycle

The [offline checker](../../instrumentation/rank10a-ground-pound/check_entries.js)
reads the generated US/JP collision and trigonometric initializers. Starting
from the recorded home height of 4966, it accounts for the idle sample, all
nine starting-jolt samples, 484 descending updates including the final clamp,
all nine stopping-jolt samples, and a parked sample: 504 in total.

The maximum downward change between these samples is 10 units. The largest
starting-jolt drop is about 3.827 units, and the stopping jolt rises at most
10 units above its resting height. Truncating the nominal base to an integer
does not create a larger than 10-unit drop. The proof also permits repeated
height samples, covering waits that leave the same floor-following conditions
true. It does not treat a frozen Mario with a still-moving elevator as a wait.

The actual geometry-input test requires Mario to be **more than 100 units**
above the selected floor before it adds the off-floor input. Even allowing
Mario and the selected base to differ from their respective nominal samples
by one unit each, the checked cycle cannot pass this test. This one-unit
allowance is an explicit live-projection obligation, not a theorem about
every possible transformed surface or floor query.

## The actual Coq execution result

[`Area2Rank10AEntryChecks.v`](../../proofs/Area2Rank10AEntryChecks.v)
checks all five height-assignment expressions in the generated elevator
handler, the selected trigonometric entries, the complete nominal cycle,
and the original floor-distance guard in both game versions. It then
executes that guard in selected Clight memory: the actual Mario Y and
floor-height reads lead to the original false branch, leaving memory
unchanged. The guard does not add the off-floor input; this does not claim
that a previously set input bit was cleared by this fragment.

This is a source-linked local execution result, not one uninterrupted run
from the warp. The remaining connection must derive the normal action/timer
sequence, retained home height and trigonometric values, actual elevator
pose and base selection, and the two one-unit agreements at every relevant
Mario update. Other action changes or position changes are not covered by
executing this one guard. The Rank 10A boundary in Main consumes the new
package; the ultimate impossibility theorem still has its live reachability
and whole-frame refinement premises.

## Where the hangable ceilings actually are

The complete Area-2 static collision stream contains six hangable triangles
in two distant regions. The parser preserves surface types and must reach
the real end-of-triangle marker; an early stop cannot certify completeness.

| Region | X range | Z range | Y |
|---|---:|---:|---:|
| Four eastern triangles | 2355 to 3174 | -3378 to -2559 | 957 |
| Two northern triangles | -1351 to 1352 | 2621 to 3113 | 1853 |
| Elevator's full outer footprint | -511 to 512 | -255 to 768 | Moves |

The Coq result excludes every one of the six triangle bounding boxes from
the entire outer footprint, which is larger than the usable bucket interior.
The four checked moving meshes—Grindel, Spindel, moving wall and elevator—
contain no hangable triangles either. Both regions' data agree between US
and JP. Ordinary hanging requires a hangable ceiling, as checked in
`mario_actions_automatic.c` and the ceiling-grab path in `mario_step.c`.

Thus simply reaching upward from inside the shaft cannot find a fresh stock
hangable ceiling there. This is not a proof that every live ceiling reference
is fresh: a gameplay mechanism that legitimately retains a different ceiling,
or moves Mario to another support, needs its own continuous history and query
accounting. Visiting a distant hanging area after already escaping the cage
does not establish a pre-gate installer.

## What remains worth searching

The [backward support follow-up](rank10a-backward-support.md) now checks the
entire static mesh inside the bucket, proves base coverage, and executes the
real floor-choice segment from loaded answers through its output store. A
lost-support proposal must identify why the live base is missing or rejected;
merely pointing to the lower static floor does not supply the change.

Find the first actual event that supplies an eligible airborne action before
the gate: a different support, an ordinary interaction, a genuine missed
reanchor or an unusual but defined ceiling history. Then account for a useful
sideways effect during or after startup. The ordinary same-face falling-wall
response still points inward in the existing diagnostic; corner histories,
other floor/ceiling responses and subsequent collisions remain separate.
Repeating the nominal elevator jolts or looking for a ceiling directly above
the bucket cannot supply the missing entry under the conditions above.

## Reproduction and scope

From the repository root, use the installed proof wrapper:

```sh
SM64_PROOF_SWITCH=sm64-item-proof SM64_PROOF_VCAP_KB=6291456 \
  bash pipeline/build.sh \
  -C SSL-Coq/less-than-one-a-press check-rank10a-entry
```

From the SSL project:

```sh
node instrumentation/rank10a-ground-pound/check_entries.js
node instrumentation/rank10a-ground-pound/check.js
```

Source authority: pinned revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, generated US/JP elevator handler,
Mario geometry-input handler, collision arrays and trigonometric initializers.
This tranche uses proof files and offline arithmetic only; it creates no
controller movie and changes no game state.

## Validation

On 2026-09-07, `check-rank10a-entry` compiled the new module and Main,
passed the no-holes and link-hygiene checks, and completed all nine assumption
audits with only the existing standard logical and CompCert assumptions.
Both offline checkers passed for US and JP. The new module compiled within
a 4 GiB virtual-memory limit; rebuilding the large Main module required the
6 GiB limit shown above after an initial 4 GiB attempt exhausted its budget.

The required repository-root proof-discipline audit was also rerun. It
remains unsuccessful because its separate legacy build requires the missing
`sm64-proof` opam switch; its no-holes and structure checks passed. This is
not a claim that the repository-wide build is green. The focused SSL build
above used the installed `sm64-item-proof` switch and completed successfully.

[Back to Rank 10A](../no-a-route-atlas.md#route-rank-10a)
