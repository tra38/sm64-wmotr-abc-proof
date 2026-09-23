# Local RNG-schedule state reductions

`analyze.py` executes the generated US/JP native cog/spinner bodies in the
fail-closed scalar/object-field evaluator `ast_exec.py`. It cross-checks every
row against unchanged functions extracted from decomp commit
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, compiled as an isolated host test.
The host supplies RNG words and the spinner's explicitly contracted generic
timer increment. It does not edit or run a ROM or emulator.

Run from the proof repository in Ubuntu-24.04 with Python 3 and GCC:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-state-reduction/analyze.py
```

The default committed metadata receipt is
`docs/notes/ttc-cog-state-reduction-results.json`. Native build artifacts and
the complete reduced transition tables go to ignored `build/cog-state-reduction/`.
No third-party Python packages are required. Assertions are part of the check;
do not use Python's `-O` option.

The audit checks all 27,040 local state/outcome cases per version (including
both cog directions and both binary32 signs of zero), plus 196,608 raw-selector
cases per version. It checks closure, identical draw counts and equivalent
successors for every pair merged by a proposed key. Independent partition
refinement finds the same 480 cog, 121 recurrent spinner and 122 extended
spinner classes. It also records a real-seed counterexample to discarding
cog target sign, and examples where equal RNG keys have different motion.

The generated uses of raw RNG temporaries are checked before enumeration.
All 65,536 single-word magnitude/sign/timer selector inputs are cross-checked;
every combination of their output classes is then checked in every local
state. This factors the raw-word pair space rather than claiming to enumerate
all 2^32 pairs per state. The finite input alphabet permits more word sequences
than the actual shared RNG, making its equivalence condition stronger but its
minimality result inapplicable as a lower bound for a seed-aware whole game.

These are **host finite checks**, not CompCert `exec_stmt` derivations or a
verified interpreter. No Coq theorem or capstone premise is discharged. See
the [report](../../docs/notes/ttc-cog-state-reduction.md) for exact domains,
the timer boundary, composition requirements and the geometry counterexamples.

`count_space.py` separately reproduces the arithmetic comparison with the
video's product from committed receipts:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-state-reduction/count_space.py
```

It writes `docs/notes/ttc-cog-search-space-results.json`. The hypothetical
hybrids retain every other video factor; they are not complete-state counts,
new game executions, or benchmarks of a reduced scheduler.
