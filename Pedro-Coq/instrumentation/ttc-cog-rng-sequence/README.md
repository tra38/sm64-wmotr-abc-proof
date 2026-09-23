# Finite RNG sequence diagnostics

Scope: `VERSION_US` and `VERSION_JP`; decomp source
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

This answers small, explicit sequence questions raised by the cog video.
It is **not** a full TTC simulator, a reachable game-state search, an emulator
edit, or a new Coq proof. See the [video and sequence report](../../docs/notes/ttc-cog-video-rng-sequence.md).

From the proof repository in Ubuntu-24.04:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-rng-sequence/analyze.py
```

The checker reads the generated US/JP Clight functions. A fail-closed evaluator
interprets the integer-only `random_u16` body on every 16-bit input. It checks
integer ranges and unsigned narrowing, and rejects unsupported AST forms.
It then extracts the unchanged `random_u16` C function from the pinned Git
source, compiles a small host driver and compares all 65,536 outputs. This
cross-check is finite evidence; neither the host evaluator nor its native
compiler is a proved refinement of CompCert/N64 execution.

`results.json` records source/function/analyzer/transition-table hashes,
all cycle lengths, residue counts, exact maximum run lengths for each fixed
draw stride 1–64, and example values. A second algorithm independently filters
all initial seeds against 1,200 prescribed selections for each stride and
checks the first empty candidate set against the longest-run result.

A stride of 1 means consecutive raw values. A stride of 2 models the magnitude
draws of one isolated cog with no other RNG consumer: its sign draw always
occurs too. A larger constant stride is a **prescribed fixed schedule**, not
an established TTC schedule. All these tests run over both every 16-bit input
and the cycle reached from seed zero. None gives a bound for variable gaps.

For a caller-supplied schedule, put a strictly increasing list of one-based
global RNG-call indices in a JSON file and use:

```sh
python3 Pedro-Coq/instrumentation/ttc-cog-rng-sequence/analyze.py \
  --draw-indices /absolute/path/to/indices.json \
  --output /absolute/path/to/diagnostic.json
```

The indices identify magnitude draws required to be divisible by 7. The
filter answers exactly which seeds satisfy **that fixed sequence of indices**.
It does not check object scheduling, mandatory sign placement, cog entry
conditions, two-cog geometry, Mario preservation or controller reachability.
An observed call schedule at one seed must not be reused as the actual TTC
schedule at every other seed without independently establishing that fact.

The default receipt also contains a deliberately relaxed 1,200-selection
example starting at arithmetic seed zero. It skips to the next suitable value
and includes the mandatory sign draw. Unspecified other consumers receive
every skipped value. This only demonstrates that a suitable subsequence exists;
it is **not** a controller choice or a game witness. Its full index list lets
the exact fixed-schedule filter independently check that narrow arithmetic fact.

Host source and executable output stay in ignored `Pedro-Coq/build/cog-rng-sequence/`.
No ROM or guest state is changed or included in these artifacts.
