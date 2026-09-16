# Square root: the routine and a concrete C binding

The actual two-instruction routine now has a checked local proof. Under
ordinary floating-point controls and a nonnegative normal-or-zero input,
it returns the correctly rounded binary32 square root and leaves RAM
unchanged. The real US/JP triplet distance helper's argument is also proved
to be in that supported range, under the existing position bounds.

A concrete local library binding now connects the generated C to that
routine. It checks the actual US/JP declaration, puts the C argument in
the argument register, executes the authenticated instructions and returns
the result register and memory. The whole generated distance helper has
a constructed execution through this binding. No separate numerical-effect
or matching-machine-call premise is needed for that new result.

This is an explicit linked runtime, not a theorem equating an unspecified
external oracle with a real library. The older Clight-oracle theorems keep
their premises. Wider game and OS control history, repeated spawning checks
and whole Rank 10A remain open.

## What the routine actually does

The shared game source, `lib/asm/sqrtf.s`, contains `jr $ra` followed by
`sqrt.s $f0, $f12` in the return's delay slot. The existing authenticated
JP manifest contains exactly those two words. Its ROM-backed verifier was
rerun successfully for this tranche. The Coq decoder reads the instruction
fields from that manifest; it does not replace the generated C with a
handwritten square-root function.

The new instruction fragment follows the delayed return and the single
floating-point operation. It uses Flocq's IEEE operation, whose correctness
theorem relates the result to the real square root rounded to binary32.
The proof derives the returned register, return destination and unchanged
RAM. It also preserves the general registers and every floating-point
register except the result register. A constructive existence theorem
shows that the admitted input conditions allow an execution; the result
does not rely on an impossible call.

This is a small, documented instruction model, not a proof of the processor
hardware or a complete console simulation. It projects RAM, register data
and delayed control flow. Floating-point exception flags are outside that
projection; their preservation is not claimed.

## A necessary correction to “finite, nonnegative”

That description alone was too broad for a guaranteed ordinary return.
The [NEC VR4300 manual](https://hack64.net/docs/VR43XX.pdf) specifies that
SQRT uses the current rounding mode and that denormalized operands cause
an unimplemented-operation exception (pages 243–244 and 605). The theorem
uses a nonnegative normal number or signed zero, a usable floating-point
unit, nearest-even rounding and disabled inexact trapping. These are
call-entry conditions. The source's ordinary initialization enables the
floating-point unit and installs controls with that rounding mode and
inexact trapping disabled; preservation up to every later call is not
newly proved here.

For the triplet calculation this corner case is excluded by a proof,
not a sample. From the existing full-base rectangle and bounded vertical
difference, its actual rounded sum of squares is finite and lies between
15,070,322 and 536,870,912. The reached-call theorem follows the real
helper's reads and expression to that very argument. There is no subnormal,
negative, infinite or NaN argument in this conditional case.

## What the new binding proves

The exact selected US and JP global environments resolve the name to the
expected single-float declaration. This is a checked lookup result, not a
name-matching assumption. The binding passes its C argument into register
f12, starts the authenticated JP instruction routine, and reads f0 on
return. The return-address and memory results follow from executing the
instructions. Every successful bound call under the stated controls has
the same numerical result and unchanged RAM. Every supported input also
has a constructed bound call, so this does not rely on a call that cannot
execute. The shared library source supplies the same routine for US; no
new proof of the complete US or JP retail compiler output is claimed.

The complete generated distance helper is followed from function entry:
its two pointer arguments, six Object-coordinate reads, rounded arithmetic,
resolved library call and C return. Under the existing rectangle and
vertical-input bounds, its linked execution returns a distance that fails
the strict 3000 spawning test and leaves memory unchanged. This is a
constructive local execution result, together with uniqueness of the
external-call result; it is not an all-gameplay-history theorem.

The normal control profile is decoded from Status bit 29 and the FCSR
rounding and inexact-enable bits. The checked profile has a usable
floating-point unit, nearest-even rounding and inexact trapping disabled.
The instruction execution preserves those controls. The caller theorem
also accepts any entry controls satisfying those precise conditions.
Preserving them from level initialization through arbitrary earlier game
and OS activity is not proved here. The profile check must not be reported
as that missing history theorem. Floating-point status flags are still
outside the instruction projection.

## What changed in the execution model

The generated C and CompCert installation are unchanged. Ordinary steps
in the new local runtime are literally the existing Clight2 steps; the
external-call step instead runs the explicit library adapter. Other
externals and builtins have no implementation in this local runtime.
The distance helper needs none of them, and its whole constructed execution
checks that fact. This is a declared model extension for this segment,
not a new axiom or a blanket guarantee about other calls.

CompCert leaves its original external-functions parameter unspecified.
It is therefore not sound to infer that every old-oracle execution equals
this linked execution. The old numeric premise remains in those older
theorems. The new theorem supplies a concrete alternative for the distance
segment; transporting and composing the surrounding engine and interpreter
results under that explicit runtime remains work. Parent preservation,
raw Mario bounds at successive checks and other actors are still separate
parts of the fresh-triplet question. The later
[conditional sequence theorem](fresh-triplet-spawning.md#the-conditional-result)
now composes the actual distance stage/store and native commands under
precise field frames and a named square-root premise in the older semantics.
It derives rejection at every supplied check without claiming the runtime
transport or gameplay applicability conditions have been proved.

## Checked artifacts

- [SqrtfMachine.v](../../proofs/SqrtfMachine.v) decodes the authentic words,
  proves ordinary execution exists, and proves the rounded result and RAM frame.
- [Area2TripletSqrt.v](../../proofs/Area2TripletSqrt.v) proves the actual
  reached argument is supported and states the explicit realization corollary.
- [Area2TripletSpawner.v](../../proofs/Area2TripletSpawner.v) exposes the
  existing rounded squared-input bound for reuse.
- [SqrtfClightBinding.v](../../proofs/SqrtfClightBinding.v) supplies the
  explicit ABI adapter, decoded controls, instruction control preservation,
  unique external result and actual C return suffix.
- [SqrtfTargetResolution.v](../../proofs/SqrtfTargetResolution.v) resolves
  the exact declaration in both selected global environments.
- [Area2TripletBoundDistance.v](../../proofs/Area2TripletBoundDistance.v)
  constructs the complete helper execution and its rejected distance test.
- The fresh-triplet and combined Rank 10A boundaries in MainTheorem consume
  both the earlier oracle-conditional results and the new linked result.
  They do not equate the two execution models.

The earlier routine/input audit passed on 2026-09-15 in
`build/audit/20260915-212452-yg859npz/`. It registered 570 sources and checked
400 of 494 proof modules in Main's import closure, with 94 standalone
modules. The Main boundary, rounded-result theorem, result/RAM theorem,
reached-input theorem and realization corollary use respectively 7, 4, 4,
7 and 7 allowed foundations. Compilation, proof-hole, link and integration
checks passed. No new axiom or admitted proof was added. This is a selected
dependency audit; its foundation counts do not count the explicit premises
or certify whole-game or OS control history.

The concrete-binding audit also passed on 2026-09-15 in
`build/audit/20260915-222220-_4tibidp/`. It registered 573 sources,
checked 403 of 497 proof modules in Main's import closure and retained
94 standalone modules. The Main boundary, adapter result/frame,
instruction control preservation, selected US/JP lookup, whole-helper
execution and triplet rejection reports use respectively 7, 4, 4, 5, 7, 7
allowed foundations. Compilation, proof-hole, link and integration checks
passed. No new axiom or admitted proof was added.

The subjective estimate for whole Rank 10A remains 2–5%. This removes
uncertainty about the local calculation under its conditions, without
constructing a Goomba route or establishing the conditions of every ordinary
gameplay check. The conditional repeated-check result is recorded separately.
