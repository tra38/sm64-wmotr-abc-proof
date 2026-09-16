# Square root: the routine is proved; the library binding is separate

The actual two-instruction routine now has a checked local proof. Under
ordinary floating-point controls and a nonnegative normal-or-zero input,
it returns the correctly rounded binary32 square root and leaves RAM
unchanged. The real US/JP triplet distance helper's argument is also proved
to be in that supported range, under the existing position bounds.

This does **not** yet remove the square-root premise from the old Clight
theorem. Its external-call model still has no implementation attached to
the name. The new proof supplies a concrete implementation result; binding
that reached external event to it remains explicit. Whole fresh-triplet
confinement and Rank 10A remain open.

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

## What this gives the caller

For a reached helper call that is realized by this proved instruction
routine, the returned distance fails the strict 3000 spawning test and
the helper's output memory equals its input memory. In particular, the
current-object pointer and the parent's raw fields retain their values.
That memory result follows from the instruction execution; it is not a
blanket harmless-call assumption.

The cross-language realization is still a premise of that caller corollary.
CompCert represents the generated declaration as `EF_external "sqrtf"`
and leaves `external_functions_sem` unspecified. A C declaration supplies
the signature, not the assembly body. Neither a matching function name nor
an instruction proof silently identifies those two execution relations.
No generated program, global external semantics or existing axiom was
changed to conceal this gap.

The remaining connection is therefore precise: relate the reached C
argument to the machine argument register, match the returned register and
RAM to the same C call, and justify the stated controls at entry. This
tranche does not certify the whole caller-to-machine refinement. The
interpreter loop, other engine updates and intervening actors also remain
separate parts of the fresh-triplet question.

## Checked artifacts

- [SqrtfMachine.v](../../proofs/SqrtfMachine.v) decodes the authentic words,
  proves ordinary execution exists, and proves the rounded result and RAM frame.
- [Area2TripletSqrt.v](../../proofs/Area2TripletSqrt.v) proves the actual
  reached argument is supported and states the explicit realization corollary.
- [Area2TripletSpawner.v](../../proofs/Area2TripletSpawner.v) exposes the
  existing rounded squared-input bound for reuse.
- The fresh-triplet and combined Rank 10A boundaries in MainTheorem consume
  the new results. The existing library-binding gap is not marked
  complete.

The selected audit passed on 2026-09-15 in
`build/audit/20260915-212452-yg859npz/`. It registered 570 sources and checked
400 of 494 proof modules in Main's import closure, with 94 standalone
modules. The Main boundary, rounded-result theorem, result/RAM theorem,
reached-input theorem and realization corollary use respectively 7, 4, 4,
7 and 7 allowed foundations. Compilation, proof-hole, link and integration
checks passed. No new axiom or admitted proof was added. This is a selected
dependency audit; its foundation counts do not count the explicit premises
or certify the remaining cross-language binding.

The subjective estimate for whole Rank 10A remains 2–5%. This removes
uncertainty about the local calculation under its conditions, without
constructing a Goomba route or finishing all successive spawning checks.
