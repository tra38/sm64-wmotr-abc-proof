# What a successful contact check must do

> Status: 2026-09-07. Partial progress on
> [hardest obligation 2](../hardest-obligations.md#2-show-what-every-successful-collection-really-requires).
> This does not close a no-A route or establish a complete collection proof.

## The result in plain English

We now have a checked proof about every successful execution of the selected
US and Japanese object-contact routine, rather than just some tested positions.
Before that routine can report success, its sideways-distance test must accept,
and neither of its two vertical-separation tests can reject. The proof follows
those checks within one execution, including the work before and between them.
It does not assume that Mario has crossed the elevator opening or second pole.

For ordinary finite positions and hitbox sizes, these checks mean that the two
objects are close enough sideways and their vertical touch ranges overlap.
The sideways limit is strict; touching exactly at the vertical boundary is
allowed. The proof uses the game's rounded-number comparisons, not an idealized
distance calculation. It does not silently assume that all coordinates are
ordinary finite numbers.

This is useful for both target stars and the Puzzle's secrets: the same contact
requirement can constrain familiar routes, contact through a wall, a moving
target, and a trick we have not named yet. A wall is not an extra condition in
this contact routine. Whether Mario can reach the necessary position remains
a separate movement and collision question.

## What changed from the earlier work?

The earlier Rank 12B proof showed that a particular later part of this routine
rejects contact from either unchanged gate footprint, once its input numbers
are supplied. The new proof works backward from success of the entire routine.
It establishes that the three comparison checkpoints really were reached and
passed, instead of assuming that execution started at those checkpoints.

It also connects those comparisons to the touch condition already used by the
star and secret proofs. To use that connection, we must establish six specific
numbers that the routine reads or computes. Supplying those numbers is more
precise than assuming that contact happened, but deriving them from live play
is still unfinished.

## Why the order matters

The routine reads positions and touch sizes, asks a helper to calculate a
square root, tests sideways distance, then reads the objects' heights and tests
vertical separation. Only afterward does it record the touching pair. A
picture taken once per frame need not show the exact values at those moments.
The new proof retains the actual intermediate states and their order.

The checkpoint result does not assume that the square-root helper leaves
everything unchanged or returns the intended number. It holds for any completed
call allowed by the chosen execution model. Connecting the comparisons to the
reported positions still requires the helper's actual numeric result and the
relevant read history; the proof does not grant those facts for free.

## What remains to finish obligation 2?

1. Follow each real target-star award or secret credit back to the correct
   recorded object pair, then to the contact check that registered that pair.
   This must cover other legitimate ways the game might set the relevant
   interaction information, not assume they are absent.
2. Show that the six numbers at the derived checkpoints describe that same
   Mario and target, with the actual helper result and read timing.
3. Establish the remaining identity, contact-list capacity, registration, and
   within-frame timing facts. An earlier call involving another object, or a
   contact record from another moment, is not a substitute.
4. Connect these facts to the accepted start and the first necessary contact.
   The later no-A argument must explain why every allowed history cannot
   achieve it, or produce a clean history that does. Neither an elevator exit
   nor a pole jump may be inserted as an assumed requirement.

The shared source-level comparison argument is now available. The whole-game
collection connection remains open, and the overall impossibility theorem
still has its three existing large requirements. No route ranking or
counterexample-promise estimate changes solely because of this result.

## Proof details and remaining readbacks

The implementation is [ObjectContactNecessity.v](../../proofs/ObjectContactNecessity.v).
It uses the actual generated function bodies and the selected program's
execution rules. The earlier
[Rank 12B module](../../proofs/Area2Rank12BContact.v) proves that those bodies
resolve in the selected US and JP programs. A completed body returning integer
one is the starting premise; locating that body execution inside the complete
gameplay trace is not yet proved here.

| Actual checkpoint value | What must be established about it |
| --- | --- |
| Radius total at the sideways test | The rounded sum of the two reported touch radii |
| Distance at the sideways test | The rounded horizontal distance for the reported positions |
| Mario-side bottom at the vertical tests | The reported Y position minus its touch-range offset |
| Target-side top at the vertical tests | Its reported bottom plus its touch height |
| Mario-side top at the vertical tests | Its reported bottom plus its touch height |
| Target-side bottom at the vertical tests | The reported Y position minus its touch-range offset |

The labels “Mario-side” and “target-side” describe the intended reporting roles.
Proving that the routine's actual arguments have those roles is still required.
Both vertical tests share the same derived memory and local-value snapshot.

`ocn_success_requires_ordered_contact_tests` proves the necessary checkpoints
without these readback premises. `ocn_actual_tests_imply_reported_overlap`
connects their comparison outcomes to the existing rounded-number overlap
formula. `ocn_successful_body_supplies_collision_phase_overlap` supplies the
exact contact predicate used by the collection framework, conditional on the
six readbacks and the other stated phase facts. Those remaining facts are
explicitly named by `ObjectContactReadbackObligation` and
`ocn_other_phase_facts`; neither is claimed proved for every live call.

[MainTheorem.v](../../proofs/MainTheorem.v) exposes the ordered-checkpoint result
and the collection-geometry construction interface. This sharpens part of the
whole-program refinement work; it does not discharge
`WholeProgramClightRefinementObligation` or replace the remaining event and
first-access proofs. No live frame certificate is constructed in this tranche:
instantiating this interface inside that certificate is still required. The
selected-code result also does not independently establish correspondence with
a commercial-console execution.

## Checks

The focused build target is `check-contact-necessity`. It compiles the integrated
capstone, checks for unfinished proofs and link-hygiene problems, and prints
the assumptions of the new source and geometry results plus the overall
conditional theorem. Successful checks are verification of the stated partial
result, not completion of obligation 2.

The focused build and all eight assumption audits passed with the installed
`sm64-item-proof` toolchain. The syntax-checkpoint theorem has no global
assumptions; the other results use only standard Coq/CompCert assumptions.
The separate repository-wide discipline audit still fails its legacy build
because the old `sm64-proof` switch is absent, as it did before this change.
Its no-hole and structural checks passed. Documentation links and the Git
whitespace check also passed.

[Back to hardest obligation 2](../hardest-obligations.md#2-show-what-every-successful-collection-really-requires)
| [Back to the route atlas](../no-a-route-atlas.md)
