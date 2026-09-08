# Working backward from collection to contact

> Work on hardest obligation 2, reviewed 2026-09-08. This is partial progress,
> not a proof that either target star is impossible without A.

## Why work backward?

Instead of guessing another way out of the elevator or off the pole, start
with the game giving Mario the desired reward. Ask what had to happen just
before it, and repeat. Many very different routes eventually use the same
collection code, so a necessary condition there can cover them together.
This does not mean running the game backward: several earlier situations can
lead to the same result, and we must keep every allowed alternative.

For an ordinary star pickup, the intended chain is:

1. The game awards the correct target star.
2. The collection handler uses the correct star object and star number.
3. The interaction code selects that object from Mario's recorded contacts.
4. The contact record comes from a successful collision check involving those
   same live objects.
5. Their positions and touch ranges satisfy the check at that moment.

Then work forward from the accepted start to prove that no allowed no-A play
can meet that condition, or produce a controller-reachable example that does.
Backward reasoning narrows what to search for; it does not make an imagined
starting position reachable.

## What this tranche establishes

The two contact searches now have proofs about their actual US and Japanese
game-code executions, including arbitrarily many completed search iterations.
They are not limited to a particular controller recording or a manually filled
contact list.

- A successful secret pair check reads the requested Mario pointer from the
  first object's contact list. It checks the current list count before that
  read. This is the exact pointer that passed the comparison, not merely an
  object with a similar position or behavior.
- A star search that returns an object pointer reads that pointer from the
  contact list and accepts its interaction-type comparison. The proof retains
  both reads of Mario's object pointer, the list count, and the object's type
  read, all in the search's unchanged memory.
- Both searches leave memory unchanged, including their function entry and
  return. They do not call an outside helper. The pair check returns only zero
  or one.
- The ordinary secret callback calls the actual selected pair-checking
  function. Any completed invocation with a net memory change or an observable
  event must have received a successful answer using its entry reads, before
  entering the effect-producing branch. Function entry and return are included;
  this ordering cannot be assembled from different executions. When the Mario
  value read at entry is a pointer, the matching list read follows from the
  same entry memory. This does not yet identify which change was puzzle credit.
- The star collection handler keeps its original Mario and star pointer
  arguments. That is a fact about which pointers it carries, **not** a claim
  that all object contents or lifetimes remain unchanged across its helpers.

The earlier [contact-comparison proof](object-contact-necessity.md) already
shows which distance and height tests every successful collision check must
pass. These new consumer results approach that check from the other side.
The missing link between them is the history of the stored contact.

## The separate secret-progress case

Pyramid Puzzle also initializes its progress from how many trigger objects
remain. It can therefore report progress from missing triggers rather than
from a new touch in the current visit. Rank 7A already tracks this case.
An exhaustive argument must explain why each relevant trigger is missing,
including earlier visits, and identify the correct puzzle controller. We must
not replace that work with the claim that every credit requires a new touch
during the final visit.

## What is still open?

First, connect the real award and secret-counter changes to the right consumer
invocations in the whole game. For stars, this includes the interaction-table
selection, the object passed to the handler, the star number read after its
helpers, and the actual saved reward. For secrets, it includes the nearest
puzzle-controller lookup, the counter update, trigger removal, and progress
restored at initialization. Selecting a star-like interaction is not the same
as awarding either target star. A credit observed before the callback finishes
also needs an argument about that partial execution; the new full-call theorem
does not silently supply one.

Second, show where each consumed contact entry came from and why it still
means the intended contact when used. This includes list clearing, capacity,
registration, later updates, object identity and lifetime, and the order of
events inside a frame. A read from a contact list is not, by itself, evidence
of a fresh collision.

Finally, establish the collision routine's actual position and touch-range
readings, then connect the resulting necessary contact to every allowed
controller history. No elevator exit, pole jump, or particular visual route
is inserted as an assumption. No route rank or counterexample-promise estimate
changes just because these local links are now checked.

## Proof files and verification

- [ContactConsumerSource.v](../../proofs/ContactConsumerSource.v) resolves the
  selected search, secret, initialization, and interaction-dispatch bodies.
- [ContactConsumerExecution.v](../../proofs/ContactConsumerExecution.v) proves
  the search read witnesses, whole-call memory frames, and preserved handler
  arguments.
- [ContactCreditExecution.v](../../proofs/ContactCreditExecution.v) connects the
  successful pair-call result to its actual argument binding and matching read.
- [SecretContactExecution.v](../../proofs/SecretContactExecution.v) follows the
  ordinary callback's entry reads and direct query call, then proves the
  necessary-contact result for the full invocation.

The focused target is `check-contact-necessity`. The overall theorem still
has its existing whole-execution, route-classification, and first-access
requirements; the new modules do not silently assume those away. All results
concern successful executions of the selected Clight programs, not an
independently established correspondence to retail-console execution.

## Checks on 2026-09-08

All four new proof modules and the integrated main theorem compiled with the
installed `sm64-item-proof` toolchain. The focused `check-contact-necessity`
target passed its unfinished-proof and link-consistency checks and all 19
assumption audits. No new project-local axioms appeared; the overall
conditional theorem retains its previous standard Coq/CompCert foundations
and its three explicit remaining requirements. The changed documentation
links and Git whitespace checks passed as well.

The separate repository-wide discipline audit still fails its legacy build
because the old `sm64-proof` toolchain is absent, as before this tranche. Its
other checks passed. That legacy failure is not reported as a successful
repository-wide build.

[Back to hardest obligation 2](../hardest-obligations.md#2-show-what-every-successful-collection-really-requires)
| [Back to the route atlas](../no-a-route-atlas.md)
