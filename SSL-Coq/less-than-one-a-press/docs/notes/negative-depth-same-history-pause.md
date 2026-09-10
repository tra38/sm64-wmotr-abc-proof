# Negative-depth same-history proof: pause recommendation

Recorded on 2026-09-10, after proof commit `bc8a53e`.

## Recommendation

Put the full negative-depth same-history proof on hold for reassessment.
Preserve the existing results, but pause further helper-by-helper expansion
until there is a credible plan for connecting them into the final argument.
This recommendation concerns this proof effort, not the entire SM64 project.
It does not declare negative depth impossible or close the Ink route.

## Why this has taken so long

The original question is whether useful negative quicksand depth can occur
without a new physical A press. Proving that it cannot happen under every
permitted controller history requires accounting for a substantial part of
the game's update machinery. The proof must connect stored values, controller
samples, movement, actions, and the order of other game updates in one
continuous execution. Ruling out an individual calculation is not enough.

The remaining work is not yet a complete, manageable list of similar tasks.
Connecting one operation often exposes additional requirements about earlier
state or other calls. This makes a reliable completion estimate difficult.
Compilation delays add overhead, but they are not the fundamental bottleneck.

The assistant's approach has also contributed: it repeatedly extended short,
locally verified segments before establishing a reusable argument for the
whole update sequence. Those results are genuine, but progress toward the
final yes/no answer has been disproportionately slow. More compute alone
will not correct that approach. File counts, successful builds, and the
number of proved lemmas are not measures of how close the route is to closure.

## What we can honestly conclude

No clean no-A negative-depth counterexample has been found. Several local
mechanisms have been excluded under their stated conditions. The route
itself has not been disproved, and the search has not exhausted all options.

The latest tranche connects consecutive completed button and joystick calls
to the first wall-query statement while preserving the relevant depth,
action, timer, and input facts. Those call completions still need to come
from the same start-to-use gameplay history. Geometry, later actions and
landing, later controller samples, and intervening game updates remain
unconnected. This is useful partial progress, not a proof covering arbitrary
gameplay. Floor alignment's separate height question also remains open.

## What should happen before resuming

First conduct a bounded review of the proof's overall design. It should:

1. Identify the remaining whole-history obligations, including any gaps in
   that inventory, rather than assuming the inventory is already complete.
2. Match existing results to those obligations and list the conditions that
   still have to be established where the game actually uses them.
3. Explain how one reusable argument will cover successive game updates and
   every permitted controller choice without combining unrelated runs.
4. Choose a concrete next checkpoint that removes a meaningful part of the
   overall gap, and state when to stop if that checkpoint cannot be reached.

If the review cannot produce a credible closure plan, keep this effort
paused. Another isolated helper result should not, by itself, justify
restarting the expansion. A newly discovered concrete gameplay candidate
could justify a targeted test without restarting the entire universal proof.

## Work retained

The current proof tranche is committed and pushed as `bc8a53e`; its Coq build
and assumption checks passed, with the timeout and retry history recorded
in the [shared-history notes](ink-shared-history-invariants.md#verification).
The [closure argument and progress ledger](negative-depth-shared-closure.md)
remain the technical reference. This planning note changes no proof
assumptions, accepted starting conditions, or route verdicts.
