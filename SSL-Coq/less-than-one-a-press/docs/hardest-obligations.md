# Hardest remaining proof obligations

> Status reviewed: 2026-09-08.

This guide concerns **Inside the Ancient Pyramid** and **Pyramid Puzzle**.

The hardest work is proving that **every allowed way of playing obeys a few
shared restrictions**, not finding a separate argument against every imagined
trick. We already have an overall proof that would rule out collecting either
target star without a new A press if its remaining requirements were met.
Those requirements are not yet all proved for the game we are studying.

This guide explains the biggest gaps in plain English. The first three are
the central problems; the next three describe especially difficult work within
them. The numbers are a reading order, not new route rankings or estimates of
which trick is most promising. For individual approaches, use the
[route atlas](no-a-route-atlas.md); for detailed work items, use the
[checklist](checklist.md).
The [impossibility-proof progress ledger](impossibility-proof-progress.md)
maps existing results to the final argument and tracks the still-missing
connections, including the difference between the accepted outside start and
the clean inside-pyramid entry used by the current conditional theorem.

## 1. Follow the real game without skipping important moments

**The task and why it is hard.** The proof needs one faithful account of what
the game does after the agreed starting point: which input it reads, what moves,
which collisions it checks, and what it remembers for later. A displayed frame
contains several separate events. Mario can move, a platform can change, and a
star can be touched between two recorded snapshots. The game also keeps more
than one record of Mario's position, and those records need not be updated at
the same moment. Looking only at the start and end of a frame can miss the very
event a glitch uses.

**What we already have.** The proof has a framework for connecting these
events, many checked pieces of game code, and detailed recordings of particular
runs. It does not yet supply that complete connection for every allowed run.
An accepted starting record settles the facts it records; it does not establish
everything that happens afterward.

**What finishes it.** Show that each relevant event in the real game is
accounted for, in its actual order, from the accepted start onward. This must
include events inside a frame and the exact controller history. We must not
combine a position from one hypothetical run with a floor or object history
from another.

## 2. Show what every successful collection really requires

**The task and why it is hard.** We need a necessary condition for collecting
each target star, not just a description of the familiar route. Saying
"Mario must jump out of the elevator" or "Mario must jump off the pole" would
assume away the alternatives we are investigating. Contact through a barrier,
a moving star, or a changed supporting floor must receive the same attention
as Mario visibly crossing an opening. The decisive contact could also happen
during the very frame in which Mario first gets access.

**What we already have.** The [shared contact proof](notes/object-contact-necessity.md)
shows which sideways-distance and vertical-separation tests every successful
contact check must pass. Working backward from collection now also gives
[checked contact-list searches](notes/collection-backward-contact.md): a
successful secret check reads the requested Mario pointer, and a star search
reads the object it returns and accepts its interaction type. Neither search
changes memory. These are facts about the actual US and Japanese code, not
assumed contacts. We still need to connect the correct saved star or secret
credit to those searches, explain when each contact record was created, and
establish the positions actually read by the collision check. Puzzle progress
restored from missing triggers needs its own earlier-visit history. A simple
height line above the second pole remains inadequate as a substitute.

**What finishes it.** Trace each real collection or secret credit back to the
correct recorded contact, establish the numbers read by that contact check,
and show that the proof reports the same objects at the right moment. Then
account for every game operation that could first make the required contact
possible. This includes changes to the star, secret, or supporting floor,
not only movement by Mario. Work backward to identify every necessary earlier
event, then forward from the accepted start to test whether allowed no-A play
can supply it. Once complete, the argument would cover unnamed tricks as well
as routes already in the atlas; the checked contact searches alone do not
finish this obligation.

## 3. Find restrictions that survive every allowed input sequence

**The task and why it is hard.** A useful restriction must hold at the start
and remain true after every relevant game operation, for every input the rules
allow. Height alone is not enough: position, speed, action, moving geometry,
and timing can compensate for one another. A move that fails once might also
become useful after repeated landings, pauses, or support changes. We need to
cover those combinations without testing every playthrough individually.

**What we already have.** Many local limits are checked, but their conditions
matter. For example, Rank 10A can provide enough relative height if ground
pound is granted, while still lacking a clean way to begin it and a useful
sideways departure. The newer elevator-jolt result excludes one way of becoming
airborne only while Mario continues to follow the same base within the stated
position allowances. It does not yet establish that every possible history
keeps those conditions true.

**What finishes it.** Prove a set of shared restrictions that the game's own
actions, collisions, and updates preserve, including repeated sequences. Then
show those restrictions prevent the necessary star or secret contact. We
cannot use "no-A play never escapes" as an assumed restriction: that would
merely assume the conclusion. If ordinary gameplay breaks a proposed rule,
we must improve the rule or investigate the resulting route.

## 4. Keep track of which floor and object the game is actually using

**The task and why it is hard.** A picture of the level does not tell us which
floor the game selects. Moving surfaces can overlap, objects can disappear,
and the space used to remember one object can later hold another. Mario may
also retain information from an earlier floor check. Therefore, "the elevator
is underneath Mario" does not by itself establish that the game is treating
the elevator as his support at the moment that matters.

**What we already have.** There are detailed checks of level geometry,
individual floor selections, and object creation and removal. In one checked
no-A upper-entry run, the disappearing pyramid top briefly left floor pieces
behind, but no floor check selected them before they were cleared. That is
strong evidence about that run, not a proof about every possible timing.

**What finishes it.** Derive which floors exist, which floor each relevant
check chooses, which object owns it, and what any remembered platform refers
to throughout play. Any legitimate use of an old floor or a replaced object
must be accounted for, not excluded by definition. Many apparently different
platform and position-split routes depend on this same missing foundation.

## 5. Account for the helper routines that can affect the result

**The task and why it is hard.** The part of the game that moves Mario calls
other routines, and those routines can call still more routines. Some compute
numbers; others handle sound, cameras, surfaces, or object creation. A name
that sounds unrelated to movement is not enough to prove that a routine leaves
all relevant game information unchanged. Equally, we should not invent effects
that the actual routine can never have.

**What we already have.** Many called routines and specific effects have been
checked, and some earlier-entry questions are already settled or no longer
required under the accepted start. The outstanding work concerns calls that
can actually happen afterward, the information they receive, and the changes
they can make. It is not a demand to redo all earlier call investigations.

**What finishes it.** For each relevant call, prove that it cannot occur on
the path in question, establish its relevant effects, or show that it leaves
the information needed by the proof unchanged. A routine that legitimately
creates an object must be treated as creating an object, not dismissed as
harmless. This accounting must also cover the further routines it calls.

## 6. Make a promising setup and its payoff belong to one playthrough

**The task and why it is hard.** Showing that a special starting situation
would produce a useful movement is not the same as showing that ordinary
controls can create that situation. A setup might require incompatible timing,
an object that has already disappeared, or access to the very place the route
is supposed to reach. Even a genuine escape is not automatically a star
collection.

**What we already have.** Several mechanisms have checked conditional payoffs,
and some later portions of routes are understood. The atlas deliberately keeps
those results separate from a clean route. For example, a star-dance sequence
after leaving the elevator does not explain how Mario leaves the elevator
without spending the A press. Likewise, Rank 10A's height advantage does not
grant the airborne action needed to start it.

**What finishes it.** For a counterexample, connect the accepted start,
controller inputs, setup, movement, collisions, and collection of the intended
star in one verified playthrough, without inserting a special setup midway.
Alternatively, prove that the required setup cannot arise; then that branch
can be closed without solving its later continuation. Collecting either target
is enough to challenge its corresponding impossibility claim: collecting both
in one playthrough is not required.

## Which starting point and which game does the conclusion cover?

The core proof begins at the agreed point in SSL Area 1, outside the pyramid.
Re-proving the castle journey is not one of these core obligations. Accepted
starting evidence should be reused with its stated limits. "No A press" means
no new press during the agreed input history; an already-held A state must
still have the permitted starting history. We must not silently change that
rule into "A can never be held."

There is also a separate distinction between proving a result for the game's
checked mathematical representation and proving it for the commercial game.
The project has checked substantial source and version-specific evidence, but
the complete connection to the commercial US and Japanese executions remains
unfinished. That connection needs to preserve the decisions that matter after
the accepted start; matching a few snapshots is not enough. Until then, a
conclusion must say which representation and version it actually covers.

Glitches reached through ordinary controls remain in scope when they fit the
agreed game model. Running newly supplied code, accessing memory outside that
model's allowed areas, and arbitrary memory edits remain deferred. That is a
limit on this proof, not a claim that the commercial game cannot exhibit them.

## What would count as decisive progress?

The best next proof work removes a shared "if" from the overall result: for
example, establishing which floor is selected throughout an entire class of
allowed histories, instead of assuming it in another movement calculation.
Such a result can settle parts of several routes at once. A new trick is useful
when it tests one of those shared restrictions, not merely because it adds
another row to the atlas.

A successful compilation, another failed test run, or another calculation
from a granted setup is not by itself a finished impossibility proof. The
finish line is either a complete argument covering all allowed runs in the
stated game model, or a verified allowed run collecting one of the target
stars. An unfinished obligation is not evidence that a counterexample exists.

## Where to find the supporting work

This guide summarizes the [overall proof](../proofs/MainTheorem.v), its
[connection between game events and collection](../proofs/FirstTargetRefinement.v),
the [first-access classification](../proofs/FirstCrossingWriterCoverage.v),
and the open [checklist](checklist.md). The concrete examples come from the
[route atlas](no-a-route-atlas.md) and the
[Rank 10A entry checks](notes/rank10a-elevator-entry-checks.md). The
[execution-scope guide](compcert-execution-scope.md) gives the detailed limits
on what the current proof can claim.

This guide now includes a new, checked contact result for obligation 2. It does
not declare any of the six obligations above finished.

[Back to the route atlas](no-a-route-atlas.md)
