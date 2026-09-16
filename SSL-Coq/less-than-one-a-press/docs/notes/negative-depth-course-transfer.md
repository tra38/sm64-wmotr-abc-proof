# Negative depth: looking beyond SSL

The question here is stricter than the earlier transfer experiment: can Mario
create a useful negative quicksand depth without ever pressing A, possibly in
another course, and bring it into SSL Area 1? We do not grant a negative seed
for this question. Ordinary controller play and defined, in-bounds gameplay
glitches remain the scope.

## What the wider source search found

The stock named collision data contains quicksand in SSL Areas 1 and 2,
Tall, Tall Mountain Area 1, and Tiny-Huge Island Area 1. The latter two use
shallow quicksand. Searching the full game source found no separate
course-specific depth writer. The existing generated US/JP census identifies
eight functions that directly write Mario's depth; that census covers the
38 selected translation units, not an assumed model of their effects.

| Writer | What matters for a first useful negative value |
| --- | --- |
| Mario initialization | Assigns zero. |
| Common airborne cancellation | Assigns zero. |
| Automatic action dispatcher | Assigns zero. |
| Submerged action dispatcher | Assigns zero. |
| Quicksand update | Clears, raises to 1.1, adds the caller's positive sinking speed, or applies a positive cap. The three source callers supply 0.25 or 0.5. |
| Quicksand death | Adds 5. |
| Quicksand jump landing | Subtracts, then immediately replaces a result below 1 with 1.1. An intermediate negative store is not a surviving seed. |
| Common landing | Adds `(4 - actionTimer) * 3.5 - 0.5`. This is the important remaining producer. |

The checked landing arithmetic needs a timer of at least four for a first
negative result from a finite nonnegative depth. With the stock landing
duration checks, only long-jump landing reaches the relevant fourth and
fifth frames. Other ordinary landing wrappers leave before those late
calculations. The normal first long-jump constructor is behind the
A-pressed test. Repeating a long jump does not explain how the first one
began. Walking off a ledge, bouncing or being thrown into the air is not, by
itself, entry into the long-jump action.

These are strong restrictions, not a new all-game impossibility theorem.
The existing proofs keep the live action history, landing timer, pointer
identity and remaining call effects as obligations. No finite gameplay
search was performed in the other courses in this investigation, and no
clean no-A negative seed was found.

## Bringing a value into SSL

The ordinary cross-course path is `warp_level`, then
`init_mario_after_warp`, then `init_mario` for an active Mario.
Initialization writes `quicksandDepth = 0.0f`. Fresh non-warp level entry
and credits entry also call that initializer. A negative value prepared
in another course therefore cannot simply persist unchanged through this
reset. If depth were negative again later, it would need a new write after
the reset, or a separately established change of the live Mario record.

Instant warps are a relevant exception to the *initialization path*, but
not an identified cross-course bypass: their source code changes the area
inside the current level. SSL's stock instant warps connect Areas 2 and 3,
not Area 1. The castle's SSL painting destinations enter Area 1 through the
ordinary level-change path. This is source and level-data inspection;
it does not classify every possible reachable warp history in Coq.

## What is now checked in Coq

[InkCourseEntryReset.v](../../proofs/InkCourseEntryReset.v) proves that every
completed execution of the real generated US or JP `init_mario` contains
the zero-depth checkpoint. It derives the live Mario pointer at that store,
the exact depth-field address, and the immediately readable zero. The
witness retains the actual allocation, preceding calls, following code and
return; no incoming depth bound or harmless-helper premise is added.

It also follows the complete `init_mario_after_warp` execution. That call
either takes its actual inactive-Mario guard, or reaches the checkpoint
through the correctly resolved internal `init_mario` call. The prefix and
suffix are retained in the same execution. The guard is checked after the
real spawn-node helpers; their preservation of an earlier action is not
silently assumed.

This closes unchanged transfer through the reached reset, including a
negative value made in any other course. It does not prove the depth at the
end of all initialization: later calls could only be excluded as new
producers after proving their effects. It also does not establish that every
possible entry history takes the active guard with the same Mario record.
The existing whole-route coverage obligations remain unchanged.

The selected audit passed on 2026-09-16 at
`build/audit/20260916-161813-zkcoveqa`: compilation, proof-hole and link
checks, and the main boundary plus both new execution theorems. The main
boundary uses nine allowed foundations and each new theorem uses seven,
with no project axioms. There are 579 registered source files; 409 of 503
proof modules are in the main import closure. This was the selected audit,
not a fresh build of every standalone module.

## What remains open

The main unresolved seed question is still a first useful negative write
without A. A meaningful candidate must explain how the landing action and
late timer are reached, or identify another ordinary write that survives
until the depth is used. The cross-course idea additionally has to explain
a route around the reset or a fresh producer after it. Simply finding
quicksand in another course does neither.

The accepted post-initialization SSL starting facts remain available for
the original proof. This wider investigation follows the user's new
request; it does not reopen the abandoned startup reconstruction. The
earlier permission to grant negative depth still applies to conditional
Ink transfer tests, not to this seed-creation question.

[Back to rank 19](../no-a-route-atlas.md#route-rank-19)
