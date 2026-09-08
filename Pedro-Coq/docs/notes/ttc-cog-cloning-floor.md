# Cloning and floor selection at the TTC cogs

Scope: `VERSION_US` and `VERSION_JP`, pinned decomp revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. This investigation reads the generated
Clight functions. It does not edit emulator memory or establish a cloning route.

## Current answer and its limits

An object's interaction hitbox and its published floor triangles are different
data. Losing ordinary object interaction does not, by itself, make an existing
triangle invisible to floor queries. The triangle must still be reachable from
the queried surface list, contain the query point, and pass the floor tests.
Its stored vertices and plane determine where it is found. Changing the parent
object's position does not translate an already published triangle.

That distinction does not supply a relocated platform at the cog spot. In the
ordinary non-holdable cloning path, `obj_set_held_state` replaces the object's
behavior cursor with a carry script and resets its behavior stack. The three
carry scripts contain `BEGIN` and `BREAK`; their interpreter loop does not run
the original platform's collision-loading behavior. The surrounding generic
object update can still perform flag-dependent movement and graphics work.

On a normal frame, `clear_dynamic_surfaces` calls `clear_spatial_partition`
before terrain objects reload collision and before Mario's object update.
Clearing removes list links; it need not erase the old triangle bytes. A
non-holdable clone whose original behavior no longer runs therefore does not
automatically republish its collision at the new object position. This is the
source-level reason the proposed teleport does not automatically repair the
floor issue. The complete linked frame and cloning route are not yet proved.

Two timing qualifications matter. Previously published triangles can remain
searchable before the next clear. Also, global Time Stop mask 64 skips dynamic
clearing. TTC's stopped-clock setting is a different variable and does not
establish that exception. Neither case is presently a preserving dust witness.

Mario's retained floor pointer is also not an independent permanent floor.
The geometry refresh calls `find_floor` with `&m->floor`; the query resets that
output pointer before searching. Local Pedro-branch preservation of a floor
reference must therefore be connected to the following geometry refresh.

## TTC candidates

The generated level and macro descriptors contain 79 entries in the surface
object list, grouped below. Membership in that list is a conservative candidate
filter, not a guarantee that every variant publishes collision.

| Behavior family | Descriptor count | Candidate significance |
| --- | ---: | --- |
| Thwomp | 1 | Existing collision object; non-holdable script |
| TTC rotating solid | 8 | Cubes/prisms; non-holdable scripts |
| TTC pendulum | 4 | Existing collision objects; non-holdable scripts |
| TTC treadmill | 7 | Existing collision objects; non-holdable scripts |
| TTC moving bar | 12 | Existing collision objects; non-holdable scripts |
| TTC cog | 8 | Existing collision objects; non-holdable scripts |
| TTC pit block | 1 | Existing collision object; non-holdable script |
| TTC elevator | 2 | Existing collision objects; non-holdable scripts |
| TTC 2D rotator | 8 | Two hands plus six decorative gears |
| TTC spinner | 14 | Existing collision objects; non-holdable scripts |
| Exclamation box | 13 | Item boxes, distinct from cork boxes |
| Blue coin switch | 1 | Existing collision object; non-holdable script |

None of these twelve families' immediate script flag writes sets the holdable
bit. This is not proof that they cannot be cloned: non-holdable objects are
precisely the targets for which behavior replacement matters. A reachable
allocation/lifetime sequence putting a particular platform in the held slot
has not been demonstrated or excluded.

The TTC descriptor scripts that set the holdable bit belong to the Heave-Ho
and two Bob-ombs. Source inspection finds interaction hitboxes, not standing
platform triangle models, for these normal behaviors. Their complete native
execution and spawn closure are not a new exclusion theorem here.

There are no `bhvBreakableBox` or `bhvBreakableBoxSmall` descriptors: stock TTC
does not supply either cork-box family. Its thirteen exclamation-box presets
select two walking 1-Ups, five ten-coin contents, and six three-coin contents,
with no descriptor parameter overrides. This is an initial descriptor census,
not an exhaustive proof of all future runtime object allocations.

## Checked formal results

- [CloneFloorExecution.v](../../proofs/CloneFloorExecution.v) compiled with
  whole-function empty-list and published-triangle floor searches, the entire
  `BREAK` handler, and its real indirect interpreter-loop dispatch and exit.
  The published-triangle result assumes readable node/triangle fields and an
  output-height cell. It returns the supplied cog-shaped surface at height
  -2088 without any parent-object field premise. It is not a clone/loader
  reachability proof.
- [CloneFloorRefresh.v](../../proofs/CloneFloorRefresh.v) records the generated
  non-holdable replacement branch and caller ordering, executes the actual
  floor-pointer reset statement, and executes the global-Time-Stop branch of
  `clear_dynamic_surfaces`. The pointer-reset theorem is a statement execution,
  not a complete Mario update.
- [TTCCloneCandidates.v](../../proofs/TTCCloneCandidates.v) compiled the exact
  US/JP descriptor, immediate holdable-flag, cork-box absence and box-parameter
  census. Initial script flags are not a runtime flag invariant.
- [CloneFloorPartition.v](../../proofs/CloneFloorPartition.v) executes the
  complete original `clear_spatial_partition` function. An induction over its
  256-cell loop constructs all 768 pointer stores and proves every list head
  null. The permissions cover the actual 6,144-byte partition; generated
  layout receipts check the eight-byte nodes and 24-byte cells. The composed
  theorem `generated_cleared_partition_has_no_floor_us_jp` derives the empty
  head from those stores and executes `find_floor_from_list`, returning null
  with unchanged memory for any query of such a head. It assumes neither an
  empty initial list nor a helper's execution. This concerns one cleared
  partition before new collision is published, not static floors or later
  terrain updates.
- [CloneFloorMechanism.v](../../proofs/CloneFloorMechanism.v) combines these
  results in `checked_ttc_cog_clone_floor_frontier_us_jp`. The active
  [MainTheorem.v](../../proofs/MainTheorem.v) consumes that frontier as part of
  `checked_ttc_cog_local_mechanism_us_jp`.

The complete Pedro build passes. The new results establish the floor-list
mechanism and sharpen the TTC candidate inventory. They do not establish a
preserving cog dust event or universally exclude every cloning setup.

## Remaining gameplay obligations

To use a clone as a dust-enabling floor, a witness must establish all of these:

1. A reachable allocation/lifetime sequence puts the intended TTC object in
   Mario's held slot, with the actual runtime flags and release behavior.
2. Script installation and the relevant subsequent updates execute. The
   non-holdable installation crosses `segmented_to_virtual`; its existing
   N64 address-refinement obligation remains open.
3. At Mario's query, a suitable triangle is still published at the needed
   coordinates. The full frame must account for clearing, terrain updates,
   list membership and surface-pool reuse. The new clear theorem must be
   instantiated with that frame's actual partition and permissions.
4. The selected floor lets the proposed action run while Mario and the cogs
   preserve the Pedro state. A floor alone does not establish a dust request,
   particle acceptance or the ordered RNG draws.

The initial script census cannot replace the runtime invariants in item 1.
The source ordering receipt cannot replace the executed frame in item 3.
The present result therefore rules out treating a teleported object's position
or interaction hitbox as an automatic new floor; it does not prove that every
timing-dependent cloning strategy is impossible.

## Verification and interrupted-command diagnosis

The verification command is:

```sh
COQ_JOBS=2 bash Pedro-Coq/pipeline/build.sh proofs COQEXTRAFLAGS=-time
```

Run it in Ubuntu's configured `sm64-item-proof` login environment, with the
working directory at the repository root. The final build log is
`Pedro-Coq/build/clone-floor-build.log` (ignored). Validation commands and file
hashes are retained in the
[cloning validation receipt](../../inputs/cog-cloning-validation.json).

During development, an expanded 768-store proof and a symbolic layout
calculation exceeded the 3 GiB compiler memory cap. The checked proof uses a
small loop induction and explicit layout rewrites instead. Separate elevated
tool launches timed out in automatic permission review; a normal-permission
launch returned `Wsl/Service/E_ACCESSDENIED` without starting Coq. Even a
read-only WSL process check encountered that review timeout. After the user
authorized another elevated attempt, WSL access resumed and the build
completed. The apparent long wait was not evidence of a long Coq computation.

The motivating [Ukikipedia cloning article](https://ukikipedia.net/wiki/Cloning)
is secondary context. The generated US/JP functions, not the article's broad
description of object collision, determine the claims above.
