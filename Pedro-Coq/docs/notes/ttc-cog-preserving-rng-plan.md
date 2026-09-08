# Preserving RNG execution work

Scope: the pinned US and JP programs. The requested theorem must exhibit
successive actual game updates and two controller continuations whose ordered
RNG calls differ while the cog gap and Mario's in-spot state remain suitable.
The current capstone does not yet assert that theorem.

## Execution chain

1. Execute the complete moving-action dispatcher around the existing slide
   body. Include common cancellation checks, the default-floor quicksand
   update, action selection, and downstream particle clearing. Carry the
   intermediate memories explicitly: on a default floor with depth zero,
   quicksand processing writes 1.1 and then zero before calling the action.
2. Replace the two remaining slide helper premises (`update_sliding` and
   `perform_ground_step`) with their actual executions. Ground-step work must
   cover attempted positions, selected floor/ceiling, wall resolution, the
   early quarter-step return, terrain sound, and graphics-vector writes.
   Sliding additionally reaches the declared external `sqrtf`; its existing
   instruction receipt does not supply an external semantic contract.
3. Execute slide-kick entry/bounce and the following backward-ground-knockback
   action from successive compatible memories. A slide-to-knockback action
   transition alone does not establish a preserving second action update.
4. Execute Mario particle dispatch, accepted dust allocation and the full
   Mist/Puff command/list paths. The existing symbolic-pointer obstruction in
   `segmented_to_virtual` requires a proved N64 address refinement. Existing
   per-call execution premises cannot substitute for that refinement.
5. Compose the other object, platform and camera updates in their real order;
   account for every RNG draw and both cogs' angle/timer changes. Instantiate
   a legal entry state and compare two preserving controller continuations.

## Results of this pass

The first step is connected directly to the current slide result in
[`CogSlideDispatcher.v`](../../proofs/CogSlideDispatcher.v), which replaces
the earlier two-helper caller as the action result consumed by
[`MainTheorem.v`](../../proofs/MainTheorem.v). The same two movement-helper
execution/preservation premises remain, but neither dispatcher-prefix callee
is assumed to execute. The resulting complete dispatcher returns zero,
retains particle mask 3 (dust plus vertical stars), selects action 132194
(backward ground knockback), and preserves the original five-field anchor:
position X/Y/Z, stored floor pointer, and stored floor height.

[`CogMovingDispatcher.v`](../../proofs/CogMovingDispatcher.v) executes the
common cancellation helper and default-floor quicksand helper for both real
action cases. Its entry image specifies Y = -2088, water level -11000,
health 2176, input 4, floor type zero and quicksand depth zero. It constructs
the two quicksand stores from writable access, proves their frame property,
and checks the health/depth offsets against both generated layouts. The
integrated caller carries these stores explicitly, with its action-side
memory images after them. These conditions are not a reachable-state witness.

The address obligation is now more than a failed expression calculation.
[`DustAllocationBoundary.v`](../../proofs/DustAllocationBoundary.v) proves
that the complete generated `segmented_to_virtual` call cannot execute from
a symbolic `Vptr`, and follows the real first call of `spawn_object_at_origin`
to prove that the allocator cannot execute from a symbolic behavior pointer
when its segmented-function symbol has the actual generated binding. This
holds before `create_object`, independently of the pool contents. The active
particle frontier consumes this full-call obstruction.

Consequently the existing positive spawn caller's allocation premise cannot
be instantiated under those bindings in standard Clight. It is not simply an
unproved true premise there. This does **not** establish retail dust
impossibility: the N64 runs numeric address operations that this symbolic
Clight model does not represent. A proved address-semantics connection is
required before composing a positive allocation proof. The generated game
code has not been changed.

The full preserving RNG theorem remains open. Steps 2–5, including the
successive knockback body, actual particle acceptance, all ordered draws,
both cogs and legal entry, are still necessary. No new gameplay replay or
positive in-spot RNG witness is claimed by this pass.

## Validation

Use the configured Ubuntu pipeline with a 3 GiB process limit and two build
jobs. Inspect log progress and process completion promptly. Run the Pedro
no-hole/source-coverage/assumption checks and the separate repository
proof-discipline audit. A clean build establishes the stated local theorems,
not a reachable or repeatable RNG witness.

The full Pedro build, no-hole check, authenticated coverage of 81 pinned
RNG-bearing files and 82 generated units, and root discipline audit passed.
The strengthened active capstone and the integrated dispatcher retain the
same six standard Coq/CompCert assumption names as the baseline. The allocator
obstruction was also checked separately. See the
[validation receipt](../../inputs/cog-preserving-validation.json) for commands,
file hashes and the precise scope of this result.
