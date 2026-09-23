# F02: following allocation before the particle copy

This follow-up replaces part of the vague “allocation might do something”
gap with proofs about the actual US and JP code. It does not establish that
all allocation or the remaining frame preserves Mario. The useful Ink
combination and clean reachability remain open.

“Child” means a separate object spawned by another object, such as a dust
particle spawned by Mario. It does not mean a second Mario. Mario occupies
one Object slot; the particle needs another. Their slots share the game's
Object pool, while MarioState is separate storage. Copying Mario's position
into a particle is how the effect starts in the right place.

## What is now proved

A completed nonempty `allocate_object` call now returns exactly the valid
pool slot named by its entry free-list head. The proof follows the actual
`try_allocate_object` return through the allocator's branch and full
initializer to its final return. The nonempty branch skips eviction. The
graph calls cannot redirect the saved local pointer; this alone makes no
claim that they preserve memory or establish live ownership.

There is also a concrete conditional freshness test. If that entry slot's
active flag is zero and Mario's flag is nonzero in the same entry memory,
they cannot be the same slot. The proof derives the distinctness from those
loads and carries it through the complete allocator call. It does not assume
distinctness under the name “child.” Establishing
the live free/active partition at each relevant call is still necessary.

The complete `allocate_object` initializer now preserves every other slot
of the same Object pool, as well as separate MarioState storage. Its writes
fit inside the selected 608-byte slot. This covers the 80-field clearing
loop, all subsequent initialization writes, and the actual `mtxf_identity`
call and both matrix loops. A proved address-and-loop checker checks the
generated US/JP bodies; it does not replace them with a hand-written game
model. The proof resolves and executes the real matrix helper without an
assumed memory contract. In the nonempty allocator, the initializer's slot
is the original free-list head and the eventual return value. Preservation
begins at initialization, after the earlier list and graph operations.

Finally, the real `find_unimportant_object` call preserves all memory. This
closes one allocator callback. The source takes the first object in list
12; it does not search by the object's unimportant flag. If both allocation
and that lookup fail, the allocator enters a spin with no completed defined
execution. This does not prove the full pool can never be reached.

## What these results do not settle

The valid-slot and entry flag conditions are explicit. We have not proved
that every relevant gameplay allocation reaches the call with an inactive
free-list head and an active Mario slot, or that earlier graph and list
operations preserve Mario. The new bounds protect the initialization phase;
they do not silently extend its starting point to the whole allocation.

The remaining allocator work is specific: prove the list splice and graph
maintenance effects; establish live free/active and list-12 ownership;
handle the full-pool eviction and unloading branch; and connect the returned
slot through `create_object`, `spawn_object_at_origin` and their
initialization calls to the particle caller. The nonempty allocator result
alone does not prove that whole chain or the particle child's lifetime.
Afterward, the remaining reached object callbacks and scheduler interval
through collision still need their own execution connection.

No whole-list integrity, future preservation, or universal callback safety
is granted here. There is no new gameplay witness and no route closure.
The atlas's subjective counterexample estimates are unchanged.

## Checked interfaces

- [Area1AllocationSource.v](../../proofs/Area1AllocationSource.v) resolves the actual selected allocator and helper definitions.
- [Area1AllocationChoice.v](../../proofs/Area1AllocationChoice.v): `pac_try_call_result_origin` and `pac_free_head_flags_exclude_mario`.
- [Area1AllocationBlockFrame.v](../../proofs/Area1AllocationBlockFrame.v) proves the write and pointer-arithmetic frame used by initialization.
- [Area1AllocationInitialization.v](../../proofs/Area1AllocationInitialization.v): `pai_actual_initializer_frames_state`, including the real matrix helper.
- [Area1AllocationCallback.v](../../proofs/Area1AllocationCallback.v): the actual allocator cut and read-only eviction lookup.
- [Area1SlotExpressions.v](../../proofs/Area1SlotExpressions.v) and [Area1SlotWriteCheck.v](../../proofs/Area1SlotWriteCheck.v): the address and bounded-loop checker, with its execution soundness proof.
- [Area1AllocationSlotFrame.v](../../proofs/Area1AllocationSlotFrame.v): `asf_actual_initializer_frames_other_slots`, checking all initialization writes within the selected slot.
- [Area1AllocationReturn.v](../../proofs/Area1AllocationReturn.v): `asr_nonempty_allocator_body_connection`, `asr_nonempty_allocate_call_returns_head` and `asr_nonempty_allocation_excludes_active_mario`.

The existing Rank-5 boundary consumes this package. It is also exported as
`MainTheorem.current_f02_allocation_boundary` and the stronger
`MainTheorem.current_f02_allocation_slot_boundary`. The earlier
[child-copy result](f02-postcopy-child-frame.md) retains its own scope.

## Validation

The 23 September 2026 selected discipline audit passed: 593 registered
sources, no proof holes or link problems, and 423 of 517 proof modules in
the MainTheorem import closure. All five checked boundaries use seven
allowed Coq/CompCert foundations, with no new axioms. The audit checks the
Rank-5 boundary, the combined allocator package, the same-pool initializer
frame, the actual nonempty execution connection and the entry-flag
separation result. It is a selected dependency build, not a full rebuild
of every standalone module. Live ownership and the other unproved effects
above remain explicit obligations.

Local audit record: `build/audit/20260923-162620-x415fswp`.
