# F02: following allocation before the child copy

This follow-up replaces part of the vague “allocation might do something”
gap with proofs about the actual US and JP code. It does not establish that
all allocation or the remaining frame preserves Mario. The useful Ink
combination and clean reachability remain open.

## What is now proved

A completed `try_allocate_object` call with a non-null pointer at the head
of its free list returns exactly that entry pointer. The later graph calls
cannot redirect the saved local pointer. This is a return-value theorem:
it makes no claim that those graph calls preserve memory or that the
returned slot is still live afterward.

There is also a concrete conditional freshness test. If that entry slot's
active flag is zero and Mario's flag is nonzero in the same entry memory,
they cannot be the same slot. The proof derives the distinctness from those
loads. It does not assume distinctness under the name “child.” Establishing
the live free/active partition at each relevant call is still necessary.

The complete `allocate_object` initializer preserves every memory block
separate from the child's block. This includes its 80-field clearing loop,
all subsequent initialization writes, and the actual `mtxf_identity` call
and both matrix loops. The proof resolves the real helper in the selected
program, binds its actual argument, and accounts for function entry and
return. It does not assume a matrix-call frame. A separate execution theorem
extracts this initialization point from a completed real allocator body.
Preservation begins at that point, after list repair or eviction.

Finally, the real `find_unimportant_object` call preserves all memory. This
closes one allocator callback. The source takes the first object in list
12; it does not search by the object's unimportant flag. If both allocation
and that lookup fail, the allocator enters a spin with no completed defined
execution. This does not prove the full pool can never be reached.

## What these results do not settle

MarioState has separate storage, but Mario's Object and a child usually
occupy different slots of the same Object pool. The new initialization
frame proves the former separation, not the latter. Byte bounds for all
initialization writes within the child's slot are still required to protect
Mario's collision and display records. The previously proved child-copy
tail does have the stronger distinct-slot frame.

The remaining allocator work is specific: prove the list splice and graph
maintenance effects; establish live free/active and list-12 ownership;
handle eviction and unloading; and connect the returned slot through
`allocate_object`, `create_object`, `spawn_object_at_origin` and their
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

The existing Rank-5 boundary consumes this package. It is also exported as
`MainTheorem.current_f02_allocation_boundary`. The earlier
[child-copy result](f02-postcopy-child-frame.md) retains its own scope.

## Validation

The targeted build and the 23 September 2026 selected discipline audit
passed: 589 registered sources, no proof holes or link problems, and 419 of
513 proof modules in the MainTheorem import closure. All four checked
boundaries use seven allowed Coq/CompCert foundations, with no new axioms.
The audit covers the updated Rank-5 boundary, conditional freshness, the
complete initializer frame, and the combined allocator package. It does
not discharge live ownership or same-pool bounds.

Local audit record: `build/audit/20260923-151228-as5j2q66`.
