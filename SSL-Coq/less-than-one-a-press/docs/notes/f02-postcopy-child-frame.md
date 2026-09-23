# F02: the child-copy tail after Mario's ordinary copy

This batch closes one specific late-writer candidate. Once particle spawning
has returned a child in a different valid object slot, copying Mario's
position and angles into that child cannot change Mario's movement,
collision or display records. This is a conditional execution proof for both
generated US and JP programs, not a claim that all spawning or the whole
remaining frame is harmless. The F02 family remains open.

## What was missing

The earlier callback inventory found nine direct receiver-taking position
writers and identified the particle/debug copy destinations in the source.
It also proved that one store into a distinct object slot cannot change
Mario's raw position. It did not connect the complete position-and-angle
copy, its actual callees, or the particle caller's returned pointer to that
memory argument. The new result supplies that connection.

## What the code does, and what the proof checks

In `object_list_processor.c`, `bhv_mario_update` copies MarioState into Mario's
Object and then processes particle requests. The taken `spawn_particle`
branch sets its active-particle flag, calls `spawn_object_at_origin`, puts
the returned pointer in `particle`, reloads `gCurrentObject`, and calls
`obj_copy_pos_and_angle(particle, gCurrentObject)`. The reloaded current
object supplies the source, not the destination.

The new modules use the generated bodies and the selected program's actual
function resolution. They check both `obj_copy_pos` and `obj_copy_angle`,
their parameter bindings, all nine stores, and the wrapper's two actual
calls. Their writes stay between bytes 160 and 219 of the destination
Object. Every disjoint memory load is preserved, including another slot
within the same Object-pool allocation. A separate MarioState allocation
is preserved too. There are no local allocations or unchecked outside calls
inside these copy helpers.

The particle execution theorem then takes the real generated
allocation-and-copy segment apart at the allocator's return. The returned
pointer is the one carried into the copy destination. If it identifies a
valid child slot distinct from Mario, the remaining tail preserves Mario's
whole Object slot and separate State. It does not require the source object
to remain Mario: changing that source does not redirect the destination.

## Exact scope

The proof starts its preservation claim **after allocation returns**. The
earlier flag write, allocation and initialization effects are not framed by
this theorem. It does not establish that the returned child is fresh,
that Mario survives allocation or slot reuse, or that all other post-copy
callbacks preserve the relevant records. Successful defined execution and
the stated valid, distinct slots remain explicit conditions.

Consequently, this tail cannot create the useful disagreement from records
that agree at its entry under those conditions. It can preserve a
disagreement supplied earlier; it does not exclude movement while display
survives in a different phase. No controller search, new clean Ink witness,
or whole-route impossibility claim is added here. Atlas percentages remain
unchanged subjective estimates.

## Checked interfaces

- [Area1PostCopyChildSource.v](../../proofs/Area1PostCopyChildSource.v): selected US/JP helper resolution.
- [Area1PostCopyChildFrame.v](../../proofs/Area1PostCopyChildFrame.v): actual leaf executions and their write bounds.
- [Area1PostCopyChildCall.v](../../proofs/Area1PostCopyChildCall.v): complete wrapper and post-allocation particle tail.
- [Area1PostCopyParticleExecution.v](../../proofs/Area1PostCopyParticleExecution.v): `pcp_actual_spawn_segment_has_framed_copy_tail`, splitting the generated allocation-and-copy execution at its real return.

The package is consumed by the existing Rank-5 boundary and exported as
`MainTheorem.current_f02_postcopy_child_boundary`. The next bounded target
is the allocator/initialization segment: derive its effects and the returned
child's separation from Mario, then extend to the remaining reached
callbacks. That is the remaining work, rather than assuming every late call
preserves Mario.

## Validation

The 23 September 2026 selected discipline audit passed: 584 registered
source files, MainTheorem and the requested dependencies, no proof holes,
clean links and 414 of 508 proof modules in the main import closure. The
updated Rank-5 boundary, complete copy frame and generated particle-segment
cut each use seven allowed Coq/CompCert foundations. No new axiom or assumed
copy-callee contract was added. This audit does not discharge the explicit
allocation, receiver or gameplay conditions above.

Local audit record: `build/audit/20260923-134418-4fo4w186`.
