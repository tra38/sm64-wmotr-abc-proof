# Which Fine Print results belong with the proofs?

The 20 September 2026 review checked all 50 ledger entries and six
assumption recommendations. The 23 September F02 batch adds a new proved
conditional child-copy result and a follow-up allocator result to
"01 / WE DO HAVE PROOFS", taking it to 29 result cards. The other sections retain the conditions and gameplay
questions outside those results, with links to the completed parts. No
whole-route verdict changes.

## F02: a new local execution proof

The [child-copy result](f02-postcopy-child-frame.md) belongs in Section 01:
the actual US/JP position-and-angle copy and the particle tail after
allocation preserve Mario's separate State and distinct valid Object slot.
The generated caller is connected to its returned destination. Section 03
and the F02 workboard still retain allocation effects, child freshness,
other callbacks and the rest of the post-copy interval. This is new proof
work, unlike simply promoting an older result's presentation.

The [allocator follow-up](f02-allocation-boundary.md) also belongs in Section
01, with its limits visible. The stronger result now follows the free-list
head through the complete nonempty allocator call, carries the explicit
flag-based separation test to that return, and bounds every initializer
write within the selected valid slot. Other shared-pool slots and separate
State storage are protected during initialization, including the real matrix
helper. The read-only full-pool lookup remains proved. Live ownership,
earlier graph/list effects, unloading, the complete spawn chain and the
remaining callbacks stay in Section 03 and the workboard. This strengthens
the existing card; it does not add a route closure. “Child” means a spawned
particle or effect, not a second Mario.

## The 20 September promotion

[InkStockSeedConditional.v](../../proofs/InkStockSeedConditional.v) proves
`isc_useful_negative_seed_requires_physical_a` and its no-A corollary.
From finite, nonnegative depth, a finite connected history satisfying the
explicit stock writer, landing, action and input conditions cannot finish
negative without a physical A press. The generated US/JP landing execution,
late long-jump restriction and first-action argument are now composed.
Temporary negatives immediately clamped within a writer are not useful
endpoints of this theorem.

The complete conditional implication moves into Section 01. Section 02
keeps its substantive applicability conditions: every relevant completed
writer must fit the classification, the stock landing gates must hold, and
legitimate action edges must have physical controller witnesses. Section 03
keeps the actual no-A seed search, including other courses. Neither a source
inventory nor the existence of the conditional theorem proves that every
gameplay history satisfies its conditions.

The course-entry reset, missing/ownerless support clearing, complete platform
frame, square-root binding, repeated triplet exclusion and eleven-descent
hold exclusion already have Section 01 cards. Their larger gameplay claims
are not new promotions. Finite geometry and recorded fixtures keep their
explicitly limited badges; bounded trials do not become universal proofs.

## Eight earlier promotions, still valid at their stated scope

| Claim | What is proved | What is still outside it |
| --- | --- | --- |
| The Ink retry uses the displayed coordinates | [InkRetryCallCompletion.v](../../proofs/InkRetryCallCompletion.v), `ircq_retry_finishes_at_the_copied_display`: the reached US/JP retry copies all three coordinates, calls the real floor routine with them and retains them after its return and the height store. | Creating the first miss, selecting the useful live floor and executing the warp. Ordinary storage and a completed retry are explicit conditions. |
| Automatic dialog skips interaction handlers | [InkDialogInteractionGate.v](../../proofs/InkDialogInteractionGate.v), `idg_automatic_dialog_skips_handler_loop`: reading that action at the real gate skips the entire handler loop, including a cached warp contact. | Reaching the gate and a useful contact after dialog release. This is a local gate transition. |
| The warp's stopping copy uses cached floor height | [InkWarpStop.v](../../proofs/InkWarpStop.v), `iws_stop_copies_floor_without_horizontal_departure`: at the completed copy, actual X/Z equal their entry values, while actual Y and displayed Y equal the entry floor height. | The remaining angle call, later sinking and the gameplay predecessor. The theorem exposes a checkpoint inside a completed defined helper call. |
| An ownerless floor clears the remembered platform | [InkPlatformDeparture.v](../../proofs/InkPlatformDeparture.v), `ipd_backward_platform_departure_checked`: the reached ownerless branch clears both pointers; a complete null-platform dispatcher changes no memory. A later displacement needs a replacement pointer. | The earlier live floor choice and every possible intervening replacement. Neither is assumed impossible. |
| Attached pole pickup chooses the standing dance | [Area2Rank9AStarExecution.v](../../proofs/Area2Rank9AStarExecution.v): `rank9a_every_attached_pole_pose_selects_standing_dance`, the actual selector execution, the initializer and the separate height-snap fragment. | Reaching the no-exit selector, preserving its choice through the remaining caller and justifying the cached floor. These pieces are not a completed pickup-to-dance execution. |
| Rising Mario fails this ledge check | The same module's `rank9a_rising_ledge_check_returns_without_writes`: the whole entered function body returns false with no memory write or outside call when vertical speed is positive. | A later check after Mario starts descending. The speed is tested at the check, not necessarily at star pickup. |
| Pauses do not raise the low coin-flight ceiling | [Area2Rank9ACoinFlight.v](../../proofs/Area2Rank9ACoinFlight.v), `rank9cf_coin_flight_boundary_checked`: binary32 bounds cover all permitted random launches and arbitrary sequences of the specified movement, pause and lower-support resets. The 2517 attack-ceiling case leaves direct-contact Mario at most 3391, at least 114 short of the proposed home window. | Higher support, renewed jumps, water or other updates outside the stated projection, and actual enemy/coin installation and collection. This is a conditional flight model. |
| The stock Amp-shock model falls back through the opening | [Area2Rank12ObjectImpulse.v](../../proofs/Area2Rank12ObjectImpulse.v), `area2_rank12_shock_composite_closure_holds`: the finite fall reaches Y=3200 on update 21; the checked stock walls and moving-owner corridors miss it, and the height gap fails platform retention. | A connected live execution from an Amp lure, with its actual owners and lists. The theorem combines generated-source checks, geometry and a finite model. Goomba damage is a different case. |

All eight are consumed by existing exported `MainTheorem` boundaries:
`current_ink_backward_execution_boundary`,
`current_rank9a_coin_star_gate_boundary` and
`current_rank12_stock_shock_composite_closure`. The no-jump standing
initializer is separately proved in the imported star-execution module;
the selected-star boundary exports the selector, snap and rising check.

## What should not be promoted as a completed route

The fresh-triplet conditional sequence, local square-root binding,
eleven-descent hold exclusion and platform collision-position frame already
have Section 01 cards. Their broader applicability questions remain open.
The supplied JP Ink success remains a recording plus a finite floor-list
certificate; the hand ride remains an authenticated local controller
primitive with a staged approach. Neither has become a complete live
Clight route. The bounded Goomba searches, supplied coin catch and other
isolated trajectories also remain evidence at their stated scope. The
global start, execution, contact, writer and lifetime connections still
need work. No route estimate changes as a result of this presentation review.

## Verification

The review reads the theorem statements and their explicit conditions,
rather than interpreting an empty proof-hole scan as route closure. The
earlier selected pipeline audit passed at `build/audit/20260916-124958-uh_niex7/`:
577 registered sources, successful build, proof-hole/link checks and
integration, and only allowed foundations (nine for the Ink boundary,
seven for the coin-star boundary and four for the stock Amp model).
The latest seed theorem and its main boundary connection passed the selected
audit at `build/audit/20260916-172120-axj4da7v/`: 580 registered sources,
successful compilation and discipline checks, nine allowed foundations for
the main boundary and seven each for the seed implication and no-A corollary.
This review reuses that checked proof snapshot. No Coq definition, theorem,
axiom or generated game source was changed, and no new proof audit is claimed.
