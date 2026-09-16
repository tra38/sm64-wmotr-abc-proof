# Which Fine Print results belong with the proofs?

The 16 September 2026 review compares the site's 50 open-ledger entries
with its 16 existing result cards. Eight more claims deserve their own
cards in "01 / WE DO HAVE PROOFS": six local execution results and two
explicitly limited model results. These are existing theorems made easier
to find, not eight new proofs or eight closed routes. The open entries stay
in place and link to the completed parts.

## The eight promoted claims

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
selected pipeline audit passed at `build/audit/20260916-124958-uh_niex7/`:
577 registered sources, successful build, proof-hole/link checks and
integration, and only allowed foundations (nine for the Ink boundary,
seven for the coin-star boundary and four for the stock Amp model).
No Coq definition, theorem, axiom or generated game source was changed by
this review.
