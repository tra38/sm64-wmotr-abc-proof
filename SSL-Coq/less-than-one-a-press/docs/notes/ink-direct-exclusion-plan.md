# Ink: what a direct exclusion would need

This is a 3 October 2026 proof review and proposed next batch. No new Coq
theorem or gameplay search is claimed. Rank 1 remains open at its subjective
1–2% estimate.

## Is the proposed argument right?

Yes, if it covers the positions used at each check and the interval between
them. The stock warp and a high top cannot both use one ordinary position.
But the collision check happens first; Mario's action, copies and final
platform query happen later. A useful separation can be between two records
or between two times. Showing only that the warp's visible shape does not
overlap the top's visible shape would miss that distinction.

The decisive goal is that no allowed upper-warp continuation can leave a useful
top address installed for the first Area-2 platform apply. An exclusion can
show that the final check always clears it, provided that check actually runs
and nothing installs another useful address afterward. If a check can be
skipped, an earlier retained address needs its own argument. If an address
survives, inactivity alone does not reject it: the actual installer has no
active-owner test. This concerns the named top-based Ink installation, not
every other possible route to the two stars.

## There is more than one working supplied split

All these checked supplied controls use X=-2200 and Z=-1024. They are
conditional installations, not controller-reachable gap producers.

| Movement Y before the update | Collision Y | Display Y | What supplies the useful query |
| ---: | ---: | ---: | --- |
| 768 | 768 | 1938.8648681640625 | Failed first lookup copies the raised display into State. |
| 1861 | 768 | 1938.8648681640625 | The first lookup already finds the top. |
| 1861 | 768 | 768 | The first lookup already finds the top; no raised display or negative depth is needed. |

The last example starts with a 1,093-unit movement/collision separation.
The disappeared action subsequently aligns movement with the selected floor;
the later ordinary copy raises collision before the final platform query.
The 78-unit lookup allowance is not the four-unit capture tolerance.
Consequently, 1,170.864868 units is the size of one proposed display retry,
not a universal minimum or a complete definition of a useful gap. Other
positions and top phases must be checked against their own contact and
selection conditions. See the [three exact controls](rank1-concrete-ink-backward.md).

## What Coq already settles

| Checked result | Its limit |
| --- | --- |
| `PyramidTopPU.one_coordinate_cannot_contact_warp_and_capture_live_top`: the modeled warp-contact Y is 608..818, while capture of a modeled floor at least 1281 requires Y above 1277. | Integer stock geometry and an explicit floor-height premise. This is not yet every live US/JP hitbox, transformed surface or phase. |
| `Area1CachedFloorSelectionClosure.upper_warp_selected_floor_height_at_most_896`: a modeled floor selected from that same contact sample is at most 896. | Its selected-floor relation and matching sample are explicit premises. The working high-State variant does not use that same low sample. |
| `Rank1PlatformInstallation.r1o_final_query_connects_raw_position_to_owner`: the real generated US/JP body reads raw X/Y/Z, calls the real floor function, tests saved raw Y and installs or clears both references. | Completed body with ordinary storage/read conditions. It consumes the actual returned memory; it does not derive every live list, caller or later lifetime. |
| `InkPlatformDistance.ipdist_low_samples_cannot_depart`: raw Y=768 cannot retain the checked timer-131 top height 1938.8648681640625. | It does not show that the later raw Y must remain 768. |
| `InkPlatformMovement.ipm_collision_and_display_survive_complete_platform_phase`: the complete platform dispatcher preserves raw and display positions in the normal Object pool. | It can move State. An earlier low raw record and usable support still need explanation. |
| `InkRawCopyHeight.irc_completed_copy_has_exact_height_cut`: the real raw-Y store makes movement and collision Y agree at that cut. Ordinary display-copy and nonnegative ground-refresh/sinking results also remove their named upward display gaps. | The raw-copy cut is inside the call. Later calls need their own preservation; the sinking theorem has explicit nonnegative-depth conditions. |
| The completed display retry and real floor-call return are connected in `InkRetryCompletion`, `InkRetryQuery` and `InkRetryCallCompletion`. | The retry transports an existing gap. It does not construct it, automatically land Mario or prove every live top choice. |

The acceptance-tail proof also shows that its action setter preserves the
three position records. That tail neither invents nor removes the incoming
split. None of these results requires every position to agree throughout
gameplay. The final-query result's recorded passing audit is
`build/audit/20260926-210704-9ushw0ao`; this review does not rerun or expand it.

## The next bounded proof plan

1. **Make the geometric obstruction operational.** Connect the actual warp
   contact tests and live top floor bounds at the relevant phases to the
   existing binary32 final-query guard. Start with the checked timer-131
   geometry, then cover the other phases in which the upper warp can be
   accepted. Completion means a generated-code exclusion for a specified
   contact/capture region, with its phase and live-surface conditions visible.
   Merely comparing object origins or rendering bounds does not complete it.
2. **Trace the two samples backward.** Fix the collision-contact sample, the
   pre-action geometry sample, the accepted-warp return and the final raw
   query. Follow the actual receivers and last position writers between them.
   In particular, distinguish an already high State with low raw collision
   from a failed lookup using a raised display. Reuse the completed platform,
   copy, retry and acceptance results. Track X/Z, signed-16 query casts and
   controller history as well as Y. Completion means either a concrete
   allowed writer producing the useful combination or an exclusion of each
   reached branch in this specified interval. Do not assume sample equality,
   harmless calls or a catch-all coverage predicate.
3. **Close the retained-address escape.** Establish that the final platform
   update runs and that no later writer supplies a useful address before the
   first Area-2 apply. A proved null result through that boundary would avoid
   having to classify the contents of every unusable old slot. Otherwise,
   analyze the actual surviving owner, unloading/reuse and first apply.
4. **Connect any remaining predecessor to gameplay.** For every producer
   surviving step 2, work back to its earlier support, action, position copies
   and permitted controller edges. A patched installer or failed finite
   Scattershot menu cannot settle this connection. A successful route needs
   an uninterrupted controller replay from the accepted start; an impossibility
   claim needs an exhaustive, proved classification for its stated scope.

The first three steps can exclude named intervals and installer branches
without reconstructing the star suffix or all Eyerok gameplay. The final
all-history closure still requires the fourth connection wherever a useful
producer remains. The 146 saved failures motivate the contact-order question;
they do not cover all its answers. No further Scattershot run is started here.
