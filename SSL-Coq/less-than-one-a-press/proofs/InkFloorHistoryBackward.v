(** A sharper backward boundary, not a clean reachability closure. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorHistorySource
  InkFloorHistoryExecution InkFloorHistoryCall InkFloorHistoryQuery
  InkBackwardSource InkBackwardExecution ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition InkQuarterMissingFloorCut : Prop :=
  forall version ge e le m t le' m' out,
  ocn_exec ge e le m (ifh_quarter_tail version) t le' m' out ->
  exists floor_value,
    eval_expr ge e le m (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr))) floor_value /\
    ((ocn_test_value ge e (PTree.set IFH._t'21 floor_value le) m ifh_null_guard true /\
      t = E0 /\ m' = m /\ out = ifh_returned 2) \/
     (ocn_test_value ge e (PTree.set IFH._t'21 floor_value le) m ifh_null_guard false /\
      exists water_le water_m pre rest,
        t = pre ++ rest /\
        ocn_exec ge e (PTree.set IFH._t'21 floor_value le) m
          (ifh_water version) pre water_le water_m Out_normal /\
        ocn_exec ge e water_le water_m (ifh_post_water version) rest le' m' out)).

Theorem ifh_missing_floor_returns_or_reaches_actual_water_tail : InkQuarterMissingFloorCut.
Proof.
  unfold InkQuarterMissingFloorCut.
  intros version ge e le m t le' m' out Hrun.
  destruct (ifh_quarter_source_cuts version)
    as (_ & _ & _ & _ & Htail & Hmissing & HwaterNormal & _).
  assert (ifh_post_water version = Ssequence (ifh_vertical version)
    (Ssequence (ifh_floor_ceil version) (ifh_accept version))) as Hpost
    by (destruct version; reflexivity).
  rewrite Htail, Hmissing, <- Hpost in Hrun.
  apply ifh_sequence_reassociate in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Sset IFH._t'21 (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr))))
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & rest & Htrace & Hset & Hrest).
  inversion Hset; subst; clear Hset.
  match goal with Hr : eval_expr _ _ _ _ (Evar IFH._floor _) ?value |- _ =>
    exists value; split; [exact Hr|] end.
  destruct (ifh_return_gate _ _ _ _ _ _ _ _ _ _ _ Hrest) as [Hblocked|Hpassed].
  - destruct Hblocked as (Htest & -> & -> & -> & ->).
    left. repeat apply conj; try assumption; reflexivity.
  - destruct Hpassed as [Htest Hfollowing].
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HwaterNormal Hfollowing)
      as (water_le & water_m & before & after & HwaterTrace & Hwater & HpostRun).
    right. split; [exact Htest|]. exists water_le, water_m, before, after.
    repeat apply conj; assumption.
Qed.

Definition InkFloorHistoryCheckedBoundary : Prop :=
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version))
      IFH._perform_ground_quarter_step = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ifh_quarter_body version))) /\
  InkGroundQuarterCallHistoryCut /\
  InkQuarterMissingFloorCut /\
  InkHighFloorGapQuarterCut /\
  InkGeometryFloorQueryHistoryCut /\
  InkPrimaryFloorQueryHeightCut.

Theorem ifh_floor_history_boundary_checked : InkFloorHistoryCheckedBoundary.
Proof.
  split; [exact ifh_selected_quarter_body_resolves|].
  split; [exact ifh_completed_quarter_call_reaches_queried_floor_cut|].
  split; [exact ifh_missing_floor_returns_or_reaches_actual_water_tail|].
  split; [exact ifh_high_gap_requires_ceiling_block_or_leaves_ground|].
  split; [exact ifh_completed_geometry_call_reaches_primary_floor_query|].
  exact ifh_primary_floor_query_uses_movement_y_and_stores_result.
Qed.
