(** The user-granted 100-coin setup retains the ordinary milestone check.
    Open that complete US/JP helper: its search is read-only and its sole
    memory update is the remembered star count. This is a reached-call frame,
    not a proof of reward placement, collection, or the later dialog history. *)
From Coq Require Import Bool List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Ctypes Events
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import
  us_mario_actions_cutscene jp_mario_actions_cutscene.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardExecution
  InkGroundCallBackward InkBodyResetFrame InkSharedReadings InkCopyCaller
  ObjectContactNecessity ContactConsumerExecution EyerokRank15LiveMovement
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Module ISD := us_mario_actions_cutscene.

Definition isd_body version := match version with
| VersionUS => ISD.f_get_star_collection_dialog
| VersionJP => jp_mario_actions_cutscene.f_get_star_collection_dialog end.

Definition isd_initial := Sset ISD._dialogID (Econst_int (Int.repr 0) tint).
Definition isd_search version := match fn_body (isd_body version) with
| Ssequence _ (Ssequence search _) => search | _ => Sskip end.
Definition isd_current_count := ibr_field ISD._m ISD._MarioState ISD._numStars tshort.
Definition isd_previous_count :=
  ibr_field ISD._m ISD._MarioState ISD._prevNumStarsForDialog tshort.
Definition isd_sync := Ssequence (Sset ISD._t'2 isd_current_count)
  (Sassign isd_previous_count (Etempvar ISD._t'2 tshort)).
Definition isd_return := Sreturn (Some (Etempvar ISD._dialogID tint)).

Lemma isd_source : forall version,
  fn_vars (isd_body version) = [] /\
  fn_params (isd_body version) = [(ISD._m, tptr (Tstruct ISD._MarioState noattr))] /\
  fn_body (isd_body version) = Ssequence isd_initial
    (Ssequence (isd_search version) (Ssequence isd_sync isd_return)) /\
  cce_readonly_keep ISD._m (isd_search version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma isd_selected_count_layout : forall version,
  let ce := prog_comp_env (selected_clight_target version) in
  ibcc_field_ok ce ISD._MarioState ISD._numStars 170 = true /\
  ibcc_field_ok ce ISD._MarioState ISD._prevNumStarsForDialog 184 = true.
Proof.
  intro version. cbn zeta. rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma isd_search_finishes_normally : forall version ge e le m t le' m' out,
  ocn_exec ge e le m (isd_search version) t le' m' out -> out = Out_normal.
Proof.
  intros version ge e le m t le' m' out Hrun.
  destruct version; cbn [isd_search isd_body fn_body] in Hrun;
    destruct (ibk_split_sequence _ _ _ _
      (Sset ISD._i (Econst_int (Int.repr 0) tint)) _ _ _ _ _ eq_refl Hrun)
      as (loop_le & loop_m & pre & rest & Htrace & Hset & Hloop).
  all: eapply igb_loop_normal; [exact Hloop|reflexivity].
Qed.

Lemma isd_split_search : forall version ge e le m rest t le' m' out,
  ocn_exec ge e le m (Ssequence (isd_search version) rest) t le' m' out ->
  exists middle memory pre suf, t = pre ++ suf /\
    ocn_exec ge e le m (isd_search version) pre middle memory Out_normal /\
    ocn_exec ge e middle memory rest suf le' m' out.
Proof.
  intros version ge e le m rest t le' m' out Hrun.
  inversion Hrun; subst.
  - eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (isd_search _) _ _ _ _ |- _ =>
      pose proof (isd_search_finishes_normally _ _ _ _ _ _ _ _ _ Hr) end.
    contradiction.
Qed.

(** This identifies the actual destination; it does not posit that the
    helper's stores belong to a harmless-store relation. The count value is
    deliberately unrestricted, covering both milestone and non-milestone
    paths as well as failed/non-finite observations of other tracked cells. *)
Lemma isd_sync_actual_store : forall version e le m t le' m' out mb,
  le ! ISD._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    isd_sync t le' m' out ->
  t = E0 /\ exists value, Mem.store Mint16signed m mb 184 value = Some m'.
Proof.
  intros version e le m t le' m' out mb Hm Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset ISD._t'2 isd_current_count)
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & first & last & Htrace & Hread & Hwrite).
  inversion Hread; subst; clear Hread.
  match type of Hwrite with ocn_exec ?ge ?env ?temps ?memory ?statement ?tr ?temps' ?memory' ?outcome =>
    assert (temps ! ISD._m = Some (Vptr mb Ptrofs.zero)) as Hstill
      by (rewrite PTree.gso by discriminate; exact Hm);
    destruct (ibr_field_assignment_store ge env temps memory ISD._m ISD._MarioState
      ISD._prevNumStarsForDialog tshort 184 Mint16signed _ tr temps' memory' outcome
      mb Ptrofs.zero Hstill (proj2 (isd_selected_count_layout version)) eq_refl Hwrite)
      as (-> & _ & _ & value & Hstore)
  end.
  split; [reflexivity|]. exists value. exact Hstore.
Qed.

Theorem isd_completed_check_has_one_counter_store :
  forall version m mb t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (isd_body version)) [Vptr mb Ptrofs.zero] t m' result ->
  t = E0 /\ exists value, Mem.store Mint16signed m mb 184 value = Some m'.
Proof.
  intros version m mb t m' result Hcall.
  destruct (isd_source version) as (Hvars & Hparams & Hsource & Hreadonly).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! ISD._m = Some (Vptr mb Ptrofs.zero)) as Hm by
      (rewrite Hparams in Hb; cbn in Hb; inversion Hb; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr;
    destruct (ibk_split_sequence _ _ _ _ isd_initial _ _ _ _ _ eq_refl Hr)
      as (first_le & first_m & pre & suf & Htrace & Hinit & Hrest) end.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ ISD._m Hinit eq_refl)
    as (-> & -> & Hfirst).
  destruct (isd_split_search _ _ _ _ _ _ _ _ _ _ Hrest)
    as (search_le & search_m & first & last & Htrace2 & Hsearch & Htail).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hsearch Hreadonly)
    as (-> & -> & Hsearch_m).
  destruct (ibk_split_sequence _ _ _ _ isd_sync _ _ _ _ _ eq_refl Htail)
    as (copy_le & copy_m & copy_t & return_t & Htrace3 & Hsync & Hreturn).
  match type of Hsync with ocn_exec ?ge ?env ?temps ?memory _ ?tr ?temps' ?memory' ?outcome =>
    assert (temps ! ISD._m = Some (Vptr mb Ptrofs.zero)) as Hstill
      by (rewrite Hsearch_m, Hfirst; exact Hm);
    destruct (isd_sync_actual_store version env temps memory tr temps' memory' outcome
      mb Hstill Hsync) as (-> & value & Hstore)
  end.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ ISD._m Hreturn eq_refl)
    as (-> & -> & _).
  split; [rewrite Htrace, Htrace2, Htrace3; reflexivity|].
  exists value. exact Hstore.
Qed.

Definition InkMilestoneCheckFrame : Prop :=
  forall version m a t m' result,
  area1_state_storage_block a <> area1_object_pool_block a ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (isd_body version))
    [Vptr (area1_state_storage_block a) Ptrofs.zero] t m' result ->
  t = E0 /\ InkSameReadings a m m'.

Theorem isd_milestone_check_preserves_shared_readings : InkMilestoneCheckFrame.
Proof.
  intros version m a t m' result Hseparate Hcall.
  destruct (isd_completed_check_has_one_counter_store _ _ _ _ _ _ Hcall)
    as (Ht & value & Hstore).
  split; [exact Ht|]. intros cell Hin.
  eapply ibr_single_store_frames; [exact Hstore|].
  cbn [ink_shared_cells In] in Hin.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; subst cell;
    unfold ibr_cell_disjoint; cbn [ink_cell ink_cell_block ink_cell_offset ink_cell_chunk size_chunk];
    (left; congruence) || (right; left; lia) || (right; right; lia).
Qed.

(** A backward cut at this complete call rules it out as the first producer
    of ANY changed depth word. No incoming nonnegativity or numeric
    finiteness assumption is needed for the equality. *)
Corollary isd_milestone_check_cannot_first_change_depth :
  forall version m mb t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (isd_body version)) [Vptr mb Ptrofs.zero] t m' result ->
  Mem.load Mfloat32 m' mb 192 = Mem.load Mfloat32 m mb 192.
Proof.
  intros version m mb t m' result Hcall.
  destruct (isd_completed_check_has_one_counter_store _ _ _ _ _ _ Hcall)
    as (_ & value & Hstore).
  eapply Mem.load_store_other; [exact Hstore|]. right; right. cbn. lia.
Qed.
