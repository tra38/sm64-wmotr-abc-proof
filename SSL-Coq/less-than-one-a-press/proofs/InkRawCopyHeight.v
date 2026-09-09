(** The collision-height store copies the incoming State height while leaving
    display Y alone. This is a reached checkpoint, not a whole-frame frame. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkRawCopySource
  InkRawCopyExpressions InkRawCopyStores InkRawCopyIndex InkFloorResetCopy
  InkFloorResetExecution InkBackwardExecution InkCopyCaller
  ObjectContactNecessity Area1Rank18CopyRead Area1Rank18CopyResolution
  Area1Rank18StateArrayBound EyerokRank15LiveMovement
  CompositeLayoutRefinement EntryMemory OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition InkRawCopyHeightCut : Prop :=
  forall version m cb gb mb ob slot height t m' result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge IRC._gCurrentObject = Some cb ->
  Genv.find_symbol ge IRC._gMarioObject = Some gb ->
  Genv.find_symbol ge IRC._gMarioStates = Some mb ->
  Genv.find_symbol ge IRC._gObjectPool = Some ob ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 m gb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (rank18_copy_body version)) [] t m' result ->
  exists choice_le before_le before_m after_le after_m final_le pre write_trace suffix out,
    t = pre ++ (write_trace ++ suffix) /\
    before_le ! IRC._i = Some (Vint Int.zero) /\
    ocn_exec ge empty_env choice_le m (ocn_prepend (irc_before_y version) Sskip)
      pre before_le before_m Out_normal /\
    ocn_exec ge empty_env before_le before_m (irc_y_stage version)
      write_trace after_le after_m Out_normal /\
    Mem.store Mfloat32 before_m ob (object_slot_offset slot + 164)
      (Vsingle height) = Some after_m /\
    Mem.load Mfloat32 after_m ob (object_slot_offset slot + 164) = Some (Vsingle height) /\
    Mem.load Mfloat32 after_m mb 64 = Some (Vsingle height) /\
    Mem.load Mfloat32 after_m ob (object_slot_offset slot + 36) =
      Mem.load Mfloat32 m ob (object_slot_offset slot + 36) /\
    ocn_exec ge empty_env after_le after_m (irc_after_y version) suffix final_le m' out.

Theorem irc_completed_copy_has_exact_height_cut : InkRawCopyHeightCut.
Proof.
  unfold InkRawCopyHeightCut.
  intros version m cb gb mb ob slot height t m' result Hslot
    HcurrentSymbol HmarioSymbol HstateSymbol HpoolSymbol Hcurrent Hmario Hheight Hcall.
  assert (cb <> ob) as HcurrentSeparate by
    (eapply Genv.global_addresses_distinct; eauto; discriminate).
  assert (mb <> ob) as HstateSeparate by
    (exact (ibcc_ordinary_storage_separate _ _ _ HstateSymbol HpoolSymbol)).
  destruct (irc_generated_cuts version) as (Hvars & Hbody & Hstages & Hnormal & HyNormal & HkeepIndex).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (rank18_copy_entry_has_empty_locals _ _ _ _ _ _ _ Hentry) as (-> & ->) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hrun;
    destruct (ibk_split_sequence _ _ _ _ (Sset IRC._i (Econst_int Int.zero tint))
      _ _ _ _ _ eq_refl Hrun)
      as (initial_le & initial_m & initial_trace & rest_trace & Htrace & Hinitial & Hrest) end.
  inversion Hinitial; subst.
  match goal with Hconst : eval_expr _ _ _ _ (Econst_int Int.zero tint) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_const_int_value; eauto); subst v end.
  destruct (ibk_split_sequence _ _ _ _ rank18_index_test _ _ _ _ _ eq_refl Hrest)
    as (choice_le & choice_m & choice_trace & tail_trace & HchoiceTrace & Hchoice & Htail).
  destruct (irc_index_test_keeps_zero _ _ _ _ _ _ _ _ _ _ _ _
    (PTree.gempty _ _) (PTree.gempty _ _) HcurrentSymbol HmarioSymbol Hcurrent Hmario
    (PTree.gss _ _ _) Hchoice) as (Hindex & -> & -> & _).
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Htail)
    as (before_le & before_m & pre & rest & HprefixTrace & Hprefix & HrestY).
  pose proof (irc_before_y_preserves_protected_reads _ _ _ _ _ _ _ _ _ _ _ _
    Hstages Hslot HcurrentSeparate (PTree.gempty _ _) HcurrentSymbol Hcurrent Hprefix) as HprefixFrame.
  assert (before_le ! IRC._i = Some (Vint Int.zero)) as HbeforeIndex.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hprefix HkeepIndex). exact Hindex. }
  assert (Mem.load Mint32 before_m cb 0 =
    Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HbeforeCurrent.
  { rewrite HprefixFrame; [exact Hcurrent|left; exact HcurrentSeparate]. }
  assert (Mem.load Mfloat32 before_m mb 64 = Some (Vsingle height)) as HbeforeHeight.
  { rewrite HprefixFrame; [exact Hheight|left; exact HstateSeparate]. }
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HyNormal HrestY)
    as (after_le & after_m & write_trace & suffix & HwriteTrace & Hwrite & Hsuffix).
  pose proof Hwrite as HactualWrite. rewrite irc_y_stage_is_generated in Hwrite.
  destruct (irc_float_stage_actual_store version empty_env before_le before_m
    IRC._t'27 IRC._t'28 irc_source_y rank15_y_index 7 cb ob
    (Ptrofs.repr (object_slot_offset slot)) write_trace after_le after_m Out_normal
    ltac:(discriminate) (PTree.gempty _ _) HcurrentSymbol HbeforeCurrent
    eq_refl eq_refl ltac:(cbn; auto) Hwrite)
    as (read & written & Hread & Hcast & Hstore & _).
  assert ((PTree.set IRC._t'27 (Vptr ob (Ptrofs.repr (object_slot_offset slot))) before_le)
    ! IRC._i = Some (Vint Int.zero)) as HsourceIndex
    by (rewrite PTree.gso by discriminate; exact HbeforeIndex).
  pose proof (irc_source_y_read _ _ _ _ _ _ _ (PTree.gempty _ _)
    HstateSymbol HsourceIndex HbeforeHeight Hread) as HsourceHeight. subst read.
  cbn in Hcast. inversion Hcast; subst written.
  pose proof (irc_store_frames_protected_reads _ _ _ _ 7 _ Hslot ltac:(cbn; auto) Hstore) as HyFrame.
  rewrite irc_slot_address in Hstore by (auto; lia).
  match type of Hsuffix with ocn_exec _ _ _ _ _ _ ?final_le _ ?out =>
    exists choice_le, before_le, before_m, after_le, after_m, final_le,
      pre, write_trace, suffix, out end.
  split; [subst; reflexivity|].
  split; [exact HbeforeIndex|]. split; [exact Hprefix|]. split; [exact HactualWrite|].
  split; [exact Hstore|]. split; [exact (Mem.load_store_same _ _ _ _ _ _ Hstore)|].
  split.
  - rewrite HyFrame; [exact HbeforeHeight|left; exact HstateSeparate].
  - split; [|exact Hsuffix].
    rewrite HyFrame, HprefixFrame; try reflexivity;
      unfold irc_outside_copy_prefix; right; left; cbn [size_chunk]; lia.
Qed.

Definition InkRawCopyCheckedBoundary : Prop :=
  InkFloorResetCheckedBoundary /\ Area1Rank18CopyCheckedBoundary /\ InkRawCopyHeightCut.

Theorem irc_raw_copy_boundary_checked : InkRawCopyCheckedBoundary.
Proof.
  split; [exact ifrc_floor_reset_boundary_checked|].
  split; [exact area1_rank18_copy_checked_boundary_holds|].
  exact irc_completed_copy_has_exact_height_cut.
Qed.
