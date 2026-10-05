(** The actual completed Mario callback must reach its State-to-Object copy.

    The whole execute_mario_action call and the particle-flags store remain
    an actual, unframed prefix.  In particular, a completed floor-null early
    return inside execute_mario_action cannot bypass the caller's copy.
    The particle loop after that copy is retained as an actual execution
    residual, not assumed harmless.  The height conclusion is at the copy's
    completed return, not at the next collision check or callback return. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkScheduledActionSource
  InkMarioCallbackHistory InkRawCopySource InkRawCopyCompletion
  InkBackwardSource InkBackwardExecution ObjectContactNecessity
  SecretContactExecution Area2Rank12BContact Area1Rank18CopyRead
  Area1Rank18CopyResolution OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition imrc_body version := isc_body version.
Definition imrc_before_copy version := ocn_prefix_items 3 (fn_body (imrc_body version)).
Definition imrc_copy version := ibk_head
  (rank12b_drop_sequences 3 (fn_body (imrc_body version))).
Definition imrc_tail version :=
  rank12b_drop_sequences 4 (fn_body (imrc_body version)).
Definition imrc_copy_call := Scall None
  (Evar ISC._copy_mario_state_to_object (Tfunction [] tvoid cc_default)) [].

Lemma imrc_generated_copy_cut : forall version,
  fn_vars (imrc_body version) = [] /\
  fn_params (imrc_body version) = [] /\
  fn_body (imrc_body version) = ocn_prepend (imrc_before_copy version)
    (Ssequence (imrc_copy version) (imrc_tail version)) /\
  imrc_copy version = imrc_copy_call /\
  forallb ibk_normal (imrc_before_copy version) = true /\
  ibk_normal (imrc_copy version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

(** No callback local can shadow the real copy function.  Empty allocation
    also preserves the incoming memory; this does not frame the callback. *)
Lemma imrc_entry_has_empty_locals : forall version ge arguments m e le entry_m,
  function_entry2 ge (imrc_body version) arguments m e le entry_m ->
  e = empty_env /\ entry_m = m.
Proof.
  intros version ge arguments m e le entry_m Hentry.
  destruct (imrc_generated_copy_cut version) as (Hvars & _).
  inversion Hentry; subst.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst end.
  auto.
Qed.

(** Resolve the reached call to the selected real US/JP body.  The actual
    call has no arguments and does not change its caller temporaries. *)
Lemma imrc_reached_copy_calls_real_body : forall version e le m t le' after out,
  e ! ISC._copy_mario_state_to_object = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (imrc_copy version) t le' after out ->
  exists result,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (rank18_copy_body version)) [] t after result /\
    le' = le /\ out = Out_normal.
Proof.
  intros version e le m t le' after out Hlocal Hrun.
  destruct (imrc_generated_copy_cut version) as (_ & _ & _ & Hshape & _).
  destruct (rank18_selected_copy_body_resolves version) as (b & Hsymbol & Hfunction).
  rewrite Hshape in Hrun. unfold imrc_copy_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto);
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hargs : eval_exprlist _ _ _ _ [] _ _ |- _ =>
    inversion Hargs; subst end.
  eauto 8.
Qed.

Definition InkMarioCallbackRawCopyCut : Prop :=
  forall version m t returned result,
  let ge := Clight.globalenv (selected_clight_target version) in
  ClightBigstep.Clight2.eval_funcall ge m (Internal (imrc_body version))
    [] t returned result ->
  exists e entry_le entry_m cut_le cut_m copy_le copy_m last_le last_m
    pre copy_trace suffix out copy_result,
    t = pre ++ (copy_trace ++ suffix) /\
    function_entry2 ge (imrc_body version) [] m e entry_le entry_m /\
    e = empty_env /\ entry_m = m /\
    ocn_exec ge e entry_le entry_m (ocn_prepend (imrc_before_copy version) Sskip)
      pre cut_le cut_m Out_normal /\
    ocn_exec ge e cut_le cut_m (imrc_copy version)
      copy_trace copy_le copy_m Out_normal /\
    ClightBigstep.Clight2.eval_funcall ge cut_m
      (Internal (rank18_copy_body version)) [] copy_trace copy_m copy_result /\
    copy_le = cut_le /\
    ocn_exec ge e copy_le copy_m (imrc_tail version) suffix last_le last_m out /\
    outcome_result_value out (fn_return (imrc_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some returned /\
    (forall cb gb mb ob slot height,
      (slot < object_pool_capacity)%nat ->
      Genv.find_symbol ge IRC._gCurrentObject = Some cb ->
      Genv.find_symbol ge IRC._gMarioObject = Some gb ->
      Genv.find_symbol ge IRC._gMarioStates = Some mb ->
      Genv.find_symbol ge IRC._gObjectPool = Some ob ->
      Mem.load Mint32 cut_m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      Mem.load Mint32 cut_m gb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
      Mem.load Mfloat32 copy_m ob (object_slot_offset slot + 164) = Some (Vsingle height) /\
      Mem.load Mfloat32 copy_m mb 64 = Some (Vsingle height) /\
      Mem.load Mfloat32 copy_m ob (object_slot_offset slot + 36) =
        Mem.load Mfloat32 cut_m ob (object_slot_offset slot + 36)).

Theorem imrc_completed_callback_reaches_matching_raw_copy : InkMarioCallbackRawCopyCut.
Proof.
  unfold InkMarioCallbackRawCopyCut. cbn zeta.
  intros version m t returned result Hcall.
  destruct (imrc_generated_copy_cut version)
    as (_ & _ & Hshape & _ & Hnormal & HcopyNormal).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (imrc_entry_has_empty_locals _ _ _ _ _ _ _ Hentry)
      as [Hempty HentryMemory] end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hshape in Hbody;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hbody)
      as (cut_le & cut_m & pre & following & Htrace & Hprefix & Hfollowing) end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HcopyNormal Hfollowing)
    as (copy_le & copy_m & copy_trace & suffix & HfollowingTrace & Hcopy & Hsuffix).
  assert (e ! ISC._copy_mario_state_to_object = None) as Hlocal
    by (rewrite Hempty; apply PTree.gempty).
  destruct (imrc_reached_copy_calls_real_body _ _ _ _ _ _ _ _ Hlocal Hcopy)
    as (copy_result & HrealCopy & HcopyTemps & _).
  match goal with
  | Hentry : function_entry2 _ _ _ _ ?env ?entry_le ?entry_m,
    Htail : ocn_exec _ _ _ _ (imrc_tail version) _ ?last_le ?last_m ?out |- _ =>
      exists env, entry_le, entry_m, cut_le, cut_m, copy_le, copy_m, last_le, last_m,
        pre, copy_trace, suffix, out, copy_result
  end.
  split; [rewrite Htrace, HfollowingTrace; reflexivity|].
  repeat match goal with |- _ /\ _ => split; [assumption|] end.
  intros cb gb mb ob slot height Hslot HcurrentSymbol HmarioSymbol HstateSymbol
    HpoolSymbol Hcurrent Hmario Hheight.
  eapply ircc_completed_copy_has_matching_state_and_collision_height; eauto.
Qed.

(** At this mandatory copy return there is no remaining movement/collision
    height difference, independent of the pre-copy gap and of where a bounce
    actor was placed.  Later particle/spawn effects, callback return and the
    next collision phase require their own execution and framing arguments. *)
