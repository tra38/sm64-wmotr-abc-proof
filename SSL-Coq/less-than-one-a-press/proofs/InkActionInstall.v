(** The real central action setter cannot install either long-jump action
    unless that action was requested.  Calls before the final store retain
    all of their actual memory effects. *)
From Coq Require Import Bool List Lia ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkActionConstructor
  InkActionConstructorSource InkActionTimerReset InkLandingHistoryReturn
  InkBackwardSource InkBackwardExecution InkFloorResetExecution InkCopyCaller
  InkControllerEdge InkMarioInputFlag InkActionPassStart SecretContactExecution
  ContactConsumerExecution ObjectContactNecessity Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Opaque selected_clight_target.

Definition iai_initializer_type := Tfunction
  [tptr (Tstruct IBM._MarioState noattr); tuint; tuint] tuint cc_default.
Definition iai_initializer_arguments :=
  [Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr));
   Etempvar IBM._action tuint; Etempvar IBM._actionArg tuint].
Definition iai_initializer_call kind temp := Scall (Some temp)
  (Evar (iai_ident kind) iai_initializer_type) iai_initializer_arguments.
Definition iai_initializer_branch kind temp := Ssequence
  (Ssequence (iai_initializer_call kind temp)
    (Sset IBM._action (Etempvar temp tuint))) Sbreak.

Lemma iai_uint_cast_identity : forall value m result,
  sem_cast value tuint tuint m = Some result -> result = value.
Proof. intros [] m result H; cbn in H; try discriminate; inversion H; reflexivity. Qed.

Lemma iai_initializer_arguments_safe : forall ge le m args,
  iai_safe_temps le ->
  eval_exprlist ge empty_env le m iai_initializer_arguments
    [tptr (Tstruct IBM._MarioState noattr); tuint; tuint] args ->
  exists mario action arg, args = [mario; action; arg] /\ iai_safe_value action.
Proof.
  intros ge le m args Hsafe Hargs. unfold iai_initializer_arguments in Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._action tuint) ?v,
    Hcast : sem_cast ?v (typeof (Etempvar IBM._action tuint)) tuint _ = Some ?answer |- _ =>
    assert (answer = v) as Heq by (eapply iai_uint_cast_identity; exact Hcast); subst answer;
    assert (iai_safe_value v) as Hvalue by
      (eapply Hsafe; inversion Hr; subst; [eassumption|];
       match goal with Hbad : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hbad end)
  end.
  do 3 eexists. split; [reflexivity|assumption].
Qed.

Lemma iai_initializer_call_safe : forall version kind temp le m t le' m' out,
  iai_safe_temps le ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iai_initializer_call kind temp) t le' m' out ->
  exists value, le' = PTree.set temp value le /\ iai_safe_value value /\ out = Out_normal.
Proof.
  intros version kind temp le m t le' m' out Hsafe Hrun.
  destruct (iai_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  inversion Hrun; subst.
  match goal with H : classify_fun _ = _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (eapply (sce_function_name_value
        (Clight.globalenv (selected_clight_target version)) empty_env le m
        (iai_ident kind) [tptr (Tstruct IBM._MarioState noattr); tuint; tuint]
        tuint cc_default fb vf); [apply PTree.gempty|exact Hsymbol|exact H]); subst vf end.
  match goal with H : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in H;
    rewrite Hfunction in H; inversion H; subst fd end.
  match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    destruct (iai_initializer_arguments_safe _ _ _ _ Hsafe H)
      as (mario & action & arg & -> & Haction) end.
  eexists. split; [reflexivity|]. split; [|reflexivity].
  eapply iai_completed_initializer_cannot_manufacture_long_jump; eassumption.
Qed.

Lemma iai_initializer_branch_safe : forall version kind temp le m t le' m' out,
  iai_safe_temps le ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iai_initializer_branch kind temp) t le' m' out ->
  iai_safe_temps le' /\ out = Out_break.
Proof.
  intros version kind temp le m t le' m' out Hsafe Hrun.
  unfold iai_initializer_branch in Hrun.
  destruct (ibk_split_sequence _ _ _ _
    (Ssequence (iai_initializer_call kind temp) (Sset IBM._action (Etempvar temp tuint)))
    _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hpair & Hbreak).
  destruct (ibk_split_sequence _ _ _ _ (iai_initializer_call kind temp) _ _ _ _ _ eq_refl Hpair)
    as (call_le & call_m & call_t & set_t & HpairTrace & Hcall & Hset).
  destruct (iai_initializer_call_safe _ _ _ _ _ _ _ _ _ Hsafe Hcall)
    as (value & -> & Hvalue & _).
  inversion Hset; subst.
  match goal with H : eval_expr _ _ _ _ (Etempvar temp _) ?v |- _ =>
    assert (v = value) by (eapply ocn_temp_value; [exact H|apply PTree.gss]); subst v end.
  inversion Hbreak; subst. split; [|reflexivity].
  intros answer Hget. rewrite PTree.gss in Hget. inversion Hget; subst. exact Hvalue.
Qed.

Lemma iai_break_sequence_safe : forall version kind temp tail le m t le' m' out,
  iai_safe_temps le ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Ssequence (iai_initializer_branch kind temp) tail) t le' m' out ->
  iai_safe_temps le' /\ out = Out_break.
Proof.
  intros version kind temp tail le m t le' m' out Hsafe Hrun. inversion Hrun; subst.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ (iai_initializer_branch _ _) _ _ _ _ |- _ =>
      destruct (iai_initializer_branch_safe _ _ _ _ _ _ _ _ _ Hsafe H) as [_ Hbad]; discriminate end.
  - eapply iai_initializer_branch_safe; eassumption.
Qed.

Theorem iai_real_setter_initializer_keeps_non_target_request : forall version le m t le' m' out,
  iai_safe_temps le ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (iar_initializer version) t le' m' out -> iai_safe_temps le'.
Proof.
  intros version le m t le' m' out Hsafe Hrun.
  destruct version; cbn [iar_initializer ilh_set_action_body ibk_head fn_body] in Hrun;
    inversion Hrun; subst.
  all: match goal with H : ClightBigstep.exec_stmt _ _ _ _ _
      (seq_of_labeled_statement (select_switch _ _)) _ _ _ _ |- _ =>
    cbv [select_switch select_switch_case select_switch_default] in H;
    repeat match type of H with context [if ?test then _ else _] => destruct test end;
    cbn [seq_of_labeled_statement] in H end.
  all: first [
    eapply (proj1 (iai_break_sequence_safe _ IAIMoving IBM._t'1 _ _ _ _ _ _ _ Hsafe ltac:(eassumption)))
  | eapply (proj1 (iai_break_sequence_safe _ IAIAir IBM._t'2 _ _ _ _ _ _ _ Hsafe ltac:(eassumption)))
  | eapply (proj1 (iai_break_sequence_safe _ IAISubmerged IBM._t'3 _ _ _ _ _ _ _ Hsafe ltac:(eassumption)))
  | eapply (proj1 (iai_break_sequence_safe _ IAICutscene IBM._t'4 _ _ _ _ _ _ _ Hsafe ltac:(eassumption)))
  | match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
      inversion H; subst; exact Hsafe end ].
Qed.

Definition iai_state := Ederef (Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr)))
  (Tstruct IBM._MarioState noattr).
Definition iai_action_field := Efield iai_state IBM._action tuint.
Definition iai_action_load m mb mo :=
  Mem.load Mint32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 12))).
Definition iai_before_install version := ocn_prefix_items 3
  (rank12b_drop_sequences 1 (fn_body (ilh_set_action_body version))).
Definition iai_install := Sassign iai_action_field (Etempvar IBM._action tuint).
Definition iai_after_install version := rank12b_drop_sequences 5
  (fn_body (ilh_set_action_body version)).

Lemma iai_setter_source_cuts : forall version,
  fn_body (ilh_set_action_body version) = Ssequence (iar_initializer version)
    (ocn_prepend (iai_before_install version)
      (Ssequence iai_install (iai_after_install version))) /\
  forallb ibk_normal (iai_before_install version) = true /\
  ifr_keeps_temp IBM._m (ocn_prepend (iai_before_install version) Sskip) = true /\
  ifr_keeps_temp IBM._action (ocn_prepend (iai_before_install version) Sskip) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iai_final_action_store_is_safe : forall version le m mb mo t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> iai_safe_temps le ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    iai_install t le' m' out ->
  exists value, iai_action_load m' mb mo = Some value /\ iai_safe_value value.
Proof.
  intros version le m mb mo t le' m' out Hm Hsafe Hrun.
  unfold iai_install, iai_action_field in Hrun. inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) _ _ _
      IBM._m IBM._MarioState IBM._action tuint
      mb mo 12 _ _ _ Hm (ias_selected_action_field version) Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._action _) ?v |- _ =>
    assert (iai_safe_value v) as Hvalue by
      (eapply Hsafe; inversion Hr; subst; [eassumption|];
       match goal with Hb : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hb end)
  end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    apply iai_uint_cast_identity in Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
    unfold iai_action_load; rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore) end.
  eexists. split; [reflexivity|].
  match type of Hvalue with iai_safe_value ?value => destruct value end;
    cbn [Val.load_result]; unfold iai_safe_value in *; intuition discriminate.
Qed.

Definition iai_action_frame version s : Prop := forall le m mb mo t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) -> imf_room mo ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m s t le' m' out ->
  iai_action_load m' mb mo = iai_action_load m mb mo.

Lemma iai_frame_readonly : forall version s,
  cce_readonly_keep IBM._m s = true -> iai_action_frame version s.
Proof.
  intros version s Hok le m mb mo t le' m' out Hm Hroom Hrun.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun Hok) as (_ & -> & _).
  reflexivity.
Qed.

Lemma iai_frame_sequence : forall version a b,
  ifr_keeps_temp IBM._m a = true ->
  iai_action_frame version a -> iai_action_frame version b ->
  iai_action_frame version (Ssequence a b).
Proof.
  intros version a b Hkeep Ha Hb le m mb mo t le' m' out Hm Hroom Hrun.
  inversion Hrun; subst.
  - match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ a _ ?middle ?memory _,
      Hlast : ClightBigstep.exec_stmt _ _ _ _ _ b _ _ _ _ |- _ =>
      assert (middle ! IBM._m = Some (Vptr mb mo)) as Hnow by
        (rewrite <- Hm; eapply ifr_execution_keeps_temp; [exact Hfirst|exact Hkeep]);
      rewrite (Hb middle memory mb mo _ _ _ _ Hnow Hroom Hlast);
      exact (Ha le m mb mo _ _ _ _ Hm Hroom Hfirst) end.
  - eapply Ha; eassumption.
Qed.

Lemma iai_later_field_preserves_action : forall version field ty chunk offset rhs,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState field offset = true ->
  access_mode ty = By_value chunk -> 16 <= offset <= 200 ->
  iai_action_frame version (Sassign (Efield iai_state field ty) rhs).
Proof.
  intros version field ty chunk offset rhs Hfield Hmode Hoffset
    le m mb mo t le' m' out Hm Hroom Hrun. inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ice_field_location _ _ _ _ IBM._m IBM._MarioState field ty
      mb mo offset _ _ _ Hm Hfield Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  all: match goal with Haccess : access_mode (typeof (Efield _ _ _)) = ?mode |- _ =>
    change (access_mode ty = mode) in Haccess;
    rewrite Hmode in Haccess; inversion Haccess; subst end.
  unfold iai_action_load. eapply Mem.load_store_other; [eassumption|].
  right. left. cbn [size_chunk]. rewrite !imf_address by (assumption || lia). lia.
Qed.

Lemma iai_later_fields : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._actionArg 28 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._actionState 24 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._actionTimer 26 = true.
Proof.
  intro version.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version)) IBM._MarioState IBM._actionArg 28 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IBM._MarioState IBM._actionState 24 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) IBM._MarioState IBM._actionTimer 26 = true).
  rewrite <- EyerokRank15LiveMovement.rank15_selected_header_environment_exact.
  destruct version; vm_compute; repeat split; reflexivity.
Qed.

Lemma iai_after_install_preserves_action : forall version,
  iai_action_frame version (iai_after_install version).
Proof.
  intro version. destruct (iai_later_fields version) as (Harg & Hstate & Htimer).
  assert (iai_after_install version =
    Ssequence (Sassign (Efield iai_state IBM._actionArg tuint) (Etempvar IBM._actionArg tuint))
    (Ssequence (Sassign (Efield iai_state IBM._actionState tushort) (Econst_int Int.zero tint))
    (Ssequence (Sassign (Efield iai_state IBM._actionTimer tushort) (Econst_int Int.zero tint))
      (Sreturn (Some (Econst_int Int.one tint)))))) as Hshape by (destruct version; reflexivity).
  rewrite Hshape. repeat apply iai_frame_sequence; try reflexivity.
  - eapply iai_later_field_preserves_action; [exact Harg|reflexivity|lia].
  - eapply iai_later_field_preserves_action; [exact Hstate|reflexivity|lia].
  - eapply iai_later_field_preserves_action; [exact Htimer|reflexivity|lia].
  - apply iai_frame_readonly. reflexivity.
Qed.

Definition InkCompletedActionInstallExclusion : Prop := forall version m mb mo action arg t m' result,
  imf_room mo -> iai_safe_value action ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ilh_set_action_body version)) [Vptr mb mo; action; arg] t m' result ->
  exists value, iai_action_load m' mb mo = Some value /\ iai_safe_value value.

Theorem iai_completed_setter_cannot_install_unrequested_long_jump : InkCompletedActionInstallExclusion.
Proof.
  intros version m mb mo action arg t m' result Hroom Hsafe Hcall.
  destruct (iar_source_cuts version) as (Hvars & Hparams & _).
  destruct (iai_setter_source_cuts version) as (Hbody & Hnormal & HkeepM & HkeepAction).
  inversion Hcall; subst.
  match goal with H : function_entry2 _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in H; inversion H; subst; clear H end.
  match goal with H : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in H; inversion H; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb mo)) as Hm by
      (rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind;
       repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    assert (iai_safe_temps temps) as HsafeEntry by
      (intros value Hget; rewrite Hparams in Hbind; cbn in Hbind; inversion Hbind; subst;
       rewrite PTree.gso, PTree.gss in Hget by discriminate; inversion Hget; subst; exact Hsafe)
  end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (iar_split_initializer version _ _ _ _ _ _ _ _ _ Hr)
      as (first_le & first_m & first_t & rest_t & Htrace & Hfirst & Hrest) end.
  pose proof (iai_real_setter_initializer_keeps_non_target_request _ _ _ _ _ _ _ HsafeEntry Hfirst) as HfirstSafe.
  pose proof (iar_initializer_keeps_m version _ _ _ _ _ _ _ _ Hfirst) as HfirstM.
  destruct (ibk_split_prefix _ _ (iai_before_install version)
    (Ssequence iai_install (iai_after_install version)) _ _ _ _ _ _ Hnormal Hrest)
    as (store_le & store_m & pre & suf & HrestTrace & Hprefix & Htail).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IBM._m Hprefix HkeepM) as HstoreM.
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IBM._action Hprefix HkeepAction) as HstoreAction.
  assert (store_le ! IBM._m = Some (Vptr mb mo)) as HmStore
    by (rewrite HstoreM; change (first_le ! InkMovingBackwardSource.IMB._m = Some (Vptr mb mo));
        rewrite HfirstM; exact Hm).
  assert (iai_safe_temps store_le) as HsafeStore
    by (intros value Hget; apply HfirstSafe; rewrite HstoreAction in Hget; exact Hget).
  destruct (ibk_split_sequence _ _ _ _ iai_install _ _ _ _ _ eq_refl Htail)
    as (after_le & after_m & write_t & return_t & HtailTrace & Hwrite & Hafter).
  destruct (iai_final_action_store_is_safe _ _ _ _ _ _ _ _ _ HmStore HsafeStore Hwrite)
    as (value & Hvalue & HsafeValue).
  assert (after_le ! IBM._m = Some (Vptr mb mo)) as HmAfter.
  { rewrite <- HmStore. eapply ifr_execution_keeps_temp; [exact Hwrite|reflexivity]. }
  exists value. split; [|exact HsafeValue].
  rewrite (iai_after_install_preserves_action version after_le after_m mb mo
    return_t _ _ _ HmAfter Hroom Hafter). exact Hvalue.
Qed.
