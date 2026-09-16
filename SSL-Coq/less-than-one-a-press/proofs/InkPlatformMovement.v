(** A complete Mario-mode platform call preserves the Object pool.
    All five possible callees are resolved and proved here. The result is
    independent of the platform's translation, rotation or computed motion.
    It does not frame the surrounding terrain/collision scheduler. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkPlatformWriteFrame
  InkPlatformMovementSource InkPlatformSource InkCopyCaller InkFloorCallEffects
  ObjectContactNecessity SecretContactExecution SelectedClightTarget
  InkBackwardSource InkBackwardExecution ContactConsumerExecution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IPM := us_platform_displacement.

Definition ipm_leaf_globals kind : list ident := match kind with
| IPLSet => [IPM._gMarioStates] | _ => [] end.
Definition ipm_leaf_keeps kind : list ident := match kind with
| IPLGet => [IPM._x; IPM._y; IPM._z]
| IPLSet => []
| IPLMatrix => [us_math_util._dest]
| IPLMultiply | IPLTranspose => [us_object_helpers._dst] end.
Definition ipm_leaf_formals kind := fn_params (ipm_body VersionUS (Some kind)).

Lemma ipm_leaves_checked : forall version kind,
  ipw_shape (ipm_leaf_globals kind) (ipm_leaf_keeps kind) []
    (fun _ _ => false) (fn_body (ipm_body version (Some kind))) = true.
Proof. intros [] []; reflexivity. Qed.

Theorem ipm_leaf_call_frame : forall version kind m args ob t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  ipw_inputs_safe (ipm_leaf_keeps kind) ob (ipm_leaf_formals kind) args ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipm_body version (Some kind))) args t after result ->
  t = E0 /\ ipw_frame ob m after.
Proof.
  intros version kind m args ob t after result Hpool Hargs Hcall.
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite ipm_leaf_vars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (ipw_temps_safe ob (ipm_leaf_keeps kind) temps) as Htemps by
      (rewrite ipm_leaf_params in Hb;
       eapply ipw_bind_safe; [exact Hargs|exact Hb|apply ipw_undef_safe]) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (ipw_checked_frame _ empty_env ob (ipm_leaf_globals kind) (ipm_leaf_keeps kind)
      [] (fun _ _ => false) ltac:(intros; discriminate) _ _ _ _ _ _ _ Hr
      (ipm_leaves_checked version kind) ltac:(
        split;
        [ intros id Hid; destruct kind; cbn [ipm_leaf_globals] in Hid; try contradiction;
          destruct Hid as [<-|[]]; split;
          [intros b ty Hlocal; rewrite PTree.gempty in Hlocal; discriminate
          |intros Hnone b Hsymbol; eapply Genv.global_addresses_distinct; eauto; discriminate]
        |split; [intros id Hid b ofs Hread; eapply Htemps; eauto|intros; contradiction]]))
      as (Ht & Hframe & _) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  auto.
Qed.

Definition ipm_leaf_for_ident id :=
  if Pos.eqb id (ipm_ident (Some IPLGet)) then Some IPLGet else
  if Pos.eqb id (ipm_ident (Some IPLSet)) then Some IPLSet else
  if Pos.eqb id (ipm_ident (Some IPLMatrix)) then Some IPLMatrix else
  if Pos.eqb id (ipm_ident (Some IPLMultiply)) then Some IPLMultiply else
  if Pos.eqb id (ipm_ident (Some IPLTranspose)) then Some IPLTranspose else None.
Lemma ipm_leaf_for_ident_exact : forall id kind,
  ipm_leaf_for_ident id = Some kind -> id = ipm_ident (Some kind).
Proof.
  intros id kind H. unfold ipm_leaf_for_ident in H.
  repeat match type of H with context [if ?test then _ else _] =>
    destruct test eqn:?; try (inversion H; subst; now apply Pos.eqb_eq) end.
  all: discriminate.
Qed.
Definition ipm_call_check vars temps fn args := match fn with
| Evar id (Tfunction _ _ _) =>
    match ipm_leaf_for_ident id with
    | Some kind => ipw_arg_shapes vars temps (ipm_leaf_keeps kind) (ipm_leaf_formals kind) args
    | None => false end
| _ => false end.

Lemma ipm_reached_call : forall version kind e le m opt args tys ret cc t le' after out,
  e ! (ipm_ident (Some kind)) = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Scall opt (Evar (ipm_ident (Some kind)) (Tfunction tys ret cc)) args) t le' after out ->
  exists values result,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
      args (map snd (ipm_leaf_formals kind)) values /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ipm_body version (Some kind))) values t after result.
Proof.
  intros version kind e le m opt args tys ret cc t le' after out Hlocal Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ipm_selected_helpers_resolve version (Some kind)) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?tys ?ret ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id tys ret cc fb vf Hlocal Hsymbol Hr));
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Htype : type_of_fundef (Internal _) = _ |- _ =>
    unfold type_of_fundef, Clight.type_of_function, type_of_params in Htype;
    rewrite ipm_leaf_params in Htype; inversion Htype; subst end.
  eauto.
Qed.

Lemma ipm_call_frame : forall version e le m ob vars temps trues fn args t le' after out,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) us_object_list_processor._gObjectPool = Some ob ->
  (forall kind, e ! (ipm_ident (Some kind)) = None) ->
  ipw_context (Clight.globalenv (selected_clight_target version)) e le ob vars temps trues ->
  ipm_call_check vars temps fn args = true ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Scall None fn args) t le' after out -> t = E0 /\ ipw_frame ob m after.
Proof.
  intros version e le m ob vars temps trues fn args t le' after out Hpool Hnames Hctx Hcheck Hrun.
  destruct fn; try discriminate. destruct t0; try discriminate.
  cbn [ipm_call_check] in Hcheck.
  destruct (ipm_leaf_for_ident i) as [kind|] eqn:Hkind; try discriminate.
  apply ipm_leaf_for_ident_exact in Hkind. subst i.
  destruct (ipm_reached_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Hnames kind) Hrun)
    as (values & result & Hvalues & Hcall).
  eapply ipm_leaf_call_frame; [exact Hpool| |exact Hcall].
  eapply ipw_arguments_safe; eauto.
Qed.

Definition ipm_locals := map fst (fn_vars (ipm_body VersionUS None)).
Definition ipm_globals := [IPM._gMarioStates; IPM._D_8032FEC0].
Definition ipm_variables := ipm_locals ++ ipm_globals.
Lemma ipm_movement_checked : forall version,
  fn_vars (ipm_body version None) = fn_vars (ipm_body VersionUS None) /\
  fn_params (ipm_body version None) =
    [(IPM._isMario, tuint); (IPM._platform, ipd_object)] /\
  ipw_shape ipm_variables [] [IPM._isMario] (ipm_call_check ipm_variables [])
    (fn_body (ipm_body version None)) = true /\
  (forall kind, ~ In (ipm_ident (Some kind)) ipm_locals) /\
  (forall id, In id ipm_globals -> id <> us_object_list_processor._gObjectPool /\ ~ In id ipm_locals).
Proof.
  intro version. split; [destruct version; reflexivity|].
  split; [destruct version; reflexivity|].
  split; [destruct version; reflexivity|].
  split.
  - intros []; vm_compute; intuition discriminate.
  - intros id [<-|[<-|[]]]; vm_compute; intuition discriminate.
Qed.

Lemma ipm_variables_not_pool : forall id, In id ipm_variables ->
  id <> us_object_list_processor._gObjectPool.
Proof. intros id Hin E. subst id. vm_compute in Hin. intuition discriminate.
Qed.

Definition InkPlatformMovementFrame : Prop := forall version m ob platform t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipm_body version None)) [Vint Int.one; platform] t after result ->
  t = E0 /\ ipw_frame ob m after.

Theorem ipm_mario_platform_call_preserves_object_pool : InkPlatformMovementFrame.
Proof.
  intros version m ob platform t after result Hpool Hvalid Hcall.
  destruct (ipm_movement_checked version) as (Hvars & Hparams & Hbody & Hnames & Hglobals).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ empty_env _ _ _ _ |- _ =>
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha ob Hvalid
      ltac:(intros id b ty Hlocal; rewrite PTree.gempty in Hlocal; discriminate))
      as (Hlocals & Hallocframe & Houtside);
    rewrite Hvars in Houtside end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IPM._isMario = Some (Vint Int.one)) as Hmario by
      (rewrite Hparams in Hb; cbn [bind_parameter_temps] in Hb;
       inversion Hb; rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ ?e ?le _ (fn_body _) _ _ _ _ |- _ =>
    assert (forall kind, e ! (ipm_ident (Some kind)) = None) as Hcallees by
      (intro kind; rewrite Houtside by apply Hnames; apply PTree.gempty);
    assert (ipw_context (Clight.globalenv (selected_clight_target version))
      e le ob ipm_variables [] [IPM._isMario]) as Hctx by
      (split;
       [intros id Hid; split; [intros; eapply Hlocals; eauto|];
        intros Hnone b Hsymbol; eapply Genv.global_addresses_distinct;
          [exact (ipm_variables_not_pool id Hid)|exact Hsymbol|exact Hpool]
       |split; [intros; contradiction|intros id [<-|[]]; exact Hmario]]);
    destruct (ipw_checked_frame _ e ob ipm_variables [] [IPM._isMario]
      (ipm_call_check ipm_variables [])
      ltac:(intros; eapply ipm_call_frame; eauto)
      _ _ _ _ _ _ _ Hr Hbody Hctx) as (Ht & Hframe & _) end.
  split; [exact Ht|]. intros chunk ofs.
  match goal with Hfree : Mem.free_list ?last (blocks_of_env ?ge ?e) = Some ?answer |- _ =>
    rewrite (ifc_free_list_frame (blocks_of_env ge e) last answer chunk ob ofs
      ltac:(apply Forall_forall; intros [[target lo] hi] Hin;
        unfold blocks_of_env in Hin; apply in_map_iff in Hin;
        destruct Hin as [[id [b ty]] [E Hbinding]];
        cbn [block_of_binding] in E; inversion E; subst;
        eapply Hlocals; eapply PTree.elements_complete; exact Hbinding)
      Hfree) end.
  rewrite Hframe. apply Hallocframe.
Qed.

(** Work backward from ANY desired collision/display sample after movement.
    The complete platform call must already have received that sample. *)
Definition InkPlatformCannotCreateLowCollisionSample : Prop :=
  forall version m ob platform t after result offset value,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipm_body version None)) [Vint Int.one; platform] t after result ->
  Mem.load Mfloat32 after ob offset = Some value ->
  Mem.load Mfloat32 m ob offset = Some value.

Corollary ipm_collision_sample_must_precede_platform_movement :
  InkPlatformCannotCreateLowCollisionSample.
Proof.
  intros version m ob platform t after result offset value Hpool Hvalid Hcall Hvalue.
  destruct (ipm_mario_platform_call_preserves_object_pool _ _ _ _ _ _ _ Hpool Hvalid Hcall)
    as [_ Hframe]. rewrite Hframe in Hvalue; exact Hvalue.
Qed.

Definition ipm_dispatch_call := Scall None
  (Evar (ipm_ident None) (Tfunction [tuint; ipd_object] tvoid cc_default))
  [Econst_int Int.one tint; Etempvar IPM._platform ipd_object].
Lemma ipm_dispatch_call_frame : forall version le m ob t le' after out,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    ipm_dispatch_call t le' after out -> t = E0 /\ ipw_frame ob m after.
Proof.
  intros version le m ob t le' after out Hpool Hvalid Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ipm_selected_helpers_resolve version None) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?tys ?ret ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id tys ret cc fb vf eq_refl Hsymbol Hr));
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  match goal with Hcast : sem_cast (Vint Int.one) _ tuint _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  eapply ipm_mario_platform_call_preserves_object_pool; eauto.
Qed.

Definition ipm_dispatch_prefix version :=
  ocn_prefix_items 2 (fn_body (ipd_body version IPDApply)).
Lemma ipm_dispatch_source : forall version,
  fn_vars (ipd_body version IPDApply) = [] /\
  fn_body (ipd_body version IPDApply) =
    ocn_prepend (ipm_dispatch_prefix version)
      (Sifthenelse (Etempvar IPM._t'2 tint) ipm_dispatch_call Sskip) /\
  forallb ibk_normal (ipm_dispatch_prefix version) = true /\
  cce_readonly_keep IPM._isMario (ocn_prepend (ipm_dispatch_prefix version) Sskip) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Definition InkPlatformDispatcherFrame : Prop := forall version m ob t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipd_body version IPDApply)) [] t after result ->
  t = E0 /\ ipw_frame ob m after.

Theorem ipm_complete_dispatch_preserves_object_pool : InkPlatformDispatcherFrame.
Proof.
  intros version m ob t after result Hpool Hvalid Hcall.
  destruct (ipm_dispatch_source version) as (Hvars & Hbody & Hnormal & Hreadonly).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (middle & memory & pre & rest & Htrace & Hpre & Hbranch) end.
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hpre Hreadonly) as (-> & -> & _).
  assert (rest = E0 /\ ipw_frame ob m1 m2) as Hresult.
  { inversion Hbranch; subst. destruct b.
    - eapply ipm_dispatch_call_frame; eauto.
    - match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
        inversion Hs; subst end. split; [reflexivity|intros chunk ofs; reflexivity]. }
  destruct Hresult as (-> & Hframe).
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  split; [reflexivity|exact Hframe].
Qed.


(** Six actual cells, rather than an assumed abstract platform frame.
    The offsets are the generated Object layout already used by Ink's
    display-copy and raw-copy proofs. *)
Definition InkPlatformRetainsCollisionAndDisplay : Prop :=
  forall version m ob t after result base offset,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m ob ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ipd_body version IPDApply)) [] t after result ->
  In offset [32; 36; 40; 160; 164; 168] ->
  Mem.load Mfloat32 after ob (base + offset) = Mem.load Mfloat32 m ob (base + offset).
Theorem ipm_collision_and_display_survive_complete_platform_phase :
  InkPlatformRetainsCollisionAndDisplay.
Proof.
  intros version m ob t after result base offset Hpool Hvalid Hcall Hin.
  destruct (ipm_complete_dispatch_preserves_object_pool _ _ _ _ _ _ Hpool Hvalid Hcall)
    as [_ Hframe]. apply Hframe.
Qed.

Definition InkPlatformMovementBoundary : Prop :=
  (forall version kind, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) (ipm_ident kind) = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (ipm_body version kind))) /\
  InkPlatformMovementFrame /\ InkPlatformCannotCreateLowCollisionSample /\
  InkPlatformDispatcherFrame /\ InkPlatformRetainsCollisionAndDisplay.

Theorem ipm_moving_support_backward_checked : InkPlatformMovementBoundary.
Proof.
  split; [exact ipm_selected_helpers_resolve|].
  split; [exact ipm_mario_platform_call_preserves_object_pool|].
  split; [exact ipm_collision_sample_must_precede_platform_movement|].
  split; [exact ipm_complete_dispatch_preserves_object_pool|].
  exact ipm_collision_and_display_survive_complete_platform_phase.
Qed.
