(** Both angle helpers are internal, read-only calls in the selected game.
    This covers every successful execution, without assuming finite inputs
    or substituting an abstract effect for the table lookup. *)
From Coq Require Import Bool List.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkInputContinuationSource
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Lemma iia_actual_named_call : forall version kind le m opt args tys ret t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt (Evar (iis_ident kind) (Tfunction tys ret cc_default)) args)
    t le' m' out ->
  exists values result,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (iis_body version kind)) values t m' result.
Proof.
  intros version kind le m opt args tys ret t le' m' out Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (iis_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?tys ?ret ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id tys ret cc fb vf eq_refl Hsymbol Hr));
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  eauto.
Qed.

Lemma iia_lookup_is_readonly : forall version,
  cce_readonly_keep us_mario._m (fn_body (iis_body version IILookup)) = true.
Proof. intros []; reflexivity. Qed.

Theorem iia_lookup_call_preserves_memory : forall version m args t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (iis_body version IILookup)) args t after result ->
  t = E0 /\ after = m.
Proof.
  intros version m args t after result Hcall. inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite iis_helpers_have_no_stack_objects in Halloc; inversion Halloc; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hbody (iia_lookup_is_readonly version))
      as (-> & -> & _) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.

Inductive iia_angle_statement : statement -> Prop :=
| iia_readonly : forall s, cce_readonly_keep us_mario._m s = true -> iia_angle_statement s
| iia_lookup : forall opt args, iia_angle_statement
    (Scall opt (Evar (iis_ident IILookup) (Tfunction [tfloat; tfloat] tushort cc_default)) args)
| iia_seq : forall s1 s2, iia_angle_statement s1 -> iia_angle_statement s2 ->
    iia_angle_statement (Ssequence s1 s2)
| iia_if : forall cond yes no, iia_angle_statement yes -> iia_angle_statement no ->
    iia_angle_statement (Sifthenelse cond yes no).

Lemma iia_real_angle_classified : forall version,
  iia_angle_statement (fn_body (iis_body version IIAngle)).
Proof.
  intros []; cbn [iis_body fn_body].
  all: repeat first [apply iia_readonly; reflexivity | apply iia_lookup | apply iia_seq | apply iia_if].
Qed.

Lemma iia_angle_statement_frame : forall s, iia_angle_statement s ->
  forall version le m t le' after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m s t le' after out ->
  t = E0 /\ after = m.
Proof.
  intros s Hshape. induction Hshape; intros version le m t le' after out Hrun.
  - destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun H) as (-> & -> & _). auto.
  - destruct (iia_actual_named_call _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as (values & result & Hcall).
    eapply iia_lookup_call_preserves_memory; exact Hcall.
  - inversion Hrun; subst.
    + match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _,
        Hb : ClightBigstep.exec_stmt _ _ _ _ _ s2 _ _ _ _ |- _ =>
        destruct (IHHshape1 _ _ _ _ _ _ _ Ha) as (-> & ->);
        destruct (IHHshape2 _ _ _ _ _ _ _ Hb) as (-> & ->) end. auto.
    + eapply IHHshape1; eauto.
  - inversion Hrun; subst. destruct b; [eapply IHHshape1|eapply IHHshape2]; eauto.
Qed.

Theorem iia_angle_call_preserves_memory : forall version m args t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (iis_body version IIAngle)) args t after result ->
  t = E0 /\ after = m.
Proof.
  intros version m args t after result Hcall. inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite iis_helpers_have_no_stack_objects in Halloc; inversion Halloc; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (iia_angle_statement_frame _ (iia_real_angle_classified version) _ _ _ _ _ _ _ Hbody)
      as (-> & ->) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.
