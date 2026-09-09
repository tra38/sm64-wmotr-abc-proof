(** Resolve actual helper calls and retain the original argument at entry. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkLateHelperSource ObjectContactNecessity SecretContactExecution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ilh_named (id : ident) (ty : type) (fn : expr) := match fn with
| Evar found actual => Pos.eqb found id && (if type_eq actual ty then true else false)
| _ => false end.
Lemma ilh_named_exact : forall id ty fn, ilh_named id ty fn = true -> fn = Evar id ty.
Proof.
  intros id ty fn. destruct fn; try discriminate.
  cbn [ilh_named]. intro H. apply andb_true_iff in H as [Hid Hty].
  apply Pos.eqb_eq in Hid. destruct (type_eq t ty); try discriminate. subst; reflexivity.
Qed.
Definition ilh_mario_head args := match args with
| Etempvar id ty :: _ => Pos.eqb id IBM._m &&
    (if type_eq ty ill_mario_pointer then true else false)
| _ => false end.
Lemma ilh_mario_head_exact : forall args, ilh_mario_head args = true ->
  exists rest, args = Etempvar IBM._m ill_mario_pointer :: rest.
Proof.
  intros [|head rest]; try discriminate. destruct head; try discriminate.
  cbn [ilh_mario_head]. intro H. apply andb_true_iff in H as [Hid Hty].
  apply Pos.eqb_eq in Hid. destruct (type_eq t ill_mario_pointer); try discriminate.
  subst. eexists; reflexivity.
Qed.

Lemma ilh_actual_named_call : forall version kind e le m opt args tys ret t le' m' out,
  e ! (ill_ident kind) = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Scall opt (Evar (ill_ident kind) (Tfunction tys ret cc_default)) args)
    t le' m' out ->
  exists values result,
    eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m args tys values /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ill_body version kind)) values t m' result.
Proof.
  intros version kind e le m opt args tys ret t le' m' out Hlocal Hrun.
  inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (ill_selected_helpers_resolve version kind) as (fb & Hsymbol & Hfunction).
  lazymatch goal with Hr : eval_expr _ _ _ _ (Evar _ _) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  eauto.
Qed.

Lemma ilh_actual_mario_arguments : forall ge e le m args types values mb mo,
  le ! IBM._m = Some (Vptr mb mo) ->
  eval_exprlist ge e le m (Etempvar IBM._m ill_mario_pointer :: args)
    (ill_mario_pointer :: types) values ->
  exists rest, values = Vptr mb mo :: rest.
Proof.
  intros ge e le m args types values mb mo Hm Hargs.
  inversion Hargs; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._m _) ?v |- _ =>
    assert (v = Vptr mb mo) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr mb mo) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  eexists; reflexivity.
Qed.

Definition ilh_argument kind := match kind with ILLoad => us_memory._list | _ => IBM._m end.
Lemma ilh_actual_helper_entry : forall version kind m mb mo args t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ill_body version kind)) (Vptr mb mo :: args) t m' result ->
  exists entry_le final_le out,
    entry_le ! (ilh_argument kind) = Some (Vptr mb mo) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env entry_le m
      (fn_body (ill_body version kind)) t final_le m' out.
Proof.
  intros version kind m mb mo args t m' result Hcall.
  destruct (ill_empty_locals_and_original_argument version kind) as [Hvars _].
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?after |- _ =>
    change (Some before = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! (ilh_argument kind) = Some (Vptr mb mo)) as Hm
      by (destruct version, kind; destruct args as [|a [|b [|c tail]]];
        cbn in Hbind; try discriminate; inversion Hbind; reflexivity) end.
  eauto.
Qed.
