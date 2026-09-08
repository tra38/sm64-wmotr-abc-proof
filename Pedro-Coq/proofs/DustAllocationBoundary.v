From Coq Require Import List ZArith.
From compcert Require Import Archi AST Clight ClightBigstep Clightdefs Cop
  Ctypes Events Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import us_memory jp_memory us_object_helpers jp_object_helpers.
From Pedro.Proofs Require Import GameTypes SegmentedPointerBoundary TTCCogExecution.
Import ListNotations.

Definition dust_segment_function version : function :=
  match version with VersionUS => us_memory.f_segmented_to_virtual
  | VersionJP => jp_memory.f_segmented_to_virtual end.
Definition dust_origin_function version : function :=
  match version with VersionUS => us_object_helpers.f_spawn_object_at_origin
  | VersionJP => jp_object_helpers.f_spawn_object_at_origin end.

(** Lift the existing expression obstruction to the COMPLETE generated call.
    This is a property of standard CompCert's symbolic-pointer semantics, not
    an assertion that the corresponding retail game call fails. *)
Theorem generated_segmented_call_cannot_execute_from_symbolic_pointer_us_jp :
  forall version ge before after b offset trace result,
    ~ eval_funcall function_entry2 ge before (Internal (dust_segment_function version))
      [Vptr b offset] trace after result.
Proof.
  intros version ge before after b offset trace result Hcall.
  destruct version; cbn [dust_segment_function] in Hcall.
  all: inversion Hcall; subst; clear Hcall.
  all: match goal with
    | Hentry : function_entry2 _ _ _ _ _ _ _ |- _ => inversion Hentry; subst
    end.
  all: match goal with
    | Hparams : bind_parameter_temps _ _ _ = Some _ |- _ =>
        cbn [fn_params fn_temps bind_parameter_temps create_undef_temps] in Hparams;
        inversion Hparams; subst; clear Hparams
    end.
  all: match goal with
    | Hbody : exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
        cbn [fn_body] in Hbody; inversion Hbody; subst; clear Hbody
    end.
  all: match goal with
    | Hset : exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _ =>
        inversion Hset; subst; clear Hset
    end.
  all: eapply segment_index_expression_cannot_eval_from_vptr; [| eassumption].
  all: cbn; reflexivity.
Qed.

Lemma dust_global_function_value :
  forall (ge : Clight.genv) environment locals memory id args ret cc code value,
    environment ! id = None ->
    Genv.find_symbol ge id = Some code ->
    eval_expr ge environment locals memory (Evar id (Tfunction args ret cc)) value ->
    value = Vptr code Ptrofs.zero.
Proof.
  intros ge environment locals memory id args ret cc code value Hlocal Hsymbol Heval.
  inversion Heval; subst.
  match goal with Hlv : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hlv; subst end;
    try congruence.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst end;
    try discriminate; congruence.
Qed.

Lemma dust_behavior_argument_value :
  forall ge environment locals memory id b offset args,
    locals ! id = Some (Vptr b offset) ->
    eval_exprlist ge environment locals memory [Etempvar id (tptr tuint)]
      [tptr tvoid] args -> args = [Vptr b offset].
Proof.
  intros ge environment locals memory id b offset args Hbinding Hargs.
  inversion Hargs; subst.
  match goal with Hnil : eval_exprlist _ _ _ _ [] [] _ |- _ => inversion Hnil; subst end.
  match goal with Htemp : eval_expr _ _ _ _ (Etempvar _ _) ?loaded |- _ =>
    pose proof (eval_tempvar_binding _ _ _ _ _ _ _ Htemp);
    assert (loaded = Vptr b offset) by congruence; subst loaded
  end.
  cbn in *. congruence.
Qed.

Definition dust_allocation_symbolic_boundary_claim : Prop :=
  forall version (ge : Clight.genv) before after parent unused model behavior offset code trace result,
    Genv.find_symbol ge us_object_helpers._segmented_to_virtual = Some code ->
    Genv.find_funct_ptr ge code = Some (Internal (dust_segment_function version)) ->
    ~ eval_funcall function_entry2 ge before (Internal (dust_origin_function version))
      [parent; unused; model; Vptr behavior offset] trace after result.

(** No object/free-list assumptions are involved: the failure occurs before
    create_object. Both bindings below name the actual generated callee. *)
Theorem generated_spawn_origin_cannot_execute_from_symbolic_behavior_us_jp :
  dust_allocation_symbolic_boundary_claim.
Proof.
  intros version ge before after parent unused model behavior offset code trace result
    Hsymbol Hcode Hcall.
  destruct version; cbn [dust_origin_function] in Hcall.
  all: inversion Hcall; subst; clear Hcall.
  all: match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst end.
  all: match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    cbn [fn_vars] in Halloc; inversion Halloc; subst; clear Halloc end.
  all: match goal with Hparams : bind_parameter_temps _ _ _ = Some _ |- _ =>
    cbn [fn_params fn_temps bind_parameter_temps create_undef_temps] in Hparams;
    inversion Hparams; subst; clear Hparams end.
  all: match goal with Hbody : exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    cbn [fn_body] in Hbody; inversion Hbody; subst; clear Hbody end.
  all: match goal with Hseq : exec_stmt _ _ _ _ _ (Ssequence (Scall _ _ _) _) _ _ _ _ |- _ =>
    inversion Hseq; subst; clear Hseq end.
  all: match goal with Hcall : exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ =>
    inversion Hcall; subst; clear Hcall end.
  all: match goal with
    Hfun : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (Hfun_value : vf = Vptr code Ptrofs.zero) by
      (eapply dust_global_function_value; [| exact Hsymbol | exact Hfun]; reflexivity);
    subst vf
    end.
  all: match goal with Hclass : classify_fun _ = _ |- _ => inversion Hclass; subst end.
  all: match goal with Hargs : eval_exprlist _ _ _ _ _ _ ?args |- _ =>
    assert (Harg_value : args = [Vptr behavior offset]) by
      (eapply dust_behavior_argument_value; [| exact Hargs]; cbn; reflexivity);
    subst args end.
  all: match goal with Hfind : Genv.find_funct _ (Vptr _ Ptrofs.zero) = Some ?fd |- _ =>
    rewrite (cog_find_funct_zero _ _ _ Hcode) in Hfind;
    inversion Hfind; subst fd end.
  all: match type of Hcode with
    | Genv.find_funct_ptr _ _ = Some (Internal (dust_segment_function ?selectedVersion)) =>
      eapply generated_segmented_call_cannot_execute_from_symbolic_pointer_us_jp
        with (version := selectedVersion); eassumption
    end.
Qed.
