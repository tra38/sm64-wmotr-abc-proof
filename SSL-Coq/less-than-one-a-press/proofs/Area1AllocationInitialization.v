(** The real allocate_object initializer, including its reached matrix
    helper, preserves every separate memory block. Same-pool slot bounds
    and the earlier list/graph/eviction segment remain separate obligations. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1AllocationSource
 Area1AllocationBlockFrame InkPlatformWriteFrame InkFloorResetExecution
 InkBackwardExecution ObjectContactNecessity SecretContactExecution
 ContactConsumerExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Module PAM := us_math_util.

Definition pai_initializer version := match fn_body (pas_body version PAAllocate) with
| Ssequence _ (Ssequence _ init) => init | _ => Sskip end.
Definition pai_matrix_temps := [PAM._mtx;PAM._dest].

Lemma pai_matrix_checked : forall version,
 fn_vars (pas_body version PAIdentity) = [] /\
 fn_params (pas_body version PAIdentity) = [(PAM._mtx,tptr (tarray tfloat 4))] /\
 pab_shape pai_matrix_temps (fun _ _ => false) (fn_body (pas_body version PAIdentity)) = true.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

Theorem pai_matrix_call_frames_other_blocks : forall version m arg t after result mb,
 ipw_value_safe mb arg ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PAIdentity)) [arg] t after result ->
 ipw_frame mb m after.
Proof.
 intros version m arg t after result mb Harg Hcall.
 destruct (pai_matrix_checked version) as (Hvars & Hparams & Hshape).
 inversion Hcall; subst.
 match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
 match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
 match goal with Hf : Mem.free_list ?m (blocks_of_env _ empty_env) = Some ?last |- _ =>
   change (Some m = Some last) in Hf; inversion Hf; subst end.
 assert (ipw_inputs_safe pai_matrix_temps mb (fn_params (pas_body version PAIdentity)) [arg]) as Hinputs.
 { unfold ipw_inputs_safe. rewrite Hparams. constructor; [intros _; exact Harg|constructor]. }
 match goal with Hb : bind_parameter_temps _ _ _ = Some ?le |- _ =>
   pose proof (ipw_bind_safe _ _ _ _ Hinputs _ _ Hb (ipw_undef_safe _ _ _)) as Htemps end.
 match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
   exact (proj1 (pab_checked_frame _ _ mb pai_matrix_temps (fun _ _ => false) ltac:(intros; discriminate) _ _ _ _ _ _ _ Hr Hshape Htemps)) end.
Qed.

Definition pai_matrix_call_ok temps fn args := match fn,args with
| Evar id (Tfunction _ _ _), [arg] => Pos.eqb id (pas_ident PAIdentity) && pab_safe_expr temps arg
| _,_ => false end.

Lemma pai_matrix_reached_frame : forall version temps le m fn args t le' after out mb,
 pab_temps le mb temps -> pai_matrix_call_ok temps fn args = true ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (Scall None fn args) t le' after out -> ipw_frame mb m after.
Proof.
 intros version temps le m fn args t le' after out mb Hctx Hshape Hrun.
 destruct fn; try discriminate. destruct t0; try discriminate.
 destruct args as [|arg rest]; try discriminate. destruct rest; try discriminate.
 cbn [pai_matrix_call_ok] in Hshape. apply andb_true_iff in Hshape as [Hid Harg].
 apply Pos.eqb_eq in Hid. subst i.
 inversion Hrun; subst.
 destruct (pas_selected_helpers_resolve version PAIdentity) as (fb & Hsymbol & Hfunction).
 match goal with Hr : eval_expr ?ge ?e ?le ?m (Evar ?id (Tfunction ?ps ?r ?cc)) ?v |- _ =>
   assert (v = Vptr fb Ptrofs.zero) by
     (eapply sce_function_name_value; [apply PTree.gempty|exact Hsymbol|exact Hr]); subst v end.
 match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
   change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
   rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
 repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
 eapply pai_matrix_call_frames_other_blocks; [|eassumption].
 intros b ofs E.
 match goal with Hcast : sem_cast _ _ _ _ = Some ?v |- _ =>
   assert (v = Vptr b ofs) by exact E; subst v;
   pose proof (ipw_cast_keeps_block _ _ _ _ _ _ Hcast) as Ev end.
 eapply pab_expr_safe; [exact Harg|exact Hctx|eassumption|exact Ev].
Qed.

Lemma pai_initializer_checked : forall version,
 pab_shape [PAS._obj] (pai_matrix_call_ok [PAS._obj]) (pai_initializer version) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem pai_actual_initializer_frames_state : forall version le m ob oo mb t le' after out,
 le ! PAS._obj = Some (Vptr ob oo) -> mb <> ob ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pai_initializer version) t le' after out -> ipw_frame mb m after.
Proof.
 intros version le m ob oo mb t le' after out Hobj Hne Hrun.
 assert (pab_temps le mb [PAS._obj]) as Htemps.
 { intros id b ofs [E|Hbad] Hread; [subst; congruence|contradiction]. }
 exact (proj1 (pab_checked_frame _ _ mb [PAS._obj] (pai_matrix_call_ok [PAS._obj])
   ltac:(intros; eapply pai_matrix_reached_frame; eauto) _ _ _ _ _ _ _ Hrun
   (pai_initializer_checked version) Htemps)).
Qed.
