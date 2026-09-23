(** The real allocator initializer is confined to its selected Object slot.
    The spawned object may be a particle; it is not a second Mario. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1SlotExpressions
 Area1SlotWriteCheck Area1AllocationSource Area1AllocationInitialization
 InkBackwardExecution InkFloorResetExecution InkPlatformWriteFrame
 ObjectContactNecessity SecretContactExecution ContactConsumerExecution
 EyerokRank15LiveMovement OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition asf_matrix_env : ase_env := [(PAM._mtx,ASEptr (Ptrofs.repr 540))].
Definition asf_no_calls (_ : ase_env) (_ : expr) (_ : list expr) := false.

Lemma asf_matrix_checked : forall version, exists last,
 asw_check 100 (prog_comp_env (selected_clight_target version)) asf_no_calls
   asf_matrix_env (fn_body (pas_body version PAIdentity)) = Some (last,ASWnormal).
Proof.
 intro version. rewrite <- rank15_selected_header_environment_exact.
 destruct version; eexists; vm_compute; reflexivity.
Qed.

Theorem asf_matrix_frames_other_slots : forall version m ob slot t after result,
 (slot < object_pool_capacity)%nat ->
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PAIdentity))
   [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 540))]
   t after result -> asw_frame ob slot m after.
Proof.
 intros version m ob slot t after result Hslot Hcall.
 destruct (pai_matrix_checked version) as (Hvars & Hparams & _).
 inversion Hcall; subst.
 match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
 match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
 match goal with Hf : Mem.free_list ?m (blocks_of_env _ empty_env) = Some ?last |- _ =>
   change (Some m = Some last) in Hf; inversion Hf; subst end.
 match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
   rewrite Hparams in Hb; cbn [bind_parameter_temps] in Hb; inversion Hb; subst temps end.
 destruct (asf_matrix_checked version) as (last & Hcheck).
 match goal with Hr : ClightBigstep.exec_stmt _ _ _ ?le _ _ _ _ _ _ |- _ =>
   assert (ase_context ob (Ptrofs.repr (object_slot_offset slot)) asf_matrix_env le) as Hctx;
   [ | exact (proj1 (asw_check_sound _ _ ob slot asf_no_calls Hslot
     ltac:(intros; discriminate) _ _ _ _ _ _ _ Hr 100 asf_matrix_env last ASWnormal Hcheck Hctx)) ] end.
 intros id x Hget. cbn [asf_matrix_env ase_get] in Hget.
 destruct (Pos.eqb id PAM._mtx) eqn:E; try discriminate.
 apply Pos.eqb_eq in E; subst. inversion Hget; subst. apply PTree.gss.
Qed.

Definition asf_matrix_call ce ae fn args := match fn,args with
| Evar id (Tfunction _ _ _), [arg] =>
 Pos.eqb id (pas_ident PAIdentity) &&
 match fst (ase_eval ce ae arg) with
 | Some (ASEptr delta) => Ptrofs.eq delta (Ptrofs.repr 540) | _ => false end
| _,_ => false end.

Lemma asf_matrix_reached_frame : forall version ae le m fn args ob slot t le' after out,
 (slot < object_pool_capacity)%nat ->
 ase_context ob (Ptrofs.repr (object_slot_offset slot)) ae le ->
 asf_matrix_call (Clight.globalenv (selected_clight_target version)) ae fn args = true ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (Scall None fn args) t le' after out -> asw_frame ob slot m after.
Proof.
 intros version ae le m fn args ob slot t le' after out Hslot Hctx Hcheck Hrun.
 destruct fn; try discriminate. destruct t0; try discriminate.
 destruct args as [|arg rest]; try discriminate. destruct rest; try discriminate.
 cbn [asf_matrix_call] in Hcheck. apply andb_true_iff in Hcheck as [Hid Harg].
 apply Pos.eqb_eq in Hid. subst i.
 destruct (fst (ase_eval _ ae arg)) as [[number|delta]|] eqn:E; try discriminate.
 apply Ptrofs.same_if_eq in Harg. subst delta.
 inversion Hrun; subst.
 destruct (pas_selected_helpers_resolve version PAIdentity) as (fb & Hsymbol & Hfunction).
 match goal with Hr : eval_expr ?ge ?e ?le ?m (Evar ?id (Tfunction ?ps ?r ?cc)) ?v |- _ =>
   assert (v = Vptr fb Ptrofs.zero) by
     (eapply sce_function_name_value; [apply PTree.gempty|exact Hsymbol|exact Hr]); subst v end.
 match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
   change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
   rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
 match goal with Hty : type_of_fundef _ = _ |- _ =>
   assert (type_of_fundef (Internal (pas_body version PAIdentity)) =
     Tfunction [tptr (tarray tfloat 4)] tvoid cc_default) as Et by (destruct version; reflexivity);
   rewrite Et in Hty; inversion Hty; subst end.
 repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
 match goal with Hr : eval_expr _ _ _ _ arg ?v |- _ =>
   pose proof (proj1 (ase_eval_sound _ _ _ _ _ _ _ Hctx) _ _ Hr _ E) as Ev;
   cbn [ase_denote] in Ev; subst v end.
 match goal with Hcast : sem_cast (Vptr _ _) _ (tptr (tarray tfloat 4)) _ = Some _ |- _ =>
   destruct (typeof arg);
   cbn in Hcast; try discriminate; inversion Hcast; subst end.
 all: eapply (asf_matrix_frames_other_slots version); eauto.
Qed.

Definition asf_initial_env : ase_env := [(PAS._obj,ASEptr Ptrofs.zero)].
Lemma asf_initializer_checked : forall version, exists last,
 asw_check 150 (prog_comp_env (selected_clight_target version))
   (asf_matrix_call (prog_comp_env (selected_clight_target version)))
   asf_initial_env (pai_initializer version) = Some (last,ASWreturn) /\
 ase_get PAS._obj last = Some (ASEptr Ptrofs.zero).
Proof.
 intro version. rewrite <- rank15_selected_header_environment_exact.
 destruct version; eexists; split; vm_compute; reflexivity.
Qed.

Theorem asf_actual_initializer_frames_other_slots : forall version le m ob slot t le' after out,
 (slot < object_pool_capacity)%nat ->
 le ! PAS._obj = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (pai_initializer version) t le' after out -> asw_frame ob slot m after.
Proof.
 intros version le m ob slot t le' after out Hslot Hobj Hrun.
 destruct (asf_initializer_checked version) as (last & Hcheck & Hfinal).
 assert (ase_context ob (Ptrofs.repr (object_slot_offset slot)) asf_initial_env le) as Hctx.
 2: exact (proj1 (asw_check_sound _ _ ob slot _ Hslot
   ltac:(intros; eapply asf_matrix_reached_frame; eauto)
   _ _ _ _ _ _ _ Hrun 150 asf_initial_env last ASWreturn Hcheck Hctx)).
 intros id x Hget. cbn [asf_initial_env ase_get] in Hget.
 destruct (Pos.eqb id PAS._obj) eqn:E; try discriminate.
 apply Pos.eqb_eq in E; subst. inversion Hget; subst.
 cbn [ase_denote]. rewrite Ptrofs.add_zero. exact Hobj.
Qed.

Lemma asw_distinct_slot_frame : forall ob child mario before after,
 child <> mario -> asw_frame ob child before after ->
 forall chunk offset, 0 <= offset -> offset + size_chunk chunk <= object_size ->
 Mem.load chunk after ob (object_slot_offset mario + offset) =
 Mem.load chunk before ob (object_slot_offset mario + offset).
Proof.
 intros ob child mario before after Hne Hframe chunk offset Hlo Hhi.
 apply Hframe. unfold asw_outside.
 destruct (distinct_object_slot_intervals_are_disjoint child mario Hne);
  [right; right; lia|right; left; lia].
Qed.
