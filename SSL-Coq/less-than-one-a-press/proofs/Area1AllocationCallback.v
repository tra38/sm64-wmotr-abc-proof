(** The allocator's full-pool lookup is a real read-only callback, not an
    assumed frame. It chooses list 12's first node; list ownership is still
    needed to exclude Mario as that node. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
 Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1AllocationSource
 Area1AllocationInitialization Area1AllocationSlotFrame Area1SlotWriteCheck Area1AllocationChoice Area1PostCopyParticleExecution
 OrdinaryArea1EntryMemory InkBackwardExecution ContactConsumerExecution
 ObjectContactNecessity SecretContactExecution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma paf_finder_checked : forall version,
 fn_vars (pas_body version PAFind) = [] /\
 cce_readonly_keep PAS._objList (fn_body (pas_body version PAFind)) = true.
Proof. intros []; split; reflexivity. Qed.

Theorem paf_complete_finder_preserves_memory : forall version m args t after result,
 ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
   m (Internal (pas_body version PAFind)) args t after result -> t = E0 /\ after = m.
Proof.
 intros version m args t after result Hcall.
 destruct (paf_finder_checked version) as [Hvars Hshape].
 inversion Hcall; subst.
 match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
 match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ => rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
 match goal with Hf : Mem.free_list ?m (blocks_of_env _ empty_env) = Some ?last |- _ =>
   change (Some m = Some last) in Hf; inversion Hf; subst end.
 match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
   destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hr Hshape) as [Ht [Hm _]]; auto end.
Qed.

Definition paf_finder_call version := match fn_body (pas_body version PAAllocate) with
| Ssequence _ (Ssequence
    (Sifthenelse _ (Ssequence (Ssequence call _) _) _) _) => call
| _ => Sskip end.
Lemma paf_finder_call_generated : forall version,
 paf_finder_call version = Scall (Some PAS._t'2)
  (Evar (pas_ident PAFind) (Tfunction [] (tptr (Tstruct PAS._Object noattr)) cc_default)) [].
Proof. intros []; reflexivity. Qed.

Theorem paf_reached_finder_preserves_memory : forall version le m t le' after out,
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (paf_finder_call version) t le' after out -> t = E0 /\ after = m.
Proof.
 intros version le m t le' after out Hrun. rewrite paf_finder_call_generated in Hrun. inversion Hrun; subst.
 destruct (pas_selected_helpers_resolve version PAFind) as (fb & Hsymbol & Hfunction).
 match goal with Hr : eval_expr ?ge ?e ?le ?m (Evar ?id (Tfunction ?ps ?r ?cc)) ?v |- _ =>
   assert (v = Vptr fb Ptrofs.zero) by
     (eapply sce_function_name_value; [apply PTree.gempty|exact Hsymbol|exact Hr]); subst v end.
 match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
   change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
   rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
 eapply paf_complete_finder_preserves_memory; eauto.
Qed.

Definition paf_allocate_choice version := match fn_body (pas_body version PAAllocate) with
| Ssequence _ (Ssequence choice _) => choice | _ => Sskip end.
Definition paf_allocate_prefix version := match fn_body (pas_body version PAAllocate) with
| Ssequence prefix _ => prefix | _ => Sskip end.

Lemma paf_spin_has_no_completed_execution : forall ge e le m t le' after out,
 ~ ocn_exec ge e le m (Sloop Sskip Sskip) t le' after out.
Proof.
 intros ge e le m t le' after out Hrun.
 remember (Sloop Sskip Sskip) as s eqn:E in Hrun.
 induction Hrun; inversion E; subst; clear E;
   repeat match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
     inversion Hr; subst; clear Hr end; auto; try contradiction.
 all: try discriminate.
 all: try match goal with Hbad : out_break_or_return Out_normal _ |- _ => inversion Hbad end.
 all: auto.
Qed.

Lemma paf_choice_finishes_normally : forall version le m t le' after out,
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (paf_allocate_choice version) t le' after out -> out = Out_normal.
Proof.
 intros version le m t le' after out Hrun.
 assert (paf_allocate_choice version = paf_allocate_choice VersionUS) as E by (destruct version; reflexivity).
 rewrite E in Hrun. cbv [paf_allocate_choice pas_body PAS.f_allocate_object fn_body] in Hrun.
 unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
 cce_unroll_loop_free_exec.
 all: repeat match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ =>
   inversion Hc; subst; clear Hc end.
 all: try reflexivity; try contradiction.
 all: exfalso; eapply paf_spin_has_no_completed_execution; eauto.
Qed.

(** This cut really is reached from allocate_object. Initialization is
    framed only from this point; list repair and eviction precede it. *)
Theorem paf_actual_allocator_reaches_initializer : forall version le m t le' after out,
 ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
   (fn_body (pas_body version PAAllocate)) t le' after out ->
 exists init_le init_m pre suffix,
   t = pre ++ suffix /\
   ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env init_le init_m
     (pai_initializer version) suffix le' after out /\
   (forall ob oo mb, init_le ! PAS._obj = Some (Vptr ob oo) -> mb <> ob ->
     forall chunk offset, Mem.load chunk after mb offset = Mem.load chunk init_m mb offset).
Proof.
 intros version le m t le' after out Hrun.
 assert (fn_body (pas_body version PAAllocate) = Ssequence (paf_allocate_prefix version)
   (Ssequence (paf_allocate_choice version) (pai_initializer version))) as Hbody
   by (destruct version; reflexivity).
 assert (ibk_normal (paf_allocate_prefix version) = true) as Hnormal by (destruct version; reflexivity).
 rewrite Hbody in Hrun.
 destruct (ibk_split_sequence _ _ _ _ (paf_allocate_prefix version) _ _ _ _ _ Hnormal Hrun)
   as (ll & mm & tt & ts & Et & Hp & Hrest).
 inversion Hrest; subst.
 - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _ (paf_allocate_choice _) ?pre _ _ _,
     Hinit : ClightBigstep.exec_stmt _ _ _ ?init_le ?init_m (pai_initializer _) ?suffix _ _ _ |- _ =>
     exists init_le, init_m, (tt ++ pre), suffix end.
   split; [apply app_assoc|].
   split; [eassumption|]. intros. eapply pai_actual_initializer_frames_state; eauto.
 - match goal with Hchoice : ClightBigstep.exec_stmt _ _ _ _ _ (paf_allocate_choice _) _ _ _ _ |- _ =>
     pose proof (paf_choice_finishes_normally _ _ _ _ _ _ _ Hchoice); contradiction end.
Qed.

(** This package keeps the proved pieces separate from live free/active
    ownership, earlier list effects and the rest of the scheduler. *)
Record Area1PostCopyAllocationCheckedBoundary : Prop := {
 pca_copy_boundary : Area1PostCopyParticleCheckedBoundary;
 pca_initializer_same_pool_frame : forall version le m ob slot t le' after out,
   (slot < object_pool_capacity)%nat ->
   le ! PAS._obj = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
   ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
     (pai_initializer version) t le' after out -> asw_frame ob slot m after;
 pca_nonempty_slot_origin : forall version m dest fb fo ob oo t after result,
   Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) = Some (Vptr ob oo) ->
   ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
     m (Internal (pas_body version PATry)) [dest;Vptr fb fo] t after result -> result = Vptr ob oo;
 pca_free_active_separation : forall version m dest fb fo ob child mario flags t after result,
   Mem.load Mint32 m fb (Ptrofs.unsigned (Ptrofs.add fo (Ptrofs.repr 96))) =
     Some (Vptr ob (Ptrofs.repr (object_slot_offset child))) ->
   Mem.load Mint16signed m ob (object_slot_offset child + object_active_flags_offset) = Some (Vint Int.zero) ->
   Mem.load Mint16signed m ob (object_slot_offset mario + object_active_flags_offset) = Some (Vint flags) ->
   flags <> Int.zero ->
   ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
     m (Internal (pas_body version PATry)) [dest;Vptr fb fo] t after result ->
   child <> mario /\ result = Vptr ob (Ptrofs.repr (object_slot_offset child));
 pca_initializer_execution_cut : forall version le m t le' after out,
   ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
     (fn_body (pas_body version PAAllocate)) t le' after out ->
   exists init_le init_m pre suffix,
     t = pre ++ suffix /\
     ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env init_le init_m
       (pai_initializer version) suffix le' after out /\
     (forall ob oo mb, init_le ! PAS._obj = Some (Vptr ob oo) -> mb <> ob ->
       forall chunk offset, Mem.load chunk after mb offset = Mem.load chunk init_m mb offset);
 pca_eviction_lookup_has_no_effect : forall version le m t le' after out,
   ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
     (paf_finder_call version) t le' after out -> t = E0 /\ after = m
}.

Theorem area1_postcopy_allocation_checked_boundary_holds : Area1PostCopyAllocationCheckedBoundary.
Proof.
 constructor.
 - exact area1_postcopy_particle_checked_boundary_holds.
 - exact asf_actual_initializer_frames_other_slots.
 - exact pac_try_call_result_origin.
 - exact pac_free_head_flags_exclude_mario.
 - exact paf_actual_allocator_reaches_initializer.
 - exact paf_reached_finder_preserves_memory.
Qed.
