(** Both writes of the real sink call, with their destinations derived. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkQuicksandSource
  InkQuicksandExpressions InkBackwardExecution InkFloorResetExecution
  ObjectContactNecessity ContactConsumerExecution OrdinaryArea1EntryMemory
  InkRawCopyStores SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem iq_matrix_branch_actual_store :
  forall version e le m ob oo qb qo t le' m' out,
  le ! IQ._o = Some (Vptr ob oo) ->
  Mem.load Mint32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 80))) = Some (Vptr qb qo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iq_matrix_branch version) t le' m' out ->
  exists written,
    Mem.store Mfloat32 m qb (Ptrofs.unsigned (Ptrofs.add qo (Ptrofs.repr 52))) written = Some m' /\
    t = E0 /\ out = Out_normal.
Proof.
  intros version e le m ob oo qb qo t le' m' out Ho Hload Hrun.
  destruct (iq_generated_cuts version) as (_ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: repeat match goal with Hr : eval_expr _ _ ?temps _ iq_matrix ?value |- _ =>
    assert (temps ! IQ._o = Some (Vptr ob oo)) as HoNow
      by (repeat rewrite PTree.gso by discriminate; exact Ho);
    assert (value = Vptr qb qo) by (eapply iq_matrix_read; eauto); subst value; clear Hr HoNow end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ (iq_matrix_y IQ._t'4) _ _ _ |- _ =>
    assert (temps ! IQ._t'4 = Some (Vptr qb qo)) as Htarget
      by (repeat rewrite PTree.gso by discriminate; apply PTree.gss);
    destruct (iq_matrix_y_location _ _ _ _ _ _ _ _ _ _ Htarget Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  eexists. split; [eassumption|]. split; reflexivity.
Qed.

Theorem iq_display_tail_actual_store :
  forall version e le m mb mo ob oo height depth t le' m' out,
  le ! IQ._m = Some (Vptr mb mo) -> le ! IQ._o = Some (Vptr ob oo) ->
  Mem.load Mfloat32 m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 192))) = Some (Vsingle depth) ->
  Mem.load Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36))) = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iq_display_tail version) t le' m' out ->
  Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 36)))
    (Vsingle (Float32.sub height depth)) = Some m' /\ t = E0 /\ out = Out_normal.
Proof.
  intros version e le m mb mo ob oo height depth t le' m' out Hm Ho Hd Hy Hrun.
  destruct (iq_generated_cuts version) as (_ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ iq_y ?value |- _ =>
    pose proof (iq_graphics_y_read _ _ _ _ _ _ _ _ Ho Hy Hr) as Hvalue; subst value end.
  all: match goal with Hr : eval_expr _ _ ?temps _ iq_depth ?value |- _ =>
    assert (temps ! IQ._m = Some (Vptr mb mo)) as HmNow
      by (rewrite PTree.gso by discriminate; exact Hm);
    pose proof (iq_depth_read _ _ _ _ _ _ _ _ HmNow Hd Hr) as Hvalue; subst value end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ ?temps _ iq_y _ _ _ |- _ =>
    assert (temps ! IQ._o = Some (Vptr ob oo)) as HoNow
      by (repeat rewrite PTree.gso by discriminate; exact Ho);
    destruct (iq_graphics_y_location _ _ _ _ _ _ _ _ _ HoNow Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Ebinop Osub _ _ _) _ |- _ => inversion Hr; subst end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end].
  repeat match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inversion Hr; subst; clear Hr end.
  all: try solve [match goal with Hbad : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Hbad end].
  repeat match goal with Htemp : (PTree.set _ _ _) ! _ = Some _ |- _ =>
    first [rewrite PTree.gss in Htemp | rewrite PTree.gso in Htemp by discriminate];
    try (inversion Htemp; subst; clear Htemp) end.
  match goal with Hsem : sem_binary_operation _ Osub _ _ _ _ _ = Some _ |- _ =>
    cbn in Hsem; inversion Hsem; subst end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split; [assumption|]. split; reflexivity.
Qed.

Definition iq_optional_pointer (matrix : option (block * ptrofs)) : val :=
  match matrix with None => Vnullptr | Some (b, ofs) => Vptr b ofs end.
Definition iq_matrix_storage_separate mb ob slot (matrix : option (block * ptrofs)) : Prop :=
  match matrix with
  | None => True
  | Some (qb, qo) => qb <> mb /\
      (qb <> ob \/ Ptrofs.unsigned (Ptrofs.add qo (Ptrofs.repr 52)) + 4 <= object_slot_offset slot \/
        object_slot_offset slot + 184 <= Ptrofs.unsigned (Ptrofs.add qo (Ptrofs.repr 52)))
  end.
Definition iq_protected_read (mb ob : block) slot chunk b ofs : Prop :=
  b = mb \/ (b = ob /\ object_slot_offset slot <= ofs /\
    ofs + size_chunk chunk <= object_slot_offset slot + 184).
Definition iq_matrix_frame mb ob slot m m' := forall chunk b ofs,
  iq_protected_read mb ob slot chunk b ofs -> Mem.load chunk m' b ofs = Mem.load chunk m b ofs.

Lemma iq_matrix_store_frame : forall m m' mb ob slot qb qo written,
  iq_matrix_storage_separate mb ob slot (Some (qb, qo)) ->
  Mem.store Mfloat32 m qb (Ptrofs.unsigned (Ptrofs.add qo (Ptrofs.repr 52))) written = Some m' ->
  iq_matrix_frame mb ob slot m m'.
Proof.
  intros m m' mb ob slot qb qo written [Hm Ho] Hstore chunk b ofs Hread.
  eapply Mem.load_store_other; [exact Hstore|].
  destruct Hread as [->|[-> [Hlo Hhi]]]; [left; congruence|].
  destruct Ho as [Hblock|[Hbelow|Habove]]; [left; congruence|right; right; cbn; lia|right; left; cbn; lia].
Qed.
