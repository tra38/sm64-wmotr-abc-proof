(** Aggregate fields retain the block of their remembered object/buffer
    pointer. Scalar animation stores in a different block cannot alter the
    MarioState timer, irrespective of the stored value. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkLandingHistoryGate ObjectContactNecessity.
Import ListNotations.
Import Clightdefs.ClightNotations.

Fixpoint iad_aggregate_root (a : expr) : option ident := match a with
| Ederef (Etempvar id _) (Tstruct _ _) => Some id
| Efield base _ (Tstruct _ _) => iad_aggregate_root base
| _ => None end.

Lemma iad_aggregate_block : forall a ge e le m id b ofs v,
  iad_aggregate_root a = Some id -> le ! id = Some (Vptr b ofs) ->
  eval_expr ge e le m a v -> exists offset, v = Vptr b offset.
Proof.
  induction a; intros ge e le m root object_block object_ofs v Hroot Htemp Hread;
    cbn [iad_aggregate_root] in Hroot; try discriminate.
  - destruct a; try discriminate. destruct t; try discriminate.
    inversion Hroot; subst root.
    inversion Hread; subst.
    match goal with Hl : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ =>
      inversion Hl; subst end.
    match goal with Ht : eval_expr _ _ _ _ (Etempvar _ _) ?value |- _ =>
      assert (value = Vptr object_block object_ofs) as Heq by (eapply ocn_temp_value; eauto);
      inversion Heq; subst end.
    match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
      inversion Hd; subst; try discriminate end.
    eexists; reflexivity.
  - destruct t; try discriminate.
    inversion Hread; subst.
    match goal with Hl : eval_lvalue _ _ _ _ (Efield _ _ _) _ _ _ |- _ =>
      inversion Hl; subst end.
    all: lazymatch type of Hroot with iad_aggregate_root ?base = Some _ =>
      match goal with Hr : eval_expr _ _ _ _ base ?value |- _ =>
        destruct (IHa _ _ _ _ root object_block object_ofs value Hroot Htemp Hr) as [offset Heq];
        inversion Heq; subst end end.
    all: match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
      inversion Hd; subst; try discriminate end.
    all: try solve [match goal with Hbit : load_bitfield _ _ _ _ _ _ _ _ |- _ => inversion Hbit end].
    all: eexists; reflexivity.
Qed.

Definition iad_write_root lhs := match lhs with
| Efield base _ ty => match access_mode ty with
    | By_value _ => iad_aggregate_root base | _ => None end
| _ => None end.

Lemma iad_scalar_destination_block : forall ge e le m lhs id b ofs loc offset bf,
  iad_write_root lhs = Some id -> le ! id = Some (Vptr b ofs) ->
  eval_lvalue ge e le m lhs loc offset bf -> loc = b.
Proof.
  intros ge e le m lhs id b ofs loc offset bf Hroot Htemp Hl.
  destruct lhs; cbn [iad_write_root] in Hroot; try discriminate.
  destruct (access_mode t); try discriminate.
  inversion Hl; subst.
  all: lazymatch type of Hroot with iad_aggregate_root ?base = Some _ =>
    match goal with Hr : eval_expr _ _ _ _ base ?value |- _ =>
      destruct (iad_aggregate_block base _ _ _ _ id b ofs value Hroot Htemp Hr)
        as [aggregate_offset Hpointer]; inversion Hpointer; subst; reflexivity end end.
Qed.

Lemma iad_other_block_assignment : forall ge e le m lhs rhs id b ofs mb mo t le' m' out,
  iad_write_root lhs = Some id -> le ! id = Some (Vptr b ofs) -> b <> mb ->
  ocn_exec ge e le m (Sassign lhs rhs) t le' m' out ->
  ilh_timer_load m' mb mo = ilh_timer_load m mb mo.
Proof.
  intros ge e le m lhs rhs id b ofs mb mo t le' m' out Hroot Htemp Hother Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ lhs _ _ _ |- _ =>
    pose proof (iad_scalar_destination_block _ _ _ _ lhs id b ofs _ _ _ Hroot Htemp Hl)
      as Heq; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - unfold ilh_timer_load. eapply Mem.load_store_other; [eassumption|left; congruence].
  - destruct lhs; cbn [iad_write_root] in Hroot; try discriminate.
    match goal with Hmode : access_mode _ = By_copy |- _ =>
      cbn [typeof] in Hmode; rewrite Hmode in Hroot; discriminate end.
  - match goal with Hbit : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion Hbit; subst end.
    unfold ilh_timer_load. eapply Mem.load_store_other; [eassumption|left; congruence].
Qed.
