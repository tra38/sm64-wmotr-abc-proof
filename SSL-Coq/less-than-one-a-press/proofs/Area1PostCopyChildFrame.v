(** Semantic write bounds for the real child-copy helpers. All reads may use
    arbitrary source values. No contract is assumed for either copy callee.
    A distinct allocated child slot is a remaining caller/allocator premise. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes Area1PostCopyChildSource
  InkRawCopyExpressions InkRawCopySource InkCopyCaller InkFloorResetExecution
  ObjectContactNecessity SecretContactExecution EyerokRank15LiveMovement
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition pcc_scalar (angle : bool) := if angle then tint else tfloat.
Definition pcc_member (angle : bool) := if angle then PCC._asS32 else PCC._asF32.
Definition pcc_array version angle := Efield (irc_raw_union version PCC._dst)
  (pcc_member angle) (tarray (pcc_scalar angle) 80).
Definition pcc_lhs version angle index := Ederef
  (Ebinop Oadd (pcc_array version angle) index (tptr (pcc_scalar angle))) (pcc_scalar angle).
Definition pcc_numbers : list Z := [6; 7; 8; 15; 16; 17; 18; 19; 20].

Definition pcc_union_check (ce : composite_env) tag member :=
  match ce ! tag with
  | Some co => match union_field_offset ce member (co_members co) with
      | OK (offset, Full) => Z.eqb offset 0 | _ => false end
  | _ => false end.

Lemma pcc_union_check_sound : forall ce tag member,
  pcc_union_check ce tag member = true ->
  exists co, ce ! tag = Some co /\ union_field_offset ce member (co_members co) = OK (0, Full).
Proof.
  intros ce tag member H. unfold pcc_union_check in H.
  destruct (ce ! tag) as [co|] eqn:Hco; try discriminate.
  destruct (union_field_offset ce member (co_members co)) as [[offset bf]|] eqn:Hoff;
    try discriminate. destruct bf; try discriminate.
  apply Z.eqb_eq in H. subst. eauto.
Qed.

Lemma pcc_union_layout : forall version angle,
  exists co,
    (genv_cenv (Clight.globalenv (selected_clight_target version))) !
      (rank15_raw_union_tag version) = Some co /\
    union_field_offset (Clight.globalenv (selected_clight_target version))
      (pcc_member angle) (co_members co) = OK (0, Full).
Proof.
  intros version angle. apply pcc_union_check_sound.
  change (pcc_union_check (prog_comp_env (selected_clight_target version))
    (rank15_raw_union_tag version) (pcc_member angle) = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version, angle; vm_compute; reflexivity.
Qed.

Lemma pcc_array_value : forall version angle e le m ob oo answer,
  le ! PCC._dst = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (pcc_array version angle) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)).
Proof.
  intros version angle e le m ob oo answer Htemp Hread.
  destruct (rank15_selected_raw_layout version)
    as (object_type & raw_type & Hobject & Hraw & HobjectOffset & _).
  destruct (pcc_union_layout version angle) as (co & Hco & Hoffset).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    PCC._Object PCC._rawData 136 = true) as Hfield.
  { unfold ibcc_field_ok. rewrite Hobject, HobjectOffset. reflexivity. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (irc_raw_union version PCC._dst) v ->
    v = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136))) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := irc_raw_object PCC._dst)
      (tag := PCC._Object) (field := PCC._rawData)
      (ty := Tunion (rank15_raw_union_tag version) noattr) (delta := 136);
      [reflexivity| |exact Hfield|right; reflexivity|eassumption].
    intros. eapply ibcc_deref_struct; eauto. }
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl; subst; try discriminate end.
  match goal with Hr : eval_expr _ _ _ _ (irc_raw_union _ _) _ |- _ => apply Hbase in Hr; inversion Hr; subst end.
  match goal with Htype : typeof (irc_raw_union _ _) = _ |- _ =>
    cbn [typeof irc_raw_union] in Htype; inversion Htype; subst end.
  match goal with Hfound : (genv_cenv _) ! _ = Some ?found |- _ =>
    assert (found = co) by congruence; subst found end.
  match goal with Hoff : union_field_offset _ _ _ = OK (?offset, ?bf) |- _ =>
    assert (offset = 0 /\ bf = Full) as E by (split; congruence);
    destruct E as [-> ->] end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  all: try solve [match goal with Hmode : access_mode _ = _ |- _ =>
    destruct angle; cbn [pcc_array pcc_scalar access_mode] in Hmode; discriminate end].
  all: rewrite Ptrofs.add_zero; reflexivity.
Qed.

Lemma pcc_raw_location : forall version angle e le m index number ob oo b ofs bf,
  le ! PCC._dst = Some (Vptr ob oo) ->
  typeof index = tint -> irc_constant index = Some (Int.repr number) ->
  In number pcc_numbers ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (pcc_lhs version angle index) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (136 + 4 * number)) /\ bf = Full.
Proof.
  intros version angle e le m index number ob oo b ofs bf Htemp Htype Hindex Hnumber Hl.
  inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hb; subst; clear Hb end.
  - match goal with Ha : eval_expr _ _ _ _ (pcc_array _ _) ?value |- _ =>
      assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)))
        by (eapply pcc_array_value; eauto); subst value end.
    match goal with Hi : eval_expr _ _ _ _ index ?value |- _ =>
      assert (value = Vint (Int.repr number)) by (eapply irc_constant_read; eauto); subst value end.
    destruct angle;
      match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
        cbn [typeof pcc_array pcc_scalar] in Hsem; rewrite Htype in Hsem;
        cbn in Hsem; inversion Hsem; subst end;
      rewrite Ptrofs.add_assoc;
      repeat (destruct Hnumber as [<-|Hnumber]; [repeat split; reflexivity|]); contradiction.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Definition pcc_outside (ob : block) slot chunk b offset :=
  b <> ob \/ offset + size_chunk chunk <= object_slot_offset slot + 160 \/
    object_slot_offset slot + 220 <= offset.
Definition pcc_frame ob slot before after := forall chunk b offset,
  pcc_outside ob slot chunk b offset ->
  Mem.load chunk after b offset = Mem.load chunk before b offset.

Lemma pcc_slot_address : forall slot delta,
  (slot < object_pool_capacity)%nat -> 0 <= delta <= 220 ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr delta)) =
    object_slot_offset slot + delta.
Proof.
  intros slot delta Hslot Hdelta.
  pose proof (rank15_pool_slot_offset_in_pointer_range _ Hslot) as Hrange.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (object_slot_offset slot)) by (unfold object_size in Hrange; lia).
  rewrite (Ptrofs.unsigned_repr delta) by (change (0 <= delta <= 4294967295); lia).
  apply Ptrofs.unsigned_repr. unfold object_size in Hrange. lia.
Qed.

Definition pcc_write_shape version lhs : Prop := exists angle index number,
  lhs = pcc_lhs version angle index /\ typeof index = tint /\
  irc_constant index = Some (Int.repr number) /\ In number pcc_numbers.

Lemma pcc_actual_write_frame : forall version e le m lhs rhs ob slot t le' after out,
  (slot < object_pool_capacity)%nat ->
  le ! PCC._dst = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  pcc_write_shape version lhs ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign lhs rhs) t le' after out -> pcc_frame ob slot m after.
Proof.
  intros version e le m lhs rhs ob slot t le' after out Hslot Hdst
    (angle & index & number & -> & Htype & Hconstant & Hnumber) Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (pcc_raw_location _ _ _ _ _ _ _ _ _ _ _ _ Hdst Htype Hconstant Hnumber Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - destruct angle;
      match goal with Hmode : access_mode _ = By_value _ |- _ =>
        cbn [pcc_lhs pcc_scalar access_mode] in Hmode; inversion Hmode; subst end.
    all: assert (6 <= number <= 20) as Hrange by
      (repeat (destruct Hnumber as [<-|Hnumber]; [lia|]); contradiction).
    all: match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
      cbn [Mem.storev] in Hstore; rewrite pcc_slot_address in Hstore by (auto; lia);
      intros chunk b offset Houtside; eapply Mem.load_store_other; [exact Hstore|] end.
    all: unfold pcc_outside in Houtside; cbn [size_chunk];
      destruct Houtside as [Hb|[Hlo|Hhi]]; [left; exact Hb|right; left; lia|right; right; lia].
  - match goal with Hmode : access_mode _ = By_copy |- _ =>
      destruct angle; cbn [pcc_lhs pcc_scalar access_mode] in Hmode; discriminate end.
Qed.

Fixpoint pcc_shape version s : Prop := match s with
| Sskip | Sreturn _ => True
| Sset id _ => id <> PCC._dst
| Sassign lhs _ => pcc_write_shape version lhs
| Ssequence a b | Sifthenelse _ a b => pcc_shape version a /\ pcc_shape version b
| _ => False end.

Lemma pcc_checked_body_frame : forall version e ob slot,
  (slot < object_pool_capacity)%nat ->
  forall le m s t le' after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' after out ->
  pcc_shape version s -> le ! PCC._dst = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  pcc_frame ob slot m after /\ le' ! PCC._dst = le ! PCC._dst.
Proof.
  intros version e ob slot Hslot le m s t le' after out Hrun.
  induction Hrun; cbn [pcc_shape]; intros Hshape Hdst; try contradiction;
    try solve [split; [intros chunk b offset _; reflexivity|reflexivity]].
  - split; [eapply pcc_actual_write_frame; eauto; econstructor; eauto|reflexivity].
  - split; [intros chunk b offset _; reflexivity|apply PTree.gso; congruence].
  - destruct Hshape as [Ha Hb].
    destruct (IHHrun1 Ha Hdst) as [Hfirst Hkeep].
    destruct (IHHrun2 Hb ltac:(rewrite Hkeep; exact Hdst)) as [Hlast Hkeep2].
    split; [intros chunk b offset Hout; rewrite Hlast, Hfirst; auto|congruence].
  - destruct Hshape as [Ha Hb]. auto.
  - destruct Hshape as [Ha Hb]. destruct b; auto.
Qed.

Ltac pcc_store_shape angle number :=
  cbn [pcc_shape]; unfold pcc_write_shape; exists angle; eexists; exists number;
  repeat split; try reflexivity; cbv [pcc_numbers In]; auto 12.

Lemma pcc_leaves_checked : forall version (angle : bool),
  pcc_shape version (fn_body (pcc_body version (if angle then PCCAngle else PCCPosition))).
Proof.
  intros [] []; cbn [pcc_body fn_body pcc_shape]; repeat split; try discriminate.
  all: solve [pcc_store_shape true 15 | pcc_store_shape true 16 | pcc_store_shape true 17 |
    pcc_store_shape true 18 | pcc_store_shape true 19 | pcc_store_shape true 20 |
    pcc_store_shape false 6 | pcc_store_shape false 7 | pcc_store_shape false 8].
Qed.

Lemma pcc_call_entry : forall version kind m dst src t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (pcc_body version kind)) [dst; src] t after result ->
  exists le final out,
    le ! PCC._dst = Some dst /\ le ! PCC._src = Some src /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
      (fn_body (pcc_body version kind)) t final after out.
Proof.
  intros version kind m dst src t after result Hcall.
  destruct (pcc_params version kind) as [Hvars Hparams].
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    rewrite Hparams in Hb; cbn [bind_parameter_temps] in Hb; inversion Hb; subst temps end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ ?temps _ _ _ ?final _ ?out |- _ =>
    exists temps, final, out end.
  split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
  split; [apply PTree.gss|eassumption].
Qed.

Theorem pcc_leaf_call_frames_other_slots : forall version (angle : bool) m ob slot src t after result,
  (slot < object_pool_capacity)%nat ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (pcc_body version (if angle then PCCAngle else PCCPosition)))
    [Vptr ob (Ptrofs.repr (object_slot_offset slot)); src] t after result ->
  pcc_frame ob slot m after.
Proof.
  intros version angle m ob slot src t after result Hslot Hcall.
  destruct (pcc_call_entry _ _ _ _ _ _ _ _ Hcall) as (le & final & out & Hdst & Hsrc & Hrun).
  eapply (proj1 (pcc_checked_body_frame _ _ _ _ Hslot _ _ _ _ _ _ _ Hrun
    (pcc_leaves_checked version angle) Hdst)).
Qed.
