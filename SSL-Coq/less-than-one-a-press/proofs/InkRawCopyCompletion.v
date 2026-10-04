(** Finish the actual State-to-collision copy after its Y-store checkpoint.
    The remaining destinations are derived from the generated US/JP tail.
    Reads may have arbitrary values; there are no external/helper calls here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Errors Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor jp_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkRawCopySource
  InkRawCopyExpressions InkRawCopyStores InkRawCopyHeight InkCopyCaller
  InkBackwardExecution ObjectContactNecessity ContactConsumerExecution
  Area2Rank12BContact Area1PostCopyChildFrame EyerokRank15LiveMovement
  Area1Rank18CopyRead Area1Rank18CopyResolution
  OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ircc_array version receiver angle := Efield (irc_raw_union version receiver)
  (pcc_member angle) (tarray (pcc_scalar angle) 80).
Definition ircc_lhs version receiver angle index := Ederef
  (Ebinop Oadd (ircc_array version receiver angle) index (tptr (pcc_scalar angle)))
  (pcc_scalar angle).
Definition ircc_numbers : list Z := [8; 15; 16; 17; 18; 19; 20; 35; 36; 37].

Lemma ircc_array_value : forall version receiver angle e le m ob oo answer,
  le ! receiver = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ircc_array version receiver angle) answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)).
Proof.
  intros version receiver angle e le m ob oo answer Htemp Hread.
  destruct (rank15_selected_raw_layout version)
    as (object_type & raw_type & Hobject & Hraw & HobjectOffset & _).
  destruct (pcc_union_layout version angle) as (co & Hco & Hoffset).
  assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IRC._Object IRC._rawData 136 = true) as Hfield.
  { unfold ibcc_field_ok.
    change ((genv_cenv (Clight.globalenv (selected_clight_target version))) ! IRC._Object =
      Some object_type) in Hobject.
    change (field_offset (Clight.globalenv (selected_clight_target version))
      IRC._rawData (co_members object_type) = OK (136, Full)) in HobjectOffset.
    rewrite Hobject, HobjectOffset. reflexivity. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (irc_raw_union version receiver) v ->
    v = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136))) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := irc_raw_object receiver)
      (tag := IRC._Object) (field := IRC._rawData)
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
    destruct angle; cbn [ircc_array pcc_scalar access_mode] in Hmode; discriminate end].
  all: rewrite Ptrofs.add_zero; reflexivity.
Qed.

Lemma ircc_raw_location : forall version receiver angle e le m index number ob oo b ofs bf,
  le ! receiver = Some (Vptr ob oo) ->
  typeof index = tint -> irc_constant index = Some (Int.repr number) ->
  In number ircc_numbers ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (ircc_lhs version receiver angle index) b ofs bf ->
  b = ob /\ ofs = Ptrofs.add oo (Ptrofs.repr (136 + 4 * number)) /\ bf = Full.
Proof.
  intros version receiver angle e le m index number ob oo b ofs bf Htemp Htype Hindex Hnumber Hl.
  inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ => inversion Hb; subst; clear Hb end.
  - match goal with Ha : eval_expr _ _ _ _ (ircc_array _ _ _) ?value |- _ =>
      assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 136)))
        by (eapply ircc_array_value; eauto); subst value end.
    match goal with Hi : eval_expr _ _ _ _ index ?value |- _ =>
      assert (value = Vint (Int.repr number)) by (eapply irc_constant_read; eauto); subst value end.
    destruct angle;
      match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
        cbn [typeof ircc_array pcc_scalar] in Hsem; rewrite Htype in Hsem;
        cbn in Hsem; inversion Hsem; subst end;
      rewrite Ptrofs.add_assoc;
      repeat (destruct Hnumber as [<-|Hnumber]; [repeat split; reflexivity|]); contradiction.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma ircc_slot_address : forall slot delta,
  (slot < object_pool_capacity)%nat -> 0 <= delta <= 288 ->
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

Definition ircc_outside (ob : block) slot chunk b offset : Prop :=
  b <> ob \/ offset + size_chunk chunk <= object_slot_offset slot + 168 \/
    object_slot_offset slot + 288 <= offset.
Definition ircc_frame ob slot before after : Prop := forall chunk b offset,
  ircc_outside ob slot chunk b offset ->
  Mem.load chunk after b offset = Mem.load chunk before b offset.

Definition ircc_stage version receiver prefix angle index rhs :=
  Ssequence (Sset receiver rank15_current_object_expression)
    (ocn_prepend prefix (Sassign (ircc_lhs version receiver angle index) rhs)).
Definition ircc_stage_ok version s : Prop :=
  exists receiver prefix angle index rhs number,
    s = ircc_stage version receiver prefix angle index rhs /\
    forallb ibk_normal prefix = true /\
    cce_readonly_keep receiver (ocn_prepend prefix Sskip) = true /\
    typeof index = tint /\ irc_constant index = Some (Int.repr number) /\
    In number ircc_numbers.

Lemma ircc_stage_frames : forall version e le m s cb ob slot t le' after out,
  (slot < object_pool_capacity)%nat ->
  e ! IRC._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ircc_stage_ok version s ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' after out ->
  ircc_frame ob slot m after.
Proof.
  intros version e le m s cb ob slot t le' after out Hslot Hlocal Hsymbol Hcurrent
    (receiver & prefix & angle & index & rhs & number & -> & Hnormal & Hpure &
      Htype & Hconstant & Hnumber) Hrun.
  unfold ircc_stage in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset receiver rank15_current_object_expression)
    _ _ _ _ _ eq_refl Hrun)
    as (read_le & read_m & read_trace & rest_trace & _ & Hread & Hrest).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ rank15_current_object_expression ?v |- _ =>
    assert (v = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
      (eapply irc_global_pointer_read; eauto); subst v end.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrest)
    as (store_le & store_m & prefix_trace & store_trace & _ & Hprefix & Hstore).
  destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hprefix Hpure)
    as (_ & -> & Hreceiver).
  assert (store_le ! receiver = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as Hptr
    by (rewrite Hreceiver; apply PTree.gss).
  inversion Hstore; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ircc_raw_location _ _ _ _ _ _ _ _ _ _ _ _ _ Hptr Htype Hconstant Hnumber Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst end.
  - destruct angle;
      match goal with Hmode : access_mode _ = By_value _ |- _ =>
        cbn [ircc_lhs pcc_scalar access_mode] in Hmode; inversion Hmode; subst end.
    all: assert (8 <= number <= 37) as Hrange by
      (repeat (destruct Hnumber as [<-|Hnumber]; [lia|]); contradiction).
    all: match goal with Hwrite : Mem.storev _ _ _ _ = Some _ |- _ =>
      cbn [Mem.storev] in Hwrite; rewrite ircc_slot_address in Hwrite by (auto; lia);
      intros chunk b offset Houtside; eapply Mem.load_store_other; [exact Hwrite|] end.
    all: unfold ircc_outside in Houtside; cbn [size_chunk];
      destruct Houtside as [Hb|[Hlo|Hhi]]; [left; exact Hb|right; left; lia|right; right; lia].
  - match goal with Hmode : access_mode _ = By_copy |- _ =>
      destruct angle; cbn [ircc_lhs pcc_scalar access_mode] in Hmode; discriminate end.
Qed.

Definition ircc_items version :=
  ocn_prefix_items 9 (irc_after_y version) ++
  [rank12b_drop_sequences 9 (irc_after_y version)].
Fixpoint ircc_join items := match items with
| [] => Sskip | [s] => s | s :: rest => Ssequence s (ircc_join rest) end.

Ltac ircc_receipt prefix_count angle number :=
  lazymatch goal with |- ircc_stage_ok _ ?s =>
    let body := eval cbv [irc_after_y rank18_copy_body fn_body rank12b_drop_sequences
      us_object_list_processor.f_copy_mario_state_to_object
      jp_object_list_processor.f_copy_mario_state_to_object] in s in
    lazymatch body with Ssequence (Sset ?receiver _) ?rest =>
      let count := eval compute in (Z.to_nat prefix_count) in
      let prefix := eval cbn [ocn_prefix_items] in (ocn_prefix_items count rest) in
      let store := eval cbn [rank12b_drop_sequences] in (rank12b_drop_sequences count rest) in
      lazymatch store with Sassign ?lhs ?rhs =>
        let index := lazymatch lhs with Ederef (Ebinop Oadd _ ?idx _) _ => idx end in
        unfold ircc_stage_ok; exists receiver, prefix, angle, index, rhs, number;
        repeat split; try reflexivity; cbv [ircc_numbers In]; auto 12
      end
    end
  end.

Lemma ircc_generated_tail : forall version,
  irc_after_y version = ircc_join (ircc_items version) /\
  Forall (ircc_stage_ok version) (ircc_items version) /\
  forallb ibk_normal (ircc_items version) = true.
Proof.
  intro version. split; [destruct version; reflexivity|].
  split; [|destruct version; reflexivity].
  destruct version.
  all: apply Forall_cons; [ircc_receipt 1 false 8|].
  all: apply Forall_cons; [ircc_receipt 2 true 15|].
  all: apply Forall_cons; [ircc_receipt 2 true 16|].
  all: apply Forall_cons; [ircc_receipt 2 true 17|].
  all: apply Forall_cons; [ircc_receipt 2 true 18|].
  all: apply Forall_cons; [ircc_receipt 2 true 19|].
  all: apply Forall_cons; [ircc_receipt 2 true 20|].
  all: apply Forall_cons; [ircc_receipt 1 true 35|].
  all: apply Forall_cons; [ircc_receipt 1 true 36|].
  all: apply Forall_cons; [ircc_receipt 1 true 37|].
  all: apply Forall_nil.
Qed.

Lemma ircc_tail_list_frames : forall version e items,
  Forall (ircc_stage_ok version) items -> forallb ibk_normal items = true ->
  forall cb ob slot le m t le' after out,
  (slot < object_pool_capacity)%nat -> cb <> ob ->
  e ! IRC._gCurrentObject = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IRC._gCurrentObject = Some cb ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ircc_join items) t le' after out ->
  ircc_frame ob slot m after.
Proof.
  intros version e items Hitems. induction Hitems as [|s rest Hstage Hrest IH];
    intros Hnormal cb ob slot le m t le' after out Hslot Hdistinct Hlocal Hsymbol Hcurrent Hrun.
  - inversion Hrun; subst. intros chunk b offset _. reflexivity.
  - destruct rest as [|next rest].
    + cbn [ircc_join] in Hrun. eapply ircc_stage_frames; eauto.
    + cbn in Hnormal. apply andb_true_iff in Hnormal as [Hhead Htail].
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hhead Hrun)
      as (mid & mid_m & pre & suf & _ & Hfirst & Hsuffix).
    pose proof (ircc_stage_frames _ _ _ _ _ _ _ _ _ _ _ _ Hslot Hlocal Hsymbol Hcurrent Hstage Hfirst) as Hframe.
    assert (Mem.load Mint32 mid_m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcurrentNext.
    { rewrite Hframe; [exact Hcurrent|left; exact Hdistinct]. }
    pose proof (IH Htail _ _ _ _ _ _ _ _ _ Hslot Hdistinct Hlocal Hsymbol HcurrentNext Hsuffix) as Hlast.
    intros chunk b offset Houtside. rewrite Hlast, Hframe; auto.
Qed.

Definition InkRawCopyCompletion : Prop :=
  forall version m cb gb mb ob slot height t after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge IRC._gCurrentObject = Some cb ->
  Genv.find_symbol ge IRC._gMarioObject = Some gb ->
  Genv.find_symbol ge IRC._gMarioStates = Some mb ->
  Genv.find_symbol ge IRC._gObjectPool = Some ob ->
  Mem.load Mint32 m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mint32 m gb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (rank18_copy_body version)) [] t after result ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 164) = Some (Vsingle height) /\
  Mem.load Mfloat32 after mb 64 = Some (Vsingle height) /\
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) =
    Mem.load Mfloat32 m ob (object_slot_offset slot + 36).

Theorem ircc_completed_copy_has_matching_state_and_collision_height : InkRawCopyCompletion.
Proof.
  unfold InkRawCopyCompletion.
  intros version m cb gb mb ob slot height t after result. cbn zeta.
  intros Hslot Hcs Hgs Hms Hps Hcurrent Hmario Hheight Hcall.
  pose proof (irc_completed_copy_has_exact_height_cut _ _ _ _ _ _ _ _ _ _ _
    Hslot Hcs Hgs Hms Hps Hcurrent Hmario Hheight Hcall) as Hcut.
  destruct Hcut as (choice & before & before_m & copied & copied_m & final & pre & write & suffix & out &
    Htrace & Hindex & Hprefix & Hy & Hstore & Hraw & Hstate & Hdisplay & Htail).
  assert (cb <> ob) as Hcb by
    (eapply Genv.global_addresses_distinct with
      (id1 := IRC._gCurrentObject) (id2 := IRC._gObjectPool);
      [discriminate|exact Hcs|exact Hps]).
  assert (mb <> ob) as Hmb by
    (eapply Genv.global_addresses_distinct with
      (id1 := IRC._gMarioStates) (id2 := IRC._gObjectPool);
      [discriminate|exact Hms|exact Hps]).
  destruct (irc_generated_cuts version) as (_ & _ & Hstages & _).
  pose proof (irc_before_y_preserves_protected_reads _ _ _ _ _ _ _ _ _ _ _ _
    Hstages Hslot Hcb (PTree.gempty _ _) Hcs Hcurrent Hprefix) as Hbefore.
  assert (Mem.load Mint32 copied_m cb 0 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcopiedCurrent.
  { assert (Mem.load Mint32 copied_m cb 0 = Mem.load Mint32 before_m cb 0) as HcbFrame
      by (eapply Mem.load_store_other; [exact Hstore|left; exact Hcb]).
    rewrite HcbFrame.
    rewrite Hbefore; [exact Hcurrent|left; exact Hcb]. }
  destruct (ircc_generated_tail version) as [Hsource [Hitems Hnormal]].
  rewrite Hsource in Htail.
  pose proof (ircc_tail_list_frames _ _ _ Hitems Hnormal _ _ _ _ _ _ _ _ _
    Hslot Hcb (PTree.gempty _ _) Hcs HcopiedCurrent Htail) as Hframe.
  split.
  - rewrite Hframe; [exact Hraw|right; left; cbn [size_chunk]; lia].
  - split.
    + rewrite Hframe; [exact Hstate|left; exact Hmb].
    + rewrite Hframe; [exact Hdisplay|right; left; cbn [size_chunk]; lia].
Qed.
