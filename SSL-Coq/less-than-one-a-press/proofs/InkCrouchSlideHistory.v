(** Carry the actual entry input through crouch-slide's long-jump window.
    Its timer write is disjoint from input; no controller history or later
    action helper is silently assumed here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkMovingBackwardSource
  InkLongJumpGuard InkLandingExecution InkLandingHistory InkControllerEdge
  InkMarioInputFlag InkBackwardSource InkBackwardExecution InkFloorResetExecution InkCopyCaller
  ObjectContactNecessity SelectedClightTarget Area2Rank12BContact.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ich_window version := ibk_head
  (rank12b_drop_sequences 1 (fn_body (imb_body version IMBCrouch))).
Definition ich_increment version := match ich_window version with
| Ssequence _ (Sifthenelse _ (Ssequence first _) _) => first | _ => Sskip end.
Definition ich_after_window version := rank12b_drop_sequences 2
  (fn_body (imb_body version IMBCrouch)).
Definition ich_slide_yes version := match ibk_head (fn_body (imb_body version IMBCrouch)) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.

Lemma ich_source : forall version,
  fn_body (imb_body version IMBCrouch) =
    Ssequence (ilh_input_guard IMB._t'16 (Int.repr 8) (ich_slide_yes version))
      (Ssequence (ich_window version) (ich_after_window version)) /\
  ich_window version = Ssequence (Sset IMB._t'12 imb_timer)
    (Sifthenelse (Ebinop Olt (Etempvar IMB._t'12 tushort)
      (Econst_int (Int.repr 30) tint) tint)
      (Ssequence (ich_increment version) (imb_crouch_a_guard version)) Sskip) /\
  ich_increment version = Ssequence (Sset IMB._t'15 imb_timer)
    (Sassign imb_timer (Ebinop Oadd (Etempvar IMB._t'15 tushort)
      (Econst_int Int.one tint) tint)).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma ich_timer_store_preserves_input : forall version e le m mb mo rhs t le' m' out,
  imf_room mo -> le ! IMB._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign imb_timer rhs) t le' m' out ->
  imf_input_load m' mb mo = imf_input_load m mb mo /\
    t = E0 /\ out = Out_normal /\ le' = le.
Proof.
  intros version e le m mb mo rhs t le' m' out Hroom Hm Hrun.
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory imb_timer _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IMB._m IMB._MarioState IMB._actionTimer tushort mb mo 26 _ _ _
      Hm (proj1 (imb_control_fields version)) Hl) as (-> & -> & ->) end.
  match goal with H : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion H; subst; try discriminate end.
  match goal with H : access_mode _ = By_value _ |- _ => cbn in H; inversion H; subst end.
  split.
  - unfold imf_input_load. eapply Mem.load_store_other; [eassumption|].
    right; left. cbn [size_chunk]. rewrite !imf_address by (auto; lia). lia.
  - repeat split; reflexivity.
Qed.

Definition InkCrouchWindowNoA : Prop :=
  forall version e le m mb mo flags t le' m' out,
  imf_room mo -> le ! IMB._m = Some (Vptr mb mo) ->
  imf_input_load m mb mo = Some (Vint flags) -> Int.and flags (Int.repr 2) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ich_window version) t le' m' out ->
  imf_input_load m' mb mo = Some (Vint flags) /\
    t = E0 /\ out = Out_normal /\ le' ! IMB._m = Some (Vptr mb mo).

Theorem ich_actual_timer_window_cannot_create_a : InkCrouchWindowNoA.
Proof.
  unfold InkCrouchWindowNoA.
  intros version e le m mb mo flags t le' m' out Hroom Hm Hinput HnoA Hrun.
  assert (le' ! IMB._m = Some (Vptr mb mo)) as Hkeep.
  { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IMB._m Hrun
      ltac:(destruct version; reflexivity)). exact Hm. }
  destruct (ich_source version) as (_ & Hwindow & Hincrement). rewrite Hwindow in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'12 imb_timer) _ _ _ _ _ eq_refl Hrun)
    as (middle & memory & pre & suf & Htrace & Hread & Hbranch).
  inversion Hread; subst. inversion Hbranch; subst. destruct b.
  - assert (ibk_normal (ich_increment version) = true) as Hnormal by (destruct version; reflexivity).
    match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _
      (Ssequence (ich_increment _) _) _ _ _ _ |- _ =>
      destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
        as (guard_le & guard_m & inc_t & guard_t & Htrace2 & Hinc & Hguard) end.
    assert (guard_le ! IMB._m = Some (Vptr mb mo)) as HguardM.
    { rewrite (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ IMB._m Hinc
        ltac:(destruct version; reflexivity)). rewrite PTree.gso by discriminate. exact Hm. }
    rewrite Hincrement in Hinc.
    destruct (ibk_split_sequence _ _ _ _ (Sset IMB._t'15 imb_timer) _ _ _ _ _ eq_refl Hinc)
      as (store_le & store_m & read_t & store_t & Htrace3 & Hread2 & Hstore).
    inversion Hread2; subst.
    lazymatch type of Hstore with
    | ocn_exec _ ?env ?temps ?memory _ ?tr ?final_le ?final_m ?outcome =>
      destruct (ich_timer_store_preserves_input version env temps memory mb mo _ tr final_le final_m outcome Hroom
        ltac:(repeat rewrite PTree.gso by discriminate; exact Hm) Hstore)
        as (Hsame & HstoreTrace & _ & _)
    end.
    assert (imf_input_load guard_m mb mo = Some (Vint flags)) as HguardInput
      by (rewrite Hsame; exact Hinput).
    destruct (imb_actual_crouch_a_guard_skips_without_pressed_bit version e guard_le guard_m mb mo flags _ _ _ _
      HguardM HguardInput HnoA Hguard)
      as (HguardTrace & HguardMemory & Hout).
    subst. repeat split; try assumption; congruence.
  - match goal with H : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst end.
    repeat split; assumption || reflexivity.
Qed.

Definition InkCrouchSlideEntryCut : Prop :=
  forall version e le m mb mo flags t le' m' out,
  imf_room mo -> le ! IMB._m = Some (Vptr mb mo) ->
  imf_input_load m mb mo = Some (Vint flags) ->
  Int.and flags (Int.repr 8) = Int.zero -> Int.and flags (Int.repr 2) = Int.zero ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (imb_body version IMBCrouch)) t le' m' out ->
  exists after_le after_m,
    after_le ! IMB._m = Some (Vptr mb mo) /\
    imf_input_load after_m mb mo = Some (Vint flags) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e after_le after_m
      (ich_after_window version) t le' m' out.

Theorem ich_actual_crouch_entry_reaches_suffix_without_a : InkCrouchSlideEntryCut.
Proof.
  unfold InkCrouchSlideEntryCut.
  intros version e le m mb mo flags t le' m' out Hroom Hm Hinput Hslide HnoA Hrun.
  rewrite (proj1 (ich_source version)) in Hrun.
  pose proof (ilh_split_clear_input_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hm Hinput Hslide Hrun) as Hrest.
  inversion Hrest; subst.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory (ich_window _) ?tr ?final_le ?final_m ?outcome |- _ =>
      destruct (ich_actual_timer_window_cannot_create_a version env temps memory mb mo flags tr final_le final_m outcome Hroom
        ltac:(rewrite PTree.gso by discriminate; exact Hm) Hinput HnoA Hr)
        as (Hflags & -> & _ & HsameM) end.
    eauto 8.
  - match goal with Hr : ClightBigstep.exec_stmt _ _ ?env ?temps ?memory (ich_window _) ?tr ?final_le ?final_m ?outcome |- _ =>
      destruct (ich_actual_timer_window_cannot_create_a version env temps memory mb mo flags tr final_le final_m outcome Hroom
        ltac:(rewrite PTree.gso by discriminate; exact Hm) Hinput HnoA Hr)
        as (_ & _ & Hnormal & _) end. contradiction.
Qed.
