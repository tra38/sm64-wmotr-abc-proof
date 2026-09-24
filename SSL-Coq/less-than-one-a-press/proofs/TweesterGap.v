(** Backward gap test for the ordinary, non-ejecting Tweester action.
    The real continuation includes BOTH outcomes of its floor lookup. Every
    completed continuation reaches the real State-to-display copy. We reuse
    the completed vector-copy proof rather than assuming a harmless callee.
    This is a copy checkpoint, not a whole gameplay or ejection proof. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import
  us_mario_actions_automatic jp_mario_actions_automatic.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkCopyCompletion InkFloorResetExecution
  OrdinaryArea1EntryMemory ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution Area2Rank12BContact SelectedClightTarget
  Area1FirstNull InkVerticalRetryGeometry.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module TW := us_mario_actions_automatic.

Definition twg_body version := match version with
| VersionUS => TW.f_act_tornado_twirling
| VersionJP => jp_mario_actions_automatic.f_act_tornado_twirling end.
Definition twg_piece version n := ibk_head (rank12b_drop_sequences n (fn_body (twg_body version))).
Definition twg_entry_prefix version := map (twg_piece version) (seq 0 8).
Definition twg_continuation version := rank12b_drop_sequences 8 (fn_body (twg_body version)).
Definition twg_before_copy version := map (twg_piece version) (seq 8 15).
Definition twg_refresh version := twg_piece version 23.
Definition twg_tail version := rank12b_drop_sequences 24 (fn_body (twg_body version)).

Definition twg_object := Ederef (Etempvar TW._t'9 (tptr (Tstruct TW._Object noattr)))
  (Tstruct TW._Object noattr).
Definition twg_graphics := Efield (Efield twg_object TW._header
  (Tstruct TW._ObjectNode noattr)) TW._gfx (Tstruct TW._GraphNodeObject noattr).
Definition twg_display := Efield twg_graphics TW._pos (tarray tfloat 3).
Definition twg_copy := Scall None
  (Evar TW._vec3f_copy (Tfunction [tptr tfloat; tptr tfloat] (tptr tvoid) cc_default))
  [twg_display; ibcc_destination].

Theorem twg_actual_source_cuts : forall version,
  fn_body (twg_body version) = ocn_prepend (twg_entry_prefix version) (twg_continuation version) /\
  twg_continuation version = ocn_prepend (twg_before_copy version)
    (Ssequence (twg_refresh version) (twg_tail version)) /\
  forallb ibk_normal (twg_before_copy version) = true /\
  forallb (cce_keeps_temp TW._m) (twg_before_copy version) = true /\
  twg_refresh version = Ssequence (Sset TW._t'9 ibk_object_read) twg_copy /\
  ibk_normal (twg_refresh version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma twg_display_address : forall version e le m ob oo answer,
  le ! TW._t'9 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m twg_display answer ->
  answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)).
Proof.
  intros version e le m ob oo answer Hobject Hread.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & Hpos).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m twg_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m (Efield twg_object TW._header (Tstruct TW._ObjectNode noattr)) v ->
    v = Vptr ob oo) as Hhead.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _ twg_object TW._Object
      TW._header (Tstruct TW._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m twg_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hr. pose proof (ibcc_aggregate_field _ _ _ _
      (Efield twg_object TW._header (Tstruct TW._ObjectNode noattr)) TW._ObjectNode
      TW._gfx (Tstruct TW._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hr) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  eapply ibcc_aggregate_field with (base := twg_graphics)
    (tag := TW._GraphNodeObject) (field := TW._pos) (ty := tarray tfloat 3)
    (delta := 32); eauto; reflexivity.
Qed.

Lemma twg_copy_arguments : forall version e le m mb mo ob oo args,
  le ! TW._m = Some (Vptr mb mo) -> le ! TW._t'9 = Some (Vptr ob oo) ->
  eval_exprlist (Clight.globalenv (selected_clight_target version)) e le m
    [twg_display; ibcc_destination] [tptr tfloat; tptr tfloat] args ->
  args = [Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)); Vptr mb (Ptrofs.add mo (Ptrofs.repr 60))].
Proof.
  intros version e le m mb mo ob oo args Hm Hobject Hargs.
  repeat match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H end.
  match goal with H : eval_expr _ _ _ _ twg_display ?value |- _ =>
    assert (value = Vptr ob (Ptrofs.add oo (Ptrofs.repr 32)))
      by (eapply twg_display_address; eauto); subst value end.
  match goal with H : eval_expr _ _ _ _ ibcc_destination ?value |- _ =>
    assert (value = Vptr mb (Ptrofs.add mo (Ptrofs.repr 60)))
      by (eapply ifr_state_position_value; eauto); subst value end.
  repeat match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in H; inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma twg_refresh_calls_real_copy : forall version e le m mb ob slot t le' m' out,
  e ! TW._vec3f_copy = None -> le ! TW._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (twg_refresh version) t le' m' out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m (Internal (ibk_copy_body version))
    [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32));
     Vptr mb (Ptrofs.repr 60)] t m' result.
Proof.
  intros version e le m mb ob slot t le' m' out Hlocal Hm Hobject Hrun.
  destruct (twg_actual_source_cuts version) as (_ & _ & _ & _ & Hshape & _).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset TW._t'9 ibk_object_read) _ _ _ _ _ eq_refl Hrun)
    as (copy_le & copy_m & pre & rest & Htrace & Hread & Hcopy).
  inversion Hread; subst.
  match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob (Ptrofs.repr (object_slot_offset slot)))
      by (eapply ibcc_actual_object_read; eauto); subst v end.
  destruct (ibk_selected_copy_resolves version) as (b & Hsymbol & Hfunction).
  unfold twg_copy in Hcopy. inversion Hcopy; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr b Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  match goal with Hr : eval_exprlist ?ge ?env ?temps ?memory _ _ ?args |- _ =>
    assert (args = [Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 32));
      Vptr mb (Ptrofs.add Ptrofs.zero (Ptrofs.repr 60))]) as Hargs by
      (eapply (twg_copy_arguments version env temps memory mb Ptrofs.zero ob
        (Ptrofs.repr (object_slot_offset slot)));
        [rewrite PTree.gso by discriminate; exact Hm|apply PTree.gss|exact Hr]); subst args end.
  eauto.
Qed.

(** Exact post-copy loads: the same State Y is retained and displayed.
    No incoming display, velocity, floor result or wall-correction bound. *)
Theorem twg_refresh_removes_vertical_gap : forall version e le m mb ob slot height t le' m' out,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  e ! TW._vec3f_copy = None -> le ! TW._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (twg_refresh version) t le' m' out ->
  Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
  Mem.load Mfloat32 m' mb 64 = Some (Vsingle height) /\
  (forall chunk b ofs, Mem.valid_block m b -> icp_outside_display ob slot chunk b ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs).
Proof.
  intros version e le m mb ob slot height t le' m' out Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hrun.
  destruct (twg_refresh_calls_real_copy _ _ _ _ _ _ _ _ _ _ _ Hlocal Hm Hobj Hrun) as [result Hcall].
  destruct (icp_completed_copy_forgets_old_display _ _ _ _ _ _ _ _ _
    Hslot Hsep Hvalid Hheight Hcall) as [Hdisplay Hframe].
  split; [exact Hdisplay|]. split; [|exact Hframe].
  rewrite Hframe; [exact Hheight|eapply ibcc_loaded_block_valid; exact Hheight|].
  unfold icp_outside_display. left. exact Hsep.
Qed.

Definition TweesterContinuedCopyCheckpoint : Prop :=
  forall version e le m mb t le' m' out,
  let ge := Clight.globalenv (selected_clight_target version) in
  e ! TW._vec3f_copy = None -> le ! TW._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec ge e le m (twg_continuation version) t le' m' out ->
  exists cut_le cut_m copy_le copy_m pre copy_t suffix,
    t = pre ++ (copy_t ++ suffix) /\
    ocn_exec ge e le m (ocn_prepend (twg_before_copy version) Sskip) pre cut_le cut_m Out_normal /\
    ocn_exec ge e cut_le cut_m (twg_refresh version) copy_t copy_le copy_m Out_normal /\
    ocn_exec ge e copy_le copy_m (twg_tail version) suffix le' m' out /\
    (forall ob slot height, (slot < object_pool_capacity)%nat -> mb <> ob ->
      Mem.valid_block cut_m ob ->
      Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
      Mem.load Mfloat32 copy_m ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
      Mem.load Mfloat32 copy_m mb 64 = Some (Vsingle height)).

Theorem twg_non_ejecting_continuation_has_no_gap_checkpoint : TweesterContinuedCopyCheckpoint.
Proof.
  unfold TweesterContinuedCopyCheckpoint.
  intros version e le m mb t le' m' out Hlocal Hm Hrun.
  destruct (twg_actual_source_cuts version) as (_ & Hshape & Hnormal & Hkeeps & _ & HcopyNormal).
  rewrite Hshape in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (cut_le & cut_m & pre & rest & Htrace & Hprefix & Hrest).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HcopyNormal Hrest)
    as (copy_le & copy_m & copy_t & suffix & HrestTrace & Hcopy & Htail).
  assert (cce_keeps_temp TW._m (ocn_prepend (twg_before_copy version) Sskip) = true) as Hkeep
    by (destruct version; reflexivity).
  pose proof (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ _ Hprefix Hkeep) as Hcut.
  exists cut_le, cut_m, copy_le, copy_m, pre, copy_t, suffix.
  split; [rewrite Htrace,HrestTrace; reflexivity|].
  split; [exact Hprefix|]. split; [exact Hcopy|]. split; [exact Htail|].
  intros ob slot height Hslot Hsep Hvalid Hobj Hheight.
  destruct (twg_refresh_removes_vertical_gap version e cut_le cut_m mb ob slot height
    copy_t copy_le copy_m Out_normal Hslot Hsep Hvalid Hlocal ltac:(congruence) Hobj Hheight Hcopy)
    as (Hd & Hs & _).
  auto.
Qed.

Definition TweesterCopyExcludesSuppliedGap : Prop :=
  forall version e le m mb ob slot height t le' m' out,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  e ! TW._vec3f_copy = None -> le ! TW._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (twg_refresh version) t le' m' out ->
  ~ (Mem.load Mfloat32 m' mb 64 = Some (Vsingle (area1_f32_of_Z 768)) /\
     Mem.load Mfloat32 m' ob (object_slot_offset slot + 36) = Some (Vsingle ivr_contact_height)).

Theorem twg_copy_cannot_install_supplied_vertical_gap : TweesterCopyExcludesSuppliedGap.
Proof.
  unfold TweesterCopyExcludesSuppliedGap.
  intros version e le m mb ob slot height t le' m' out Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hrun [Hlow Hhigh].
  destruct (twg_refresh_removes_vertical_gap _ _ _ _ _ _ _ _ _ _ _ _
    Hslot Hsep Hvalid Hlocal Hm Hobj Hheight Hrun) as (Hd & Hs & _).
  assert (area1_f32_of_Z 768 = ivr_contact_height) as E by congruence.
  apply (f_equal Float32.to_bits) in E. vm_compute in E. discriminate.
Qed.

Definition TweesterGapBoundary : Prop := TweesterContinuedCopyCheckpoint /\
  TweesterCopyExcludesSuppliedGap /\
  (forall version, twg_refresh version = Ssequence (Sset TW._t'9 ibk_object_read) twg_copy).
Theorem twg_gap_boundary_checked : TweesterGapBoundary.
Proof.
  split; [exact twg_non_ejecting_continuation_has_no_gap_checkpoint|].
  split; [exact twg_copy_cannot_install_supplied_vertical_gap|].
  intro version. exact (proj1 (proj2 (proj2 (proj2 (proj2 (twg_actual_source_cuts version)))))).
Qed.
