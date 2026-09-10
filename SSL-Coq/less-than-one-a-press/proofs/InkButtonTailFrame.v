(** Exact source-derived footprint of the remaining button helper.  Its
    only stores are Mario's input word and the two button-age bytes. *)
From Coq Require Import List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkControllerSource InkControllerEdge InkMarioInputFlag
  InkBodyResetFrame ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition ibt_protected chunk offset :=
  offset + size_chunk chunk <= 2 \/
  (4 <= offset /\ offset + size_chunk chunk <= 40) \/ 42 <= offset.
Definition ibt_frame mb before after := forall chunk offset,
  ibt_protected chunk offset -> Mem.load chunk after mb offset = Mem.load chunk before mb offset.

Lemma ibt_store_frame : forall m mb stored_chunk stored_offset value after,
  ((stored_chunk = Mint16unsigned /\ stored_offset = 2) \/
   (stored_chunk = Mint8unsigned /\ 40 <= stored_offset <= 41)) ->
  Mem.store stored_chunk m mb stored_offset value = Some after -> ibt_frame mb m after.
Proof.
  intros m mb stored_chunk stored_offset value after Hkind Hstore chunk offset Hprotected.
  eapply Mem.load_store_other; [exact Hstore|]. right.
  unfold ibt_protected in Hprotected. destruct Hkind as [[-> ->]|[-> Hrange]];
    cbn [size_chunk]; lia.
Qed.

Theorem ibt_safe_tail_frame : forall statement, imf_safe statement ->
  forall version e le m mb t last after out,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m statement t last after out ->
  t = E0 /\ out = Out_normal /\ last ! IBM._m = le ! IBM._m /\ ibt_frame mb m after.
Proof.
  intros statement Hsafe. induction Hsafe;
    intros version e le m mb t last after out Hm Hrun.
  - inversion Hrun; subst. repeat split; reflexivity.
  - inversion Hrun; subst. split; [reflexivity|]. split; [reflexivity|].
    split; [apply PTree.gso; congruence|intros chunk offset Hprotected; reflexivity].
  - destruct (imf_counter_field version field H) as [Hlayout Hrange].
    destruct (ibr_field_assignment_store _ e le m IBM._m IBM._MarioState field tuchar
      (imf_counter_offset field) Mint8unsigned rhs t last after out mb Ptrofs.zero
      Hm Hlayout eq_refl Hrun) as (-> & -> & -> & value & Hstore).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    eapply ibt_store_frame; [right; split; [reflexivity|exact Hrange]|].
    rewrite Ptrofs.add_zero_l in Hstore.
    rewrite Ptrofs.unsigned_repr in Hstore by (change (0 <= imf_counter_offset field <= 4294967295); lia).
    exact Hstore.
  - unfold imf_or_stage in Hrun.
    destruct (ibk_split_sequence _ _ _ _ (Sset id ics_input) _ _ _ _ _ eq_refl Hrun)
      as (mid & memory & pre & suf & Htrace & Hread & Hwrite).
    inversion Hread; subst; clear Hread.
    match type of Hwrite with ocn_exec ?ge ?env ?temps ?memory ?s ?tr ?temps' ?memory' ?outcome =>
      assert (temps ! IBM._m = Some (Vptr mb Ptrofs.zero)) as Hm' by
        (rewrite PTree.gso by congruence; exact Hm);
      destruct (ibr_field_assignment_store ge env temps memory IBM._m IBM._MarioState IBM._input
        tushort 2 Mint16unsigned _ tr temps' memory' outcome mb Ptrofs.zero Hm'
        (proj2 (proj2 (proj2 (proj2 (proj2 (ice_selected_fields version)))))) eq_refl Hwrite)
        as (-> & -> & -> & value & Hstore)
    end.
    split; [reflexivity|]. split; [reflexivity|]. split.
    + apply PTree.gso. congruence.
    + eapply ibt_store_frame; [left; split; reflexivity|exact Hstore].
  - destruct (ibk_split_sequence _ _ _ _ first rest _ _ _ _ (imf_safe_normal _ Hsafe1) Hrun)
      as (mid & memory & pre & suf & Htrace & Hfirst & Hrest).
    destruct (IHHsafe1 _ _ _ _ _ _ _ _ _ Hm Hfirst) as (Hp & Ho & Htemp & Hframe1).
    destruct (IHHsafe2 _ _ _ _ _ _ _ _ _ (eq_trans Htemp Hm) Hrest)
      as (Hs & Ho' & Htemp' & Hframe2).
    split; [rewrite Htrace, Hp, Hs; reflexivity|]. split; [exact Ho'|].
    split; [rewrite Htemp', Htemp; reflexivity|].
    intros chunk offset Hprotected. rewrite Hframe2, Hframe1 by exact Hprotected. reflexivity.
  - inversion Hrun; subst. destruct b; [eapply IHHsafe1|eapply IHHsafe2]; eauto.
Qed.

Corollary ibt_actual_button_tail_keeps_depth_action_timer :
  forall version e le m mb t last after out,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_mario_tail version) t last after out ->
  Mem.load Mfloat32 after mb 192 = Mem.load Mfloat32 m mb 192 /\
  Mem.load Mint32 after mb 12 = Mem.load Mint32 m mb 12 /\
  Mem.load Mint16unsigned after mb 26 = Mem.load Mint16unsigned m mb 26.
Proof.
  intros. destruct (ibt_safe_tail_frame _ (imf_actual_tail_is_safe version)
    version e le m mb t last after out H H0) as (_ & _ & _ & Hframe).
  repeat split; apply Hframe; unfold ibt_protected; cbn [size_chunk]; lia.
Qed.
