(** The actual initialization action store chooses standing or water idle.
    The completed-call theorem exposes this checkpoint in the same run;
    calls elsewhere in initialization retain their actual effects. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkCourseEntryReset
  InkBackwardSource InkBackwardExecution InkControllerEdge InkControllerSource InkCopyCaller
  InkActionConstructor InkActionInstall InkDirectActionStores InkActionPassStart
  ObjectContactNecessity ContactConsumerExecution Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Opaque selected_clight_target.

Definition iia_prefix version := ocn_prefix_items 26 (fn_body (ier_body version IERInit)).
Definition iia_segment version := ibk_head (rank12b_drop_sequences 26
  (fn_body (ier_body version IERInit))).
Definition iia_suffix version := rank12b_drop_sequences 27 (fn_body (ier_body version IERInit)).
Definition iia_choice version := ibk_head (iia_segment version).
Definition iia_reads version := ocn_prefix_items 4 (iia_choice version).
Definition iia_guard version := match rank12b_drop_sequences 4 (iia_choice version) with
| Sifthenelse guard _ _ => guard | _ => Econst_int Int.zero tint end.
Definition iia_install := Ssequence (Sset IER._t'47 ier_state)
  (Sassign (idas_field IER._t'47) (Etempvar IER._t'4 tint)).
Definition iia_set value := Sset IER._t'4 (Ecast (Econst_int (Int.repr value) tint) tint).
Definition iia_value value : Prop := value = Int.repr 939532992 \/ value = Int.repr 205521409.

Lemma iia_source : forall version,
  fn_body (ier_body version IERInit) = ocn_prepend (iia_prefix version)
    (Ssequence (iia_segment version) (iia_suffix version)) /\
  forallb ibk_normal (iia_prefix version) = true /\
  iia_segment version = Ssequence (iia_choice version) iia_install /\
  iia_choice version = ocn_prepend (iia_reads version)
    (Sifthenelse (iia_guard version) (iia_set 939532992) (iia_set 205521409)) /\
  forallb ibk_normal (iia_reads version) = true /\
  ibk_normal (iia_choice version) = true /\
  ibk_normal (iia_segment version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iia_set_effect : forall ge e le m number t le' m' out,
  ocn_exec ge e le m (iia_set number) t le' m' out ->
  le' ! IER._t'4 = Some (Vint (Int.repr number)).
Proof.
  intros ge e le m number t le' m' out Hrun.
  unfold iia_set in Hrun. inversion Hrun; subst.
  match goal with H : eval_expr _ _ _ _ (Ecast _ _) _ |- _ => inversion H; subst; clear H end.
  - match goal with H : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in H; subst end.
    match goal with H : sem_cast _ _ _ _ = Some _ |- _ =>
      cbn in H; inversion H; subst end. apply PTree.gss.
  - match goal with H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma iia_choice_is_idle : forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iia_choice version) t le' m' out ->
  exists value, le' ! IER._t'4 = Some (Vint value) /\ iia_value value.
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (iia_source version) as (_ & _ & _ & Hsource & Hnormal & _).
  rewrite Hsource in Hrun.
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (branch_le & branch_m & pre & suf & Htrace & Hreads & Hbranch).
  inversion Hbranch; subst. destruct b.
  - exists (Int.repr 939532992). split; [eapply iia_set_effect; eassumption|left; reflexivity].
  - exists (Int.repr 205521409). split; [eapply iia_set_effect; eassumption|right; reflexivity].
Qed.

Lemma iia_action_base : forall ge e le m temp b ofs bf,
  eval_lvalue ge e le m (idas_field temp) b ofs bf ->
  exists mb mo, le ! temp = Some (Vptr mb mo).
Proof.
  intros ge e le m temp b ofs bf H. unfold idas_field in H.
  inversion H; subst; clear H.
  all: repeat match goal with
  | H : eval_expr _ _ _ _ (Ederef _ _) _ |- _ => inversion H; subst; clear H
  | H : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion H; subst; clear H
  | H : deref_loc _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  | H : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inversion H; subst; clear H
  end.
  all: try solve [match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end].
  all: eauto.
Qed.

Lemma iia_install_effect : forall version e le m value t le' m' out,
  le ! IER._t'4 = Some (Vint value) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    iia_install t le' m' out ->
  exists mb mo,
    eval_expr (Clight.globalenv (selected_clight_target version)) e le m
      ier_state (Vptr mb mo) /\
    iai_action_load m' mb mo = Some (Vint value).
Proof.
  intros version e le m value t le' m' out Hvalue Hrun.
  unfold iia_install in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (Sset IER._t'47 ier_state) _ _ _ _ _ eq_refl Hrun)
    as (store_le & store_m & pre & suf & Htrace & Hread & Hstore).
  inversion Hread; subst; clear Hread. inversion Hstore; subst; clear Hstore.
  lazymatch goal with Hl : eval_lvalue _ _ _ _ (idas_field _) _ _ _ |- _ =>
    destruct (iia_action_base _ _ _ _ _ _ _ _ Hl) as (mb & mo & Hptr);
    rewrite PTree.gss in Hptr; inversion Hptr; subst;
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version))
      _ _ _ IER._t'47 IER._MarioState IER._action tuint
      mb mo 12 _ _ _ ltac:(apply PTree.gss) (ias_selected_action_field version) Hl)
      as (-> & -> & ->)
  end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IER._t'4 _) ?value' |- _ =>
    assert (value' = Vint value) by
      (eapply ocn_temp_value; [exact Hr|rewrite PTree.gso by discriminate; exact Hvalue]); subst value' end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ =>
    cbn in Hmode; inversion Hmode; subst end.
  exists mb, mo. split; [eassumption|].
  unfold iai_action_load. erewrite Mem.load_store_same by eassumption. reflexivity.
Qed.

Lemma iia_segment_excludes_long_jump : forall version e le m t le' m' out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iia_segment version) t le' m' out ->
  exists mb mo value, iai_action_load m' mb mo = Some (Vint value) /\
    iia_value value /\ iai_safe_value (Vint value).
Proof.
  intros version e le m t le' m' out Hrun.
  destruct (iia_source version) as (_ & _ & Hsource & _ & _ & Hnormal & _).
  rewrite Hsource in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (install_le & install_m & pre & suf & Htrace & Hchoice & Hinstall).
  destruct (iia_choice_is_idle _ _ _ _ _ _ _ _ Hchoice) as (value & Htemp & Hvalue).
  destruct (iia_install_effect _ _ _ _ _ _ _ _ _ Htemp Hinstall) as (mb & mo & Hstate & Haction).
  exists mb, mo, value. repeat split; try assumption.
  all: destruct Hvalue as [-> | ->]; discriminate.
Qed.

Definition InkInitActionCheckpoint : Prop := forall version m t m' result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (ier_body version IERInit)) [] t m' result ->
  exists e entry_le entered prefix_le prefix_m ready_le ready_m last_le last out
    pre action_t suf mb mo value,
    function_entry2 (Clight.globalenv (selected_clight_target version))
      (ier_body version IERInit) [] m e entry_le entered /\
    t = pre ++ (action_t ++ suf) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e entry_le entered
      (ocn_prepend (iia_prefix version) Sskip) pre prefix_le prefix_m Out_normal /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e prefix_le prefix_m
      (iia_segment version) action_t ready_le ready_m Out_normal /\
    iai_action_load ready_m mb mo = Some (Vint value) /\
    iia_value value /\ iai_safe_value (Vint value) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e ready_le ready_m
      (iia_suffix version) suf last_le last out /\
    Mem.free_list last (blocks_of_env (Clight.globalenv (selected_clight_target version)) e) = Some m' /\
    outcome_result_value out (fn_return (ier_body version IERInit)) result last.

Theorem iia_completed_initialization_has_only_idle_action_at_its_store : InkInitActionCheckpoint.
Proof.
  intros version m t m' result Hcall. inversion Hcall; subst.
  destruct (iia_source version) as (Hsource & Hnormal & _ & _ & _ & _ & Hsegment).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hsource in Hr;
    destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (prefix_le & prefix_m & pre & rest & Htrace & Hprefix & Hrest) end.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hsegment Hrest)
    as (ready_le & ready_m & action_t & suf & HrestTrace & Haction & Hsuffix).
  destruct (iia_segment_excludes_long_jump _ _ _ _ _ _ _ _ Haction)
    as (mb & mo & value & Hload & Hvalue & Hsafe).
  match goal with
  | He : function_entry2 _ _ _ _ ?env ?initial_le ?initial_m,
    Hs : ocn_exec _ _ _ _ (iia_suffix _) _ ?last_le ?last ?out |- _ =>
    exists env, initial_le, initial_m, prefix_le, prefix_m, ready_le, ready_m,
      last_le, last, out, pre, action_t, suf, mb, mo, value
  end.
  repeat first [eassumption|split]. subst; reflexivity.
Qed.
