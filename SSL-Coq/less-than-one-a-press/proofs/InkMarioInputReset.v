(** The actual update_mario_inputs prefix clears old input before the button
    call. The two intervening metadata writes do not restore the old A bit. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkControllerSource
  InkControllerEdge InkMarioInputFlag InkBackwardSource InkCopyCaller
  InkBackwardExecution InkFloorResetExecution Area2Rank12BContact
  ContactConsumerExecution ObjectContactNecessity EyerokRank15LiveMovement
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition imr_first version := ibk_head (fn_body (ics_body version ICInputs)).
Definition imr_metadata version := ocn_prefix_items 2
  (rank12b_drop_sequences 2 (fn_body (ics_body version ICInputs))).
Definition imr_button_call version := ibk_head
  (rank12b_drop_sequences 4 (fn_body (ics_body version ICInputs))).
Definition imr_after_buttons version := rank12b_drop_sequences 5
  (fn_body (ics_body version ICInputs)).

Lemma imr_source : forall version,
  fn_body (ics_body version ICInputs) = Ssequence (imr_first version)
    (Ssequence (ics_reset version) (ocn_prepend (imr_metadata version)
      (Ssequence (imr_button_call version) (imr_after_buttons version)))) /\
  imr_button_call version = Scall None
    (Evar IBM._update_mario_button_inputs
      (Tfunction [tptr (Tstruct IBM._MarioState noattr)] tvoid cc_default))
    [Etempvar IBM._m (tptr (Tstruct IBM._MarioState noattr))] /\
  ibk_normal (imr_first version) = true /\
  ifr_keeps_temp IBM._m (imr_first version) = true /\
  forallb ibk_normal (imr_metadata version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma imr_reset_actual_store : forall version e le m mb mo t le' m' out,
  le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ics_reset version) t le' m' out ->
  Mem.store Mint16unsigned m mb (Ptrofs.unsigned (Ptrofs.add mo (Ptrofs.repr 2)))
    (Vint Int.zero) = Some m' /\ t = E0 /\ out = Out_normal /\ le' = le.
Proof.
  intros version e le m mb mo t le' m' out Hm Hrun.
  destruct (ics_source_cuts version) as (_ & _ & _ & _ & _ & Hreset). rewrite Hreset in Hrun.
  destruct (ice_selected_fields version) as (_ & _ & _ & _ & _ & Hfield).
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IBM._m IBM._MarioState IBM._input tushort mb mo 2 _ _ _ Hm Hfield Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply ocn_const_int_value in Hr; subst end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split; [assumption|]. repeat split; reflexivity.
Qed.

Definition imr_offset field := if Pos.eqb field IBM._flags then 4 else 164.
Lemma imr_field : forall version field,
  field = IBM._flags \/ field = IBM._collidedObjInteractTypes ->
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState field (imr_offset field) = true /\ 4 <= imr_offset field <= 164.
Proof.
  intros version field Hfield.
  change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState field (imr_offset field) = true /\ 4 <= imr_offset field <= 164).
  rewrite <- rank15_selected_header_environment_exact.
  destruct Hfield as [Hfield | Hfield]; subst field; destruct version; vm_compute; intuition discriminate.
Qed.

Lemma imr_metadata_store_frames_input : forall version e le m mb mo field rhs t le' m' out,
  field = IBM._flags \/ field = IBM._collidedObjInteractTypes -> imf_room mo ->
  le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (ics_field IBM._m IBM._MarioState field tuint) rhs) t le' m' out ->
  imf_input_load m' mb mo = imf_input_load m mb mo /\ t = E0 /\ out = Out_normal /\ le' = le.
Proof.
  intros version e le m mb mo field rhs t le' m' out Hfield Hroom Hm Hrun.
  destruct (imr_field version field Hfield) as [Hlayout Hrange].
  inversion Hrun; subst.
  lazymatch goal with Hl : eval_lvalue _ ?env ?temps ?memory _ _ _ _ |- _ =>
    destruct (ice_field_location (Clight.globalenv (selected_clight_target version)) env temps memory
      IBM._m IBM._MarioState field tuint mb mo (imr_offset field) _ _ _ Hm Hlayout Hl)
      as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  split.
  - unfold imf_input_load. eapply Mem.load_store_other; [eassumption|].
    right; left. cbn [size_chunk]. rewrite !imf_address by (auto; lia). lia.
  - repeat split; reflexivity.
Qed.

Inductive imr_safe : statement -> Prop :=
| imr_skip : imr_safe Sskip
| imr_set : forall id expr, id <> IBM._m -> imr_safe (Sset id expr)
| imr_store : forall field rhs,
    field = IBM._flags \/ field = IBM._collidedObjInteractTypes ->
    imr_safe (Sassign (ics_field IBM._m IBM._MarioState field tuint) rhs)
| imr_seq : forall first rest, imr_safe first -> imr_safe rest ->
    imr_safe (Ssequence first rest).

Lemma imr_safe_normal : forall s, imr_safe s -> ibk_normal s = true.
Proof. intros s H; induction H; cbn [ibk_normal]; auto; rewrite IHimr_safe1, IHimr_safe2; reflexivity. Qed.
Lemma imr_safe_execution : forall s, imr_safe s ->
  forall version e le m mb mo t le' m' out,
  imf_room mo -> le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' m' out ->
  imf_input_load m' mb mo = imf_input_load m mb mo /\ t = E0 /\ out = Out_normal /\
    le' ! IBM._m = le ! IBM._m.
Proof.
  intros s Hsafe. induction Hsafe; intros version e le m mb mo t le' m' out Hroom Hm Hrun.
  - inversion Hrun; subst. repeat split; reflexivity.
  - inversion Hrun; subst. repeat split; try reflexivity. apply PTree.gso. congruence.
  - destruct (imr_metadata_store_frames_input _ _ _ _ _ _ _ _ _ _ _ _ H Hroom Hm Hrun)
      as (Hsame & -> & -> & ->). repeat split; auto.
  - destruct (ibk_split_sequence _ _ _ _ first rest _ _ _ _ (imr_safe_normal _ Hsafe1) Hrun)
      as (middle & memory & pre & suf & Htrace & Hfirst & Hrest).
    destruct (IHHsafe1 _ _ _ _ _ _ _ _ _ _ Hroom Hm Hfirst)
      as (Hsame1 & Hpre & _ & Htemp1).
    destruct (IHHsafe2 _ _ _ _ _ _ _ _ _ _ Hroom (eq_trans Htemp1 Hm) Hrest)
      as (Hsame2 & Hsuf & Hout & Htemp2).
    split; [rewrite Hsame2; exact Hsame1|].
    split; [rewrite Htrace, Hpre, Hsuf; reflexivity|].
    split; [exact Hout|]. rewrite Htemp2, Htemp1. reflexivity.
Qed.

Lemma imr_actual_metadata_is_safe : forall version,
  imr_safe (ocn_prepend (imr_metadata version) Sskip).
Proof.
  intros []. all: unfold imr_metadata, ics_body; cbn [fn_body rank12b_drop_sequences ocn_prefix_items ocn_prepend].
  all: repeat first [apply imr_skip|apply imr_set; discriminate
    |apply imr_store; (left; reflexivity) || (right; reflexivity)|apply imr_seq].
Qed.

Definition InkInputResetToButtonCut : Prop :=
  forall version e le m mb mo t le' m' out,
  imf_room mo -> le ! IBM._m = Some (Vptr mb mo) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ics_body version ICInputs)) t le' m' out ->
  exists button_le button_m pre suf,
    t = pre ++ suf /\ button_le ! IBM._m = Some (Vptr mb mo) /\
    imf_input_load button_m mb mo = Some (Vint Int.zero) /\
    ocn_exec (Clight.globalenv (selected_clight_target version)) e button_le button_m
      (Ssequence (imr_button_call version) (imr_after_buttons version)) suf le' m' out.

Theorem imr_actual_input_body_reaches_buttons_with_zero_input : InkInputResetToButtonCut.
Proof.
  unfold InkInputResetToButtonCut.
  intros version e le m mb mo t le' m' out Hroom Hm Hrun.
  destruct (imr_source version) as (Hbody & _ & HfirstNormal & HfirstTemp & HmetaNormal).
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HfirstNormal Hrun)
    as (first_le & first_m & first_t & rest_t & Htrace & Hfirst & Hrest).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hfirst HfirstTemp) as Hkeep.
  assert (ibk_normal (ics_reset version) = true) as HresetNormal by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ HresetNormal Hrest)
    as (reset_le & reset_m & reset_t & meta_t & Htrace2 & Hreset & Hrest2).
  destruct (imr_reset_actual_store _ _ _ _ _ _ _ _ _ _ (eq_trans Hkeep Hm) Hreset)
    as (Hstore & HresetTrace & _ & HresetTemps). subst reset_le.
  assert (imf_input_load reset_m mb mo = Some (Vint Int.zero)) as Hzero.
  { unfold imf_input_load. rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore). reflexivity. }
  destruct (ibk_split_prefix _ _ _ _ _ _ _ _ _ _ HmetaNormal Hrest2)
    as (button_le & button_m & meta_trace & suffix & Htrace3 & Hmeta & Hsuffix).
  destruct (imr_safe_execution _ (imr_actual_metadata_is_safe version) version e first_le reset_m
    mb mo meta_trace button_le button_m Out_normal Hroom (eq_trans Hkeep Hm) Hmeta)
    as (Hsame & HmetaTrace & _ & Htemp).
  exists button_le, button_m, first_t, suffix.
  repeat split; try assumption; try congruence.
  subst. cbn. reflexivity.
Qed.
