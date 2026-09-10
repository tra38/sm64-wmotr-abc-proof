(** Exhaustive effect classification of the real joystick-input helper.
    The angle call is resolved and proved read-only, not assumed harmless.
    Successful executions preserve A-pressed, depth, action and its timer. *)
From Coq Require Import Bool List ZArith Lia.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkInputContinuationSource
  InkInputAngleFrame InkControllerSource InkControllerEdge InkMarioInputFlag
  InkBackwardSource InkBackwardExecution InkBodyResetFrame InkCopyCaller
  InkSharedReadings ObjectContactNecessity ContactConsumerExecution
  EyerokRank15LiveMovement SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iij_protected (cell : InkReadCell) mb :=
  ink_cell_block cell <> mb \/
  (ink_cell_offset cell + size_chunk (ink_cell_chunk cell) <= 2 \/
   (4 <= ink_cell_offset cell /\ ink_cell_offset cell + size_chunk (ink_cell_chunk cell) <= 32) \/
   38 <= ink_cell_offset cell).
Definition iij_frame mb m after := forall cell,
  iij_protected cell mb -> ink_read after cell = ink_read m cell.

Lemma iij_store_frame : forall m mb chunk offset value after,
  ((chunk = Mint16unsigned /\ offset = 2) \/
   (chunk = Mfloat32 /\ offset = 32) \/ (chunk = Mint16signed /\ offset = 36)) ->
  Mem.store chunk m mb offset value = Some after -> iij_frame mb m after.
Proof.
  intros m mb chunk offset value after Hkind Hstore cell Hprotected.
  apply (ibr_single_store_frames _ _ _ _ _ _ _ Hstore).
  unfold iij_protected in Hprotected. unfold ibr_cell_disjoint.
  destruct Hprotected as [Hother|Hoffset]; [left; exact Hother|right].
  destruct Hkind as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [size_chunk]; lia.
Qed.

Lemma iij_fields : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._intendedMag 32 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState IBM._intendedYaw 36 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._intendedMag 32 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._intendedYaw 36 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Inductive iij_statement : statement -> Prop :=
| iij_skip : iij_statement Sskip
| iij_set : forall id expr, id <> IBM._m -> iij_statement (Sset id expr)
| iij_store : forall field ty chunk delta rhs,
    ((field = IBM._intendedMag /\ ty = tfloat /\ chunk = Mfloat32 /\ delta = 32) \/
     (field = IBM._intendedYaw /\ ty = tshort /\ chunk = Mint16signed /\ delta = 36)) ->
    iij_statement (Sassign (ibr_field IBM._m IBM._MarioState field ty) rhs)
| iij_or : forall id mask, id <> IBM._m -> Int.testbit mask 1 = false ->
    iij_statement (imf_or_stage id mask)
| iij_angle : forall id args, id <> IBM._m -> iij_statement
    (Scall (Some id) (Evar (iis_ident IIAngle) (Tfunction [tfloat; tfloat] tshort cc_default)) args)
| iij_seq : forall first rest, iij_statement first -> iij_statement rest ->
    iij_statement (Ssequence first rest)
| iij_if : forall cond yes no, iij_statement yes -> iij_statement no ->
    iij_statement (Sifthenelse cond yes no).

Lemma iij_statement_normal : forall s, iij_statement s -> ibk_normal s = true.
Proof.
  intros s H; induction H; cbn [ibk_normal imf_or_stage]; auto;
    rewrite IHiij_statement1, IHiij_statement2; reflexivity.
Qed.

Lemma iij_real_body_classified : forall version,
  iij_statement (fn_body (iis_body version IIJoystick)).
Proof.
  intros []; cbn [iis_body fn_body].
  all: repeat first
    [apply iij_skip | apply iij_or; [discriminate|reflexivity]
    |eapply iij_store with (chunk := Mfloat32) (delta := 32); left; repeat split; reflexivity
    |eapply iij_store with (chunk := Mint16signed) (delta := 36); right; repeat split; reflexivity
    |apply iij_set; discriminate | apply iij_angle; discriminate | apply iij_seq | apply iij_if].
Qed.

Lemma iij_or_frame : forall version le m mb id mask t last after out,
  id <> IBM._m -> le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (imf_or_stage id mask) t last after out -> iij_frame mb m after.
Proof.
  intros version le m mb id mask t last after out Hid Hm Hrun.
  unfold imf_or_stage in Hrun.
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
  eapply iij_store_frame; [left; split; reflexivity|exact Hstore].
Qed.

Theorem iij_statement_effect : forall s, iij_statement s ->
  forall version le m mb before t last after out,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint16unsigned m mb 2 = Some (Vint before) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m s t last after out ->
  exists flags, Mem.load Mint16unsigned after mb 2 = Some (Vint flags) /\
    Int.testbit flags 1 = Int.testbit before 1 /\ t = E0 /\ out = Out_normal /\
    last ! IBM._m = le ! IBM._m /\ iij_frame mb m after.
Proof.
  intros s Hshape. induction Hshape; intros version le m mb before t last after out Hm Hinput Hrun.
  - inversion Hrun; subst. exists before. repeat split; auto; reflexivity.
  - inversion Hrun; subst. exists before. repeat split; auto.
    apply PTree.gso. congruence.
  - assert (ibcc_field_ok (Clight.globalenv (selected_clight_target version)) IBM._MarioState field delta = true /\
      access_mode ty = By_value chunk) as [Hlayout Hmode].
    { destruct H as [(-> & -> & -> & ->)|(-> & -> & -> & ->)];
        split; try reflexivity; apply iij_fields. }
    destruct (ibr_field_assignment_store _ empty_env le m IBM._m IBM._MarioState field ty delta chunk rhs
      t last after out mb Ptrofs.zero Hm Hlayout Hmode Hrun) as (-> & -> & -> & value & Hstore).
    assert (iij_frame mb m after) as Hframe.
    { destruct H as [(-> & -> & -> & ->)|(-> & -> & -> & ->)];
        eapply iij_store_frame; [right; left; split; reflexivity|exact Hstore|
          right; right; split; reflexivity|exact Hstore]. }
    assert (Mem.load Mint16unsigned after mb 2 = Some (Vint before)) as Hinput'.
    { rewrite <- Hinput. eapply Mem.load_store_other; [exact Hstore|]. right; left.
      destruct H as [(-> & -> & -> & ->)|(-> & -> & -> & ->)];
        [change (4 <= 32)|change (4 <= 36)]; lia. }
    exists before. repeat split; auto.
  - destruct (imf_or_stage_preserves_a version empty_env le m mb Ptrofs.zero id mask before
      t last after out H H0 Hm Hinput Hrun) as (flags & Hflags & Hbit & Htrace & Hout & Htemp).
    exists flags. split; [exact Hflags|]. split; [exact Hbit|]. split; [exact Htrace|].
    split; [exact Hout|]. split; [exact Htemp|]. eapply iij_or_frame; eauto.
  - destruct (iia_actual_named_call _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as (values & result & Hcall).
    destruct (iia_angle_call_preserves_memory _ _ _ _ _ _ Hcall) as (-> & ->).
    inversion Hrun; subst. exists before. split; [exact Hinput|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split.
    + apply PTree.gso. congruence.
    + intros cell Hprotected; reflexivity.
  - destruct (ibk_split_sequence _ _ _ _ first rest _ _ _ _ (iij_statement_normal _ Hshape1) Hrun)
      as (mid & memory & pre & suf & Htrace & Hfirst & Hrest).
    destruct (IHHshape1 _ _ _ _ _ _ _ _ _ Hm Hinput Hfirst)
      as (midflags & Hmid & Hbit1 & Hpre & _ & Htemp1 & Hframe1).
    destruct (IHHshape2 _ _ _ _ _ _ _ _ _ (eq_trans Htemp1 Hm) Hmid Hrest)
      as (flags & Hflags & Hbit2 & Hsuf & Hout & Htemp2 & Hframe2).
    exists flags. split; [exact Hflags|]. split; [congruence|].
    split; [rewrite Htrace, Hpre, Hsuf; reflexivity|]. split; [exact Hout|].
    split; [congruence|]. intros cell Hprotected. rewrite Hframe2, Hframe1 by exact Hprotected. reflexivity.
  - inversion Hrun; subst. destruct b; [eapply IHHshape1|eapply IHHshape2]; eauto.
Qed.

Theorem iij_completed_joystick_call_effect : forall version m mb before t after result,
  Mem.load Mint16unsigned m mb 2 = Some (Vint before) ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (iis_body version IIJoystick)) [Vptr mb Ptrofs.zero] t after result ->
  exists flags, Mem.load Mint16unsigned after mb 2 = Some (Vint flags) /\
    Int.testbit flags 1 = Int.testbit before 1 /\ t = E0 /\ iij_frame mb m after.
Proof.
  intros version m mb before t after result Hinput Hcall. inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite iis_helpers_have_no_stack_objects in Halloc; inversion Halloc; subst; clear Halloc end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  match goal with Hbind : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IBM._m = Some (Vptr mb Ptrofs.zero)) as Hm
      by (destruct version; cbn in Hbind; inversion Hbind; reflexivity) end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (iij_statement_effect _ (iij_real_body_classified version)
      _ _ _ _ _ _ _ _ _ Hm Hinput Hbody)
      as (flags & Hflags & Hbit & Htrace & _ & _ & Hframe) end.
  exists flags. auto.
Qed.
