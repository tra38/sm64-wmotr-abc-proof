(** Vertical effect of the actual nonrotating platform branch.
    Translation adds only oVelX/oVelZ. The no-rotation tail passes local Y
    unchanged to the real set_mario_pos and completes its three stores.

    These are reached cuts after get_mario_pos and after the rotation test.
    Deriving their local bindings and the zero test from the complete entry
    remains separate; yaw/pitch/roll matrix branches are not covered here. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkPlatformMovement
  InkPlatformMovementSource InkPlatformWriteFrame InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkFloorResetExecution
  InkRawCopyExpressions ObjectContactNecessity ContactConsumerExecution
  SelectedClightTarget Area2Rank12BContact InkFloorHistoryQuery.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module IPH := us_platform_displacement.

Definition iph_translation version := ocn_prepend
  (ocn_prefix_items 2 (rank12b_drop_sequences 4 (fn_body (ipm_body version None)))) Sskip.
Definition iph_rotation version := ibk_head
  (rank12b_drop_sequences 6 (fn_body (ipm_body version None))).
Definition iph_rotation_test version := match iph_rotation version with
| Ssequence test _ => test | _ => Sskip end.
Definition iph_rotation_gate version := match iph_rotation version with
| Ssequence _ gate => gate | _ => Sskip end.
Definition iph_commit version := rank12b_drop_sequences 7 (fn_body (ipm_body version None)).
Definition iph_no_rotation_tail version :=
  Ssequence (iph_rotation_gate version) (iph_commit version).
Definition iph_mario_commit version := match iph_commit version with
| Sifthenelse _ yes _ => yes | _ => Sskip end.
Definition iph_set_call := Scall None
  (Evar IPH._set_mario_pos (Tfunction [tfloat;tfloat;tfloat] tvoid cc_default))
  [Etempvar IPH._t'9 tfloat;Etempvar IPH._t'10 tfloat;Etempvar IPH._t'11 tfloat].

Lemma iph_generated_cuts : forall version,
  ipw_shape [IPH._x;IPH._z] [] [] (fun _ _ => false) (iph_translation version) = true /\
  ifr_keeps_temp IPH._isMario (iph_translation version) = true /\
  cce_readonly_keep IPH._isMario (iph_rotation_test version) = true /\
  iph_rotation_gate version = Sifthenelse (Etempvar IPH._t'2 tint)
    (match iph_rotation_gate version with Sifthenelse _ yes _ => yes | _ => Sskip end) Sskip /\
  iph_commit version = Sifthenelse (Etempvar IPH._isMario tuint)
    (iph_mario_commit version)
    (match iph_commit version with Sifthenelse _ _ no => no | _ => Sskip end) /\
  iph_mario_commit version = Ssequence (Sset IPH._t'9 (Evar IPH._x tfloat))
    (Ssequence (Sset IPH._t'10 (Evar IPH._y tfloat))
      (Ssequence (Sset IPH._t'11 (Evar IPH._z tfloat)) iph_set_call)).
Proof. intros []; repeat split; reflexivity. Qed.

(** Only two real scalar local allocations are required to be distinct
    from the Y local. No Object-pool or callee frame is a premise. *)
Theorem iph_horizontal_translation_preserves_local_y :
  forall version e le m xb yb zb t le' after out,
  e ! IPH._x = Some (xb,tfloat) -> e ! IPH._y = Some (yb,tfloat) ->
  e ! IPH._z = Some (zb,tfloat) -> xb <> yb -> zb <> yb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iph_translation version) t le' after out ->
  Mem.load Mfloat32 after yb 0 = Mem.load Mfloat32 m yb 0 /\
  le' ! IPH._isMario = le ! IPH._isMario.
Proof.
  intros version e le m xb yb zb t le' after out Hx Hy Hz Hxy Hzy Hrun.
  split.
  - destruct (ipw_checked_frame (Clight.globalenv (selected_clight_target version)) e yb
      [IPH._x;IPH._z] [] [] (fun _ _ => false)
      ltac:(intros; discriminate) le m (iph_translation version) t le' after out Hrun
      (proj1 (iph_generated_cuts version)) ltac:(
        split;
        [ intros id [<-|[<-|[]]]; split;
          [intros b ty Hr; rewrite Hx in Hr; inversion Hr; congruence|
           intros Hnone; rewrite Hx in Hnone; discriminate|
           intros b ty Hr; rewrite Hz in Hr; inversion Hr; congruence|
           intros Hnone; rewrite Hz in Hnone; discriminate]
        |split; intros; contradiction])) as (_ & Hframe & _).
    apply Hframe.
  - eapply ifr_execution_keeps_temp; [exact Hrun|].
    exact (proj1 (proj2 (iph_generated_cuts version))).
Qed.

Theorem iph_rotation_test_preserves_local_y :
  forall version e le m t le' after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iph_rotation_test version) t le' after out -> after = m.
Proof.
  intros version e le m t le' after out Hrun.
  exact (proj1 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun
    (proj1 (proj2 (proj2 (iph_generated_cuts version))))))).
Qed.

Definition iph_state := Ederef
  (Ebinop Oadd (Evar IPH._gMarioStates (tarray (Tstruct IPH._MarioState noattr) 0))
    (Econst_int Int.zero tint) (tptr (Tstruct IPH._MarioState noattr)))
  (Tstruct IPH._MarioState noattr).
Definition iph_position := Efield iph_state IPH._pos (tarray tfloat 3).
Definition iph_coord n := Ederef (Ebinop Oadd iph_position
  (Econst_int (Int.repr n) tint) (tptr tfloat)) tfloat.
Definition iph_set_stage version n := match
  rank12b_drop_sequences (Z.to_nat n) (fn_body (ipm_body version (Some IPLSet))) with
| Ssequence head _ => head | final => final end.

Lemma iph_set_source : forall version,
  fn_vars (ipm_body version (Some IPLSet)) = [] /\
  fn_params (ipm_body version (Some IPLSet)) = [(IPH._x,tfloat);(IPH._y,tfloat);(IPH._z,tfloat)] /\
  fn_body (ipm_body version (Some IPLSet)) = Ssequence (iph_set_stage version 0)
    (Ssequence (iph_set_stage version 1) (iph_set_stage version 2)) /\
  iph_set_stage version 0 = Sassign (iph_coord 0) (Etempvar IPH._x tfloat) /\
  iph_set_stage version 1 = Sassign (iph_coord 1) (Etempvar IPH._y tfloat) /\
  iph_set_stage version 2 = Sassign (iph_coord 2) (Etempvar IPH._z tfloat).
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iph_state_value : forall version e le m mb answer,
  e ! IPH._gMarioStates = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m iph_state answer ->
  answer = Vptr mb Ptrofs.zero.
Proof.
  intros version e le m mb answer Hlocal Hsymbol Hread.
  unfold iph_state in Hread.
  repeat match goal with
  | H : eval_expr _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  | H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  end; try congruence.
  repeat match goal with Hd : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hd; subst; clear Hd; try discriminate end.
  match goal with Hsym : Genv.find_symbol _ IPH._gMarioStates = Some ?b |- _ =>
    assert (b = mb) by congruence; subst b end.
  lazymatch goal with Hsem : sem_binary_operation _ Oadd _ _ _ _ _ = Some ?value |- _ =>
    cbn [typeof] in Hsem;
    change (Some (Vptr mb (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (sizeof (Clight.globalenv (selected_clight_target version))
        (Tstruct IPH._MarioState noattr))) Ptrofs.zero))) = Some value) in Hsem;
    rewrite Ptrofs.mul_zero, Ptrofs.add_zero in Hsem; inversion Hsem; reflexivity end.
Qed.

Lemma iph_coord_location : forall version e le m mb n b ofs bf,
  e ! IPH._gMarioStates = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  eval_lvalue (Clight.globalenv (selected_clight_target version)) e le m
    (iph_coord n) b ofs bf ->
  b = mb /\ ofs = Ptrofs.add (Ptrofs.repr 60)
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))) /\ bf = Full.
Proof.
  intros version e le m mb n b ofs bf Hlocal Hsymbol Hl.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iph_position v -> v = Vptr mb (Ptrofs.repr 60)) as Hbase.
  { intros. eapply ibcc_aggregate_field with (base := iph_state)
      (tag := IPH._MarioState) (field := IPH._pos) (ty := tarray tfloat 3)
      (b := mb) (ofs := Ptrofs.zero) (delta := 60);
      [reflexivity| |exact (proj1 (ibcc_selected_fields version))|left; reflexivity|eassumption].
    intros. eapply iph_state_value; eauto. }
  unfold iph_coord in Hl.
  eapply (ifr_array_index_location
    (Clight.globalenv (selected_clight_target version)) e le m iph_position n
    mb (Ptrofs.repr 60) b ofs bf); [reflexivity|exact Hbase|exact Hl].
Qed.

Lemma iph_scalar_local_read : forall ge e le m id b height value,
  e ! id = Some (b,tfloat) -> Mem.load Mfloat32 m b 0 = Some (Vsingle height) ->
  eval_expr ge e le m (Evar id tfloat) value -> value = Vsingle height.
Proof.
  intros ge e le m id b height value He Hy Hr.
  inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ He Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hl : Mem.loadv _ _ _ = Some value |- _ =>
    change (Mem.load Mfloat32 m b 0 = Some value) in Hl; congruence end.
Qed.

Definition iph_rotation_index n := Ederef
  (Ebinop Oadd (Evar IPH._rotation (tarray tshort 3))
    (Econst_int (Int.repr n) tint) (tptr tshort)) tshort.

Lemma iph_rotation_array_value : forall ge e le m rb value,
  e ! IPH._rotation = Some (rb,tarray tshort 3) ->
  eval_expr ge e le m (Evar IPH._rotation (tarray tshort 3)) value ->
  value = Vptr rb Ptrofs.zero.
Proof.
  intros ge e le m rb value He Hr. inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ He Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst end.
  all: try solve [match goal with Hmode : access_mode _ = _ |- _ => cbn in Hmode; discriminate end].
  all: reflexivity.
Qed.

Lemma iph_rotation_location : forall ge e le m rb n b ofs bf,
  e ! IPH._rotation = Some (rb,tarray tshort 3) ->
  eval_lvalue ge e le m (iph_rotation_index n) b ofs bf ->
  b = rb /\ ofs = Ptrofs.mul (Ptrofs.repr 2)
    (ptrofs_of_int Signed (Int.repr n)) /\ bf = Full.
Proof.
  intros ge e le m rb n b ofs bf He Hl.
  unfold iph_rotation_index in Hl. inversion Hl; subst.
  match goal with Hb : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    inversion Hb; subst; clear Hb end.
  - match goal with Hr : eval_expr _ _ _ _ (Evar IPH._rotation _) ?v |- _ =>
      assert (v = Vptr rb Ptrofs.zero) by (eapply iph_rotation_array_value; eauto); subst v end.
    match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      apply ocn_const_int_value in Hr; subst end.
    match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn in Hsem; inversion Hsem; subst end.
    rewrite Ptrofs.add_zero_l. repeat split; reflexivity.
  - match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end.
Qed.

Lemma iph_zero_rotation_cell_read : forall ge e le m rb n value,
  In n [0;1;2] -> e ! IPH._rotation = Some (rb,tarray tshort 3) ->
  Mem.load Mint16signed m rb (2*n) = Some (Vint Int.zero) ->
  eval_expr ge e le m (iph_rotation_index n) value -> value = Vint Int.zero.
Proof.
  intros ge e le m rb n value Hn He Hz Hr. inversion Hr; subst.
  match goal with Hl : eval_lvalue _ _ _ _ (iph_rotation_index _) _ _ _ |- _ =>
    destruct (iph_rotation_location _ _ _ _ _ _ _ _ _ He Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  assert (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 2)
    (ptrofs_of_int Signed (Int.repr n))) = 2*n) as Hoff.
  { destruct Hn as [<-|[<-|[<-|[]]]]; reflexivity. }
  match goal with Hload : Mem.loadv _ _ _ = Some value |- _ =>
    change (Mem.load Mint16signed m rb
      (Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 2)
        (ptrofs_of_int Signed (Int.repr n)))) = Some value) in Hload;
    rewrite Hoff in Hload; congruence end.
Qed.

(** Zero means the three signed-16 rotation cells actually consumed by the
    generated short-circuit test. No matrix or rotation helper is reached. *)
Theorem iph_zero_live_rotation_produces_zero_test :
  forall version e le m rb t le' after out,
  e ! IPH._rotation = Some (rb,tarray tshort 3) ->
  Mem.load Mint16signed m rb 0 = Some (Vint Int.zero) ->
  Mem.load Mint16signed m rb 2 = Some (Vint Int.zero) ->
  Mem.load Mint16signed m rb 4 = Some (Vint Int.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iph_rotation_test version) t le' after out ->
  after = m /\ le' ! IPH._t'2 = Some (Vint Int.zero).
Proof.
  intros version e le m rb t le' after out He H0 H1 H2 Hrun.
  pose proof (iph_rotation_test_preserves_local_y _ _ _ _ _ _ _ _ Hrun) as Hmemory.
  split; [exact Hmemory|].
  assert (iph_rotation_test version = iph_rotation_test VersionUS) as Htest.
  { destruct version; reflexivity. }
  rewrite Htest in Hrun.
  cbv [iph_rotation_test iph_rotation ipm_body rank12b_drop_sequences ibk_head fn_body
    us_platform_displacement.f_apply_platform_displacement] in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: fold (iph_rotation_index 0) (iph_rotation_index 1) (iph_rotation_index 2) in *.
  all: repeat first
    [ match goal with Hr : eval_expr ?ge ?env ?temps ?memory (iph_rotation_index ?n) ?v |- _ =>
        assert (v = Vint Int.zero) by
          (eapply (iph_zero_rotation_cell_read ge env temps memory rb n v);
            [cbn; auto|exact He|first [exact H0|exact H1|exact H2]|exact Hr]);
        subst v; clear Hr end
    | match goal with Hr : eval_expr _ _ _ _ (Ebinop One _ _ _) _ |- _ =>
        inversion Hr; subst; clear Hr end
    | match goal with Hr : eval_expr _ _ _ _ (Ecast _ _) _ |- _ =>
        inversion Hr; subst; clear Hr end
    | match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
        apply ocn_const_int_value in Hr; subst end
    | match goal with Hr : eval_expr _ _ _ _ (Etempvar _ _) ?v |- _ =>
        assert (v = Vint Int.zero) by
          (eapply ocn_temp_value; [exact Hr|repeat rewrite PTree.gso by discriminate; apply PTree.gss]);
        subst v; clear Hr end
    | match goal with Hsem : sem_binary_operation _ One (Vint ?a) _
        (Vint ?b) _ _ = Some ?answer |- _ =>
        change (Some (Vint Int.zero) = Some answer) in Hsem;
        inversion Hsem; subst; clear Hsem end
    | match goal with Hcast : sem_cast (Vint Int.zero) _ _ _ = Some ?answer |- _ =>
        change (Some (Vint Int.zero) = Some answer) in Hcast;
        inversion Hcast; subst; clear Hcast end
    | match goal with Hbool : bool_val (Vint Int.zero) _ _ = Some ?bit |- _ =>
        change (Some false = Some bit) in Hbool;
        inversion Hbool; subst; clear Hbool end
    | match goal with Hbad : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion Hbad end
    | match goal with Hbad : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion Hbad end
    | contradiction ].
  all: apply PTree.gss.
Qed.

Lemma iph_set_stage_store : forall version e le m mb n id height t le' after out,
  In n [0;1;2] ->
  e ! IPH._gMarioStates = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  le ! id = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign (iph_coord n) (Etempvar id tfloat)) t le' after out ->
  Mem.store Mfloat32 m mb (60 + 4*n) (Vsingle height) = Some after.
Proof.
  intros version e le m mb n id height t le' after out Hn Hlocal Hsymbol Hvalue Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ (iph_coord _) _ _ _ |- _ =>
    destruct (iph_coord_location _ _ _ _ _ _ _ _ _ Hlocal Hsymbol Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar id _) ?v |- _ =>
    assert (v = Vsingle height) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hcast; inversion Hcast; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  destruct Hn as [<-|[<-|[<-|[]]]]; eassumption.
Qed.

Theorem iph_completed_setter_writes_argument_y :
  forall version m mb x y z t after result,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version)) m
    (Internal (ipm_body version (Some IPLSet))) [Vsingle x;Vsingle y;Vsingle z]
    t after result -> Mem.load Mfloat32 after mb 64 = Some (Vsingle y).
Proof.
  intros version m mb x y z t after result Hsymbol Hcall.
  destruct (iph_set_source version) as (Hvars & Hparams & Hbody & Hx & Hy & Hz).
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ => inversion He; subst; clear He end.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some ?temps |- _ =>
    assert (temps ! IPH._y = Some (Vsingle y) /\ temps ! IPH._z = Some (Vsingle z))
      as [HargY HargZ] by (rewrite Hparams in Hb; cbn in Hb; inversion Hb; subst;
        split; repeat rewrite PTree.gso by discriminate; apply PTree.gss) end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite Hbody in Hr;
    destruct (ibk_split_sequence _ _ _ _ (iph_set_stage version 0) _ _ _ _ _
      ltac:(destruct version; reflexivity) Hr) as (xl & xm & xt & yr & Hxt & Hfirst & Hrest) end.
  assert (xl ! IPH._y = Some (Vsingle y) /\ xl ! IPH._z = Some (Vsingle z)) as [HargY1 HargZ1].
  { split; (erewrite ifr_execution_keeps_temp; [eassumption|exact Hfirst|destruct version; reflexivity]). }
  destruct (ibk_split_sequence _ _ _ _ (iph_set_stage version 1) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrest) as (yl & ym & yt & zt & Hyt & Hsecond & Hthird).
  rewrite Hy in Hsecond.
  pose proof (iph_set_stage_store version empty_env xl xm mb 1 IPH._y y yt yl ym Out_normal
    ltac:(cbn; auto) (PTree.gempty _ _) Hsymbol HargY1 Hsecond) as Hys.
  assert (yl ! IPH._z = Some (Vsingle z)) as HargZ2.
  { erewrite ifr_execution_keeps_temp; [exact HargZ1|exact Hsecond|reflexivity]. }
  rewrite Hz in Hthird.
  pose proof (iph_set_stage_store version empty_env yl ym mb 2 IPH._z z _ _ _ _
    ltac:(cbn; auto) (PTree.gempty _ _) Hsymbol HargZ2 Hthird) as Hzs.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?final |- _ =>
    change (Some before = Some final) in Hfree; inversion Hfree; subst end.
  erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ Hys)|
    exact Hzs|right; left; cbn; lia].
Qed.

Theorem iph_nonrotating_mario_tail_writes_unchanged_y :
  forall version e le m mb yb y t le' after out,
  e ! IPH._set_mario_pos = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  e ! IPH._y = Some (yb,tfloat) -> Mem.load Mfloat32 m yb 0 = Some (Vsingle y) ->
  le ! IPH._t'2 = Some (Vint Int.zero) -> le ! IPH._isMario = Some (Vint Int.one) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iph_no_rotation_tail version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle y).
Proof.
  intros version e le m mb yb y t le' after out Hlocal Hsymbol HyLocal Hy Hzero Hmario Hrun.
  unfold iph_no_rotation_tail in Hrun.
  destruct (iph_generated_cuts version) as (_ & _ & _ & Hgate & Hcommit & Hyes).
  rewrite Hgate in Hrun. inversion Hrun; subst.
  all: match goal with Hg : ClightBigstep.exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
    inversion Hg; subst; clear Hg end.
  all: match goal with Hr : eval_expr _ _ _ _ (Etempvar IPH._t'2 _) ?v |- _ =>
    assert (v = Vint Int.zero) by (eapply ocn_temp_value; eauto); subst v end.
  all: match goal with Hb : bool_val (Vint Int.zero) _ _ = Some _ |- _ =>
    change (Some false = Some b) in Hb; inversion Hb; subst end.
  all: match goal with Hs : ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ =>
    inversion Hs; subst end.
  2: contradiction.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (iph_commit version) _ _ _ _ |- _ =>
    rewrite Hcommit in Hr; inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IPH._isMario _) ?v |- _ =>
    assert (v = Vint Int.one) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hb : bool_val (Vint Int.one) _ _ = Some _ |- _ =>
    change (Some true = Some b) in Hb; inversion Hb; subst end.
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (iph_mario_commit version) _ _ _ _ |- _ =>
    rewrite Hyes in Hr; unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hr;
    cce_unroll_loop_free_exec end.
  all: try contradiction.
  match goal with Hr : eval_expr _ _ _ _ (Evar IPH._y tfloat) ?v |- _ =>
    assert (v = Vsingle y) by (eapply iph_scalar_local_read; eauto); subst v end.
  match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ iph_set_call _ _ _ _ |- _ =>
    destruct (ipm_reached_call version IPLSet _ _ _ _ _ _ _ _ _ _ _ _ Hlocal Hc)
      as (values & result & Hargs & Hcall) end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IPH._t'10 _) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ocn_temp_value;
      [exact Hr|rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  repeat match goal with Hcast : sem_cast ?value ?ty tfloat ?memory = Some ?answer |- _ =>
    change (sem_cast value tfloat tfloat memory = Some answer) in Hcast;
    destruct (ifh_float_cast_identity _ _ _ Hcast) as (? & ? & ?); subst; clear Hcast end.
  repeat match goal with Heq : Vsingle _ = Vsingle _ |- _ => inversion Heq; subst; clear Heq end.
  eapply iph_completed_setter_writes_argument_y; [exact Hsymbol|eassumption].
Qed.

Corollary iph_nonrotating_tail_has_no_new_vertical_change :
  forall version e le m mb yb y t le' after out,
  e ! IPH._set_mario_pos = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
  e ! IPH._y = Some (yb,tfloat) -> Mem.load Mfloat32 m yb 0 = Some (Vsingle y) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  le ! IPH._t'2 = Some (Vint Int.zero) -> le ! IPH._isMario = Some (Vint Int.one) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iph_no_rotation_tail version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Mem.load Mfloat32 m mb 64.
Proof.
  intros version e le m mb yb y t le' after out Hset Hsymbol Hlocal Hy Hstate Hzero Hmario Hrun.
  rewrite (iph_nonrotating_mario_tail_writes_unchanged_y version e le m mb yb y
    t le' after out Hset Hsymbol Hlocal Hy Hzero Hmario Hrun), Hstate.
  reflexivity.
Qed.

Definition InkPlatformNonrotationHeightBoundary : Prop :=
  (forall version e le m rb t le' after out,
    e ! IPH._rotation = Some (rb,tarray tshort 3) ->
    Mem.load Mint16signed m rb 0 = Some (Vint Int.zero) ->
    Mem.load Mint16signed m rb 2 = Some (Vint Int.zero) ->
    Mem.load Mint16signed m rb 4 = Some (Vint Int.zero) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (iph_rotation_test version) t le' after out ->
    after = m /\ le' ! IPH._t'2 = Some (Vint Int.zero)) /\
  (forall version e le m xb yb zb t le' after out,
    e ! IPH._x = Some (xb,tfloat) -> e ! IPH._y = Some (yb,tfloat) ->
    e ! IPH._z = Some (zb,tfloat) -> xb <> yb -> zb <> yb ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (iph_translation version) t le' after out ->
    Mem.load Mfloat32 after yb 0 = Mem.load Mfloat32 m yb 0 /\
    le' ! IPH._isMario = le ! IPH._isMario) /\
  (forall version e le m mb yb y t le' after out,
    e ! IPH._set_mario_pos = None ->
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) IPH._gMarioStates = Some mb ->
    e ! IPH._y = Some (yb,tfloat) -> Mem.load Mfloat32 m yb 0 = Some (Vsingle y) ->
    le ! IPH._t'2 = Some (Vint Int.zero) -> le ! IPH._isMario = Some (Vint Int.one) ->
    ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
      (iph_no_rotation_tail version) t le' after out ->
    Mem.load Mfloat32 after mb 64 = Some (Vsingle y)).

Theorem iph_platform_nonrotation_height_checked : InkPlatformNonrotationHeightBoundary.
Proof.
  split; [exact iph_zero_live_rotation_produces_zero_test|].
  split; [exact iph_horizontal_translation_preserves_local_y|
    exact iph_nonrotating_mario_tail_writes_unchanged_y].
Qed.
