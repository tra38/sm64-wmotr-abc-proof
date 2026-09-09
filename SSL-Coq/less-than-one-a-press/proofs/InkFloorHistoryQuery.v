(** The earlier movement/floor mismatch question belongs to the actual floor
    query. Its result store changes floorHeight, not movement Y. The query's
    own effects are retained explicitly rather than assumed read-only. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorHistorySource
  InkBackwardSource InkBackwardExecution InkCopyCaller InkFloorResetSource
  InkFloorResetExecution ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution EyerokRank15LiveMovement UpperElevatorQueryResolution
  SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma ifh_selected_floor_pointer_field : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version))
    IBM._MarioState IBM._floor 104 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    IBM._MarioState IBM._floor 104 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; reflexivity.
Qed.

Lemma ifh_movement_y_read : forall version e le m mb y answer,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_state_coord 1) answer -> answer = Vsingle y.
Proof.
  intros version e le m mb y answer Hm Hload Hread.
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ifr_state_y_location _ _ _ _ _ _ _ _ _ Hm Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb 64 = Some answer) in Hr; congruence end.
Qed.

Lemma ifh_floor_output_address : forall version e le m mb answer,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (Eaddrof ibk_floor_read (tptr (tptr (Tstruct IBM._Surface noattr)))) answer ->
  answer = Vptr mb (Ptrofs.repr 104).
Proof.
  intros version e le m mb answer Hm Hread.
  inversion Hread; subst.
  - lazymatch goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
      destruct (ibcc_field_location _ _ _ _ ibcc_state IBM._MarioState IBM._floor
        (tptr (Tstruct IBM._Surface noattr)) mb Ptrofs.zero 104 _ _ _ eq_refl
        ltac:(intros; eapply ibcc_deref_struct; eauto)
        (ifh_selected_floor_pointer_field version) Hl) as (-> & -> & _) end.
    reflexivity.
  - match goal with Hl : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Lemma ifh_float_cast_identity : forall m value answer,
  sem_cast value tfloat tfloat m = Some answer ->
  exists f, value = Vsingle f /\ answer = Vsingle f.
Proof.
  intros m [] answer Hcast; cbn in Hcast; try discriminate;
    inversion Hcast; subst; eauto.
Qed.

Lemma ifh_floor_result_store : forall version e le m mb id value t le' m' out,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) -> le ! id = Some value ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (Sassign ifr_floor_read (Etempvar id tfloat)) t le' m' out ->
  exists floor,
    value = Vsingle floor /\
    Mem.store Mfloat32 m mb 112 (Vsingle floor) = Some m' /\
    Mem.load Mfloat32 m' mb 112 = Some (Vsingle floor) /\
    Mem.load Mfloat32 m' mb 64 = Mem.load Mfloat32 m mb 64 /\
    t = E0 /\ le' = le /\ out = Out_normal.
Proof.
  intros version e le m mb id value t le' m' out Hm Hvalue Hrun.
  inversion Hrun; subst.
  match goal with Hl : eval_lvalue _ _ _ _ ifr_floor_read _ _ _ |- _ =>
    destruct (ibcc_field_location _ _ _ _ ibcc_state IBM._MarioState IBM._floorHeight
      tfloat mb Ptrofs.zero 112 _ _ _ eq_refl
      ltac:(intros; eapply ibcc_deref_struct; eauto)
      (ifr_selected_floor_field version) Hl) as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar id _) ?v |- _ =>
    assert (v = value) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    destruct (ifh_float_cast_identity _ _ _ Hcast) as (floor & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
    change (Mem.store Mfloat32 m mb 112 (Vsingle floor) = Some m') in Hstore end.
  exists floor. repeat split; try reflexivity; try assumption.
  - match goal with Hstored : Mem.store _ _ _ _ _ = Some _ |- _ =>
      exact (Mem.load_store_same _ _ _ _ _ _ Hstored) end.
  - eapply Mem.load_store_other; [eassumption|right; left; cbn; lia].
Qed.

Definition InkPrimaryFloorQueryHeightCut : Prop :=
  forall version e le m mb y t le' m' out,
  e ! IBM._find_floor = None ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle y) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_geometry_query version) t le' m' out ->
  exists x z floor query_m,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle x; Vsingle y; Vsingle z; Vptr mb (Ptrofs.repr 104)]
      t query_m (Vsingle floor) /\
    Mem.store Mfloat32 query_m mb 112 (Vsingle floor) = Some m' /\
    Mem.load Mfloat32 m' mb 112 = Some (Vsingle floor) /\
    Mem.load Mfloat32 m' mb 64 = Mem.load Mfloat32 query_m mb 64 /\
    out = Out_normal.

Theorem ifh_primary_floor_query_uses_movement_y_and_stores_result : InkPrimaryFloorQueryHeightCut.
Proof.
  unfold InkPrimaryFloorQueryHeightCut.
  intros version e le m mb y t le' m' out Hlocal Hm Hy Hrun.
  destruct (ifh_geometry_source_cuts version)
    as (_ & _ & Hshape & Hquery & Hstore & _).
  rewrite Hshape in Hrun.
  assert (ibk_normal (ifh_geometry_query_call version) = true) as Hnormal
    by (destruct version; reflexivity).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (store_le & query_m & query_trace & store_trace & Htrace & Hcall & Hwrite).
  assert (ifr_keeps_temp IBM._m (ifh_geometry_query_call version) = true) as Hkeep
    by (destruct version; reflexivity).
  pose proof (ifr_execution_keeps_temp _ _ _ _ _ _ _ _ _ _ Hcall Hkeep) as HmSame.
  rewrite Hquery in Hcall.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hcall.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: lazymatch goal with Hr : eval_expr ?ge ?env ?temps ?memory (ifh_state_coord 1) ?v |- _ =>
    assert (v = Vsingle y) by (eapply (ifh_movement_y_read version env temps memory mb y v);
      [rewrite PTree.gso by discriminate; exact Hm|exact Hy|exact Hr]); subst v end.
  match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ ifh_geometry_find_floor _ _ _ _ |- _ =>
    inversion Hc; subst; clear Hc end.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (upper_elevator_selected_query_body_resolves version UEQRFindFloor)
    as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hr; subst; clear Hr end.
  match goal with Hr : eval_expr _ _ ?temps _ (Etempvar IBM._t'47 _) ?v |- _ =>
    assert (v = Vsingle y) by (eapply ocn_temp_value;
      [exact Hr|rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Eaddrof ibk_floor_read _) ?v |- _ =>
    assert (v = Vptr mb (Ptrofs.repr 104)) by
      (eapply (ifh_floor_output_address version env temps memory mb v);
      [repeat rewrite PTree.gso by discriminate; exact Hm|exact Hr]); subst v end.
  repeat match goal with Hcast : sem_cast ?value ?ty tfloat ?memory = Some ?answer |- _ =>
    change (sem_cast value tfloat tfloat memory = Some answer) in Hcast;
    destruct (ifh_float_cast_identity _ _ _ Hcast) as (? & ? & ?); subst; clear Hcast end.
  repeat match goal with Heq : Vsingle _ = Vsingle _ |- _ =>
    inversion Heq; subst; clear Heq end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  rewrite Hstore in Hwrite.
  lazymatch type of Hwrite with ocn_exec ?ge ?env ?temps ?memory _ ?tr ?last ?final ?o =>
    destruct (ifh_floor_result_store version env temps memory mb IBM._t'1 _ tr last final o
      ltac:(cbn [set_opttemp]; repeat rewrite PTree.gso by discriminate; exact Hm)
      ltac:(cbn [set_opttemp]; apply PTree.gss) Hwrite)
      as (floor & Hresult & Hstored & Hloaded & Hmovement & Ht & Hl & Ho) end.
  subst. unfold Eapp, E0. rewrite ?app_nil_r.
  match goal with Hactual : ClightBigstep.eval_funcall _ _ _
    (Internal (ueqr_native_body _ UEQRFindFloor))
    [Vsingle ?x; _; Vsingle ?z; _] _ ?memory (Vsingle ?height) |- _ =>
    exists x, z, height, memory end.
  repeat apply conj; try reflexivity; eassumption.
Qed.
