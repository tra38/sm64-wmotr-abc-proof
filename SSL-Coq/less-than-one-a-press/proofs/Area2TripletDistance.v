(** The live distance helper, including its six Object reads and return.
    Its only call is the actual named sqrtf call. No numerical or memory
    contract for that unresolved external is silently supplied here. *)
From Coq Require Import List ZArith Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import Area2TripletSpawner
  GameTypes ObjectContactReadback ObjectContactNecessity EyerokRank15LiveMovement
  Area2Rank9ACoinFlight SelectedClightTarget
  InkScheduledActionSource InkBackwardExecution ContactConsumerExecution
  SecretContactExecution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition td_position m b ofs p :=
  Mem.load Mfloat32 m b
    (Ptrofs.unsigned (rank15_raw_address ofs (Int.repr 6))) = Some (Vsingle (vec_x p)) /\
  Mem.load Mfloat32 m b
    (Ptrofs.unsigned (rank15_raw_address ofs (Int.repr 7))) = Some (Vsingle (vec_y p)) /\
  Mem.load Mfloat32 m b
    (Ptrofs.unsigned (rank15_raw_address ofs (Int.repr 8))) = Some (Vsingle (vec_z p)).

Definition td_squared a b :=
  let dx := Float32.sub (vec_x a) (vec_x b) in
  let dy := Float32.sub (vec_y a) (vec_y b) in
  let dz := Float32.sub (vec_z a) (vec_z b) in
  Float32.add (Float32.add (Float32.mul dx dx) (Float32.mul dy dy))
    (Float32.mul dz dz).
Definition td_difference version n first second delta :=
  Ssequence (Sset first (ocr_position version TD._obj1 n))
    (Ssequence (Sset second (ocr_position version TD._obj2 n))
      (Sset delta (Ebinop Osub (Etempvar first tfloat)
        (Etempvar second tfloat) tfloat))).
Definition td_prefix version :=
  ocn_prepend (ocn_prefix_items 3 (fn_body (ts_distance_body version))) Sskip.
Definition td_tail := Ssequence
  (Scall (Some TD._t'1) (Evar TD._sqrtf (Tfunction [tfloat] tfloat cc_default))
    [ts_squared_expression]) (Sreturn (Some (Etempvar TD._t'1 tfloat))).
Definition td_locals le a b :=
  PTree.set TD._dz (Vsingle (Float32.sub (vec_z a) (vec_z b)))
  (PTree.set TD._t'3 (Vsingle (vec_z b))
  (PTree.set TD._t'2 (Vsingle (vec_z a))
  (PTree.set TD._dy (Vsingle (Float32.sub (vec_y a) (vec_y b)))
  (PTree.set TD._t'5 (Vsingle (vec_y b))
  (PTree.set TD._t'4 (Vsingle (vec_y a))
  (PTree.set TD._dx (Vsingle (Float32.sub (vec_x a) (vec_x b)))
  (PTree.set TD._t'7 (Vsingle (vec_x b))
  (PTree.set TD._t'6 (Vsingle (vec_x a)) le)))))))).

Lemma td_source : forall version,
  td_prefix version = ocn_prepend
    [td_difference version 0 TD._t'6 TD._t'7 TD._dx;
     td_difference version 1 TD._t'4 TD._t'5 TD._dy;
     td_difference version 2 TD._t'2 TD._t'3 TD._dz] Sskip /\
  fn_body (ts_distance_body version) =
    ocn_prepend (ocn_prefix_items 3 (fn_body (ts_distance_body version))) td_tail /\
  ocr_readonly_prefix (td_prefix version) = true /\
  forallb ocn_normal_prefix
    (ocn_prefix_items 3 (fn_body (ts_distance_body version))) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma td_reads_execute : forall version e le m ab ao a bb bo b,
  le ! TD._obj1 = Some (Vptr ab ao) -> le ! TD._obj2 = Some (Vptr bb bo) ->
  td_position m ab ao a -> td_position m bb bo b ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (td_prefix version) E0 (td_locals le a b) m Out_normal.
Proof.
  intros version e le m ab ao a bb bo b Ha Hb (Hax & Hay & Haz) (Hbx & Hby & Hbz).
  assert (forall locals temp n block offset value,
    locals ! temp = Some (Vptr block offset) ->
    Mem.load Mfloat32 m block (Ptrofs.unsigned
      (rank15_raw_address offset (Int.add (Int.repr 6) (Int.repr n)))) = Some (Vsingle value) ->
    eval_expr (Clight.globalenv (selected_clight_target version)) e locals m
      (ocr_position version temp n) (Vsingle value)) as Hposition.
  { intros. eapply rank15_raw_float_read; eauto using ocr_index_evaluates. }
  rewrite (proj1 (td_source version)). unfold ocn_prepend, td_difference, td_locals.
  repeat first
    [apply exec_Sskip
    |eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    |apply exec_Sset
    |eapply Hposition; [repeat (rewrite PTree.gso by discriminate); eassumption|eassumption]
    |eapply eval_Ebinop; [apply eval_Etempvar; rank15_temporary|
       apply eval_Etempvar; rank15_temporary|reflexivity]].
Qed.

Lemma td_argument_exact : forall ge e le m a b args,
  eval_exprlist ge e (td_locals le a b) m [ts_squared_expression] [tfloat] args ->
  args = [Vsingle (td_squared a b)].
Proof.
  intros ge e le m a b args Hargs. inversion Hargs; subst.
  match goal with Hr : eval_expr _ _ _ _ ts_squared_expression ?v |- _ =>
    assert (v = Vsingle (td_squared a b)) by
      (eapply ocr_expr_unique; [exact Hr|unfold td_squared;
        apply ts_squared_expression_evaluates; unfold td_locals; rank15_temporary]); subst v end.
  match goal with Hcast : sem_cast _ _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hnil : eval_exprlist _ _ _ _ [] [] _ |- _ => inversion Hnil; subst end.
  reflexivity.
Qed.

Lemma td_tail_exposes_sqrt : forall version e le m a b t le' m' out,
  e ! TD._sqrtf = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e
    (td_locals le a b) m td_tail t le' m' out ->
  exists fb fd value,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd /\
    type_of_fundef fd = Tfunction [tfloat] tfloat cc_default /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (td_squared a b)] t m' value /\
    out = Out_return (Some (value, tfloat)).
Proof.
  intros version e le m a b t le' m' out Hlocal Hrun.
  unfold td_tail, ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ |- _ =>
    inversion Hcall; subst; clear Hcall end.
  all: try contradiction.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hargs : eval_exprlist _ _ _ _ [ts_squared_expression] [tfloat] _ |- _ =>
    apply td_argument_exact in Hargs; subst end.
  match goal with Hname : eval_expr _ _ _ _ (Evar TD._sqrtf _) _ |- _ =>
    inversion Hname; subst; clear Hname end.
  match goal with Hlv : eval_lvalue _ _ _ _ (Evar TD._sqrtf _) _ _ _ |- _ =>
    inversion Hlv; subst; clear Hlv; try congruence end.
  match goal with Hderef : deref_loc _ _ _ _ _ _ |- _ =>
    inversion Hderef; subst; clear Hderef; try discriminate end.
  match goal with Hvalue : eval_expr _ _ _ _ (Etempvar TD._t'1 tfloat) ?v |- _ =>
    assert (Hread : _ = _) by (eapply ocn_temp_value; [exact Hvalue|apply PTree.gss]);
    subst v end.
  match goal with Hsymbol : Genv.find_symbol _ TD._sqrtf = Some ?fb,
    Hcall : ClightBigstep.eval_funcall _ _ _ ?fd _ _ _ ?value |- _ =>
    exists fb, fd, value end.
  repeat split; try assumption; try reflexivity.
  unfold Eapp. rewrite app_nil_r. assumption.
Qed.

Lemma td_body_exposes_sqrt : forall version e le m ab ao a bb bo b t le' m' out,
  e ! TD._sqrtf = None ->
  le ! TD._obj1 = Some (Vptr ab ao) -> le ! TD._obj2 = Some (Vptr bb bo) ->
  td_position m ab ao a -> td_position m bb bo b ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (ts_distance_body version)) t le' m' out ->
  exists fb fd value,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd /\
    type_of_fundef fd = Tfunction [tfloat] tfloat cc_default /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (td_squared a b)] t m' value /\
    out = Out_return (Some (value, tfloat)).
Proof.
  intros version e le m ab ao a bb bo b t le' m' out Hlocal Ha Hb Hpa Hpb Hrun.
  destruct (td_source version) as (_ & Hbody & Hreadonly & Hnormal).
  rewrite Hbody in Hrun.
  destruct (ocn_successful_prefix_decomposition _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & rest & Htrace & Hprefix & Hrest).
  pose proof (td_reads_execute version e le m ab ao a bb bo b Ha Hb Hpa Hpb) as Hconstructed.
  destruct (ocr_readonly_unique _ _ _ _ _ _ _ _ _ Hprefix Hreadonly
    _ _ _ _ Hconstructed) as (Hpre & Hmiddle & Hmemory & _).
  subst pre middle memory. cbn in Htrace. subst t.
  eapply td_tail_exposes_sqrt; eauto.
Qed.

Lemma td_entry : forall version ge m ab ao bb bo e le entry,
  function_entry2 ge (ts_distance_body version) [Vptr ab ao; Vptr bb bo] m e le entry ->
  e = empty_env /\ entry = m /\
  le ! TD._obj1 = Some (Vptr ab ao) /\ le ! TD._obj2 = Some (Vptr bb bo).
Proof.
  intros version ge m ab ao bb bo e le entry Hentry.
  assert (Hvars : fn_vars (ts_distance_body version) = []) by (destruct version; reflexivity).
  inversion Hentry; subst; clear Hentry.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst; clear Halloc end.
  repeat split; try reflexivity.
  all: match goal with Hbind : bind_parameter_temps _ _ _ = Some _ |- _ =>
    destruct version; cbn in Hbind; inversion Hbind; reflexivity end.
Qed.

Lemma td_float_cast_identity : forall value m result,
  sem_cast value tfloat tfloat m = Some result -> result = value.
Proof. intros [] m result H; cbn in H; congruence. Qed.

(** This is a whole-call statement. The memory passed to sqrtf is exactly
    the caller's memory; the memory returned from the helper is exactly
    sqrtf's output. There are no hidden local stores, allocation effects,
    or additional callees left in this helper. *)
Definition TripletLiveDistanceCall : Prop :=
  forall version m ab ao a bb bo b t after result,
  td_position m ab ao a -> td_position m bb bo b ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] t after result ->
  exists fb fd,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd /\
    type_of_fundef fd = Tfunction [tfloat] tfloat cc_default /\
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m fd
      [Vsingle (td_squared a b)] t after result.

Theorem td_live_distance_call_reduces_to_sqrt : TripletLiveDistanceCall.
Proof.
  intros version m ab ao a bb bo b t after result Ha Hb Hcall.
  inversion Hcall; subst; clear Hcall.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (td_entry _ _ _ _ _ _ _ _ _ _ He) as (-> & -> & Hobj1 & Hobj2) end.
  match goal with Hfree : Mem.free_list ?memory (blocks_of_env _ empty_env) = Some after |- _ =>
    change (Some memory = Some after) in Hfree; inversion Hfree; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    destruct (td_body_exposes_sqrt _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (PTree.gempty _ _) Hobj1 Hobj2 Ha Hb Hbody)
      as (fb & fd & value & Hsymbol & Hfun & Htype & Hsqrt & Hout); subst end.
  replace (fn_return (ts_distance_body version)) with tfloat in H2
    by (destruct version; reflexivity).
  unfold outcome_result_value in H2.
  destruct H2 as [_ Hcast].
  apply td_float_cast_identity in Hcast. subst result.
  exists fb, fd. repeat split; assumption.
Qed.

(** The previously proved universal distance bound now applies to the live
    helper, conditional only on the already explicit named square-root
    numerical effect. This premise is NOT discharged by this theorem. *)
Definition TripletLiveElevatorDistanceRejection : Prop :=
  forall version m ab ao y bb bo b t after result,
  let a := {| vec_x := ts_float 3181; vec_y := y; vec_z := ts_float 3587 |} in
  td_position m ab ao a -> td_position m bb bo b ->
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub y (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub y (vec_y b)) <= 16384)%R ->
  ocr_sqrt_numeric_effect version m (td_squared a b) ->
  ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] t after result ->
  exists distance, result = Vsingle distance /\ Float32.cmp Clt distance ts_threshold = false.

Theorem td_live_elevator_distance_rejects : TripletLiveElevatorDistanceRejection.
Proof.
  intros version m ab ao y bb bo b t after result a Ha Hb Hbase Fdy Hdy Hnumeric Hcall.
  destruct (td_live_distance_call_reduces_to_sqrt version m ab ao a bb bo b t after result Ha Hb Hcall)
    as (fb & fd & Hsymbol & Hfun & Htype & Hsqrt).
  assert (result = Vsingle (Float32.sqrt (td_squared a b))) by
    (eapply Hnumeric; eauto). subst result. eexists. split; [reflexivity|].
  exact (ts_elevator_distance_rejects_native_guard _ _ _ Hbase Fdy Hdy).
Qed.
