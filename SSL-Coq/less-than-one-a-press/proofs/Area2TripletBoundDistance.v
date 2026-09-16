(** The real US/JP distance helper executes with an explicitly linked sqrtf
    implementation. No opaque numerical-effect or same-call-realization
    premise is used. This local runtime uses the unchanged generated body;
    it is not silently substituted for CompCert's old external-call oracle. *)
From Coq Require Import Bool List ZArith Reals.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib
  Ctypes Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import SqrtfClightBinding
  SqrtfTargetResolution SqrtfMachine Area2TripletDistance Area2TripletSpawner
  Area2TripletSqrt Area2Rank9ACoinFlight GameTypes SelectedClightTarget
  InkTimer131RetailMipsCode
  ReadOnlyClightPaths ObjectContactReadback ObjectContactNecessity.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma tbd_prepend_steps : forall items controls ge e memory le final,
  readonly_path ge e memory le (ocn_prepend items Sskip) final -> forall f k tail,
  SqrtfLinkedSteps controls ge
    (State f (ocn_prepend items tail) k e le memory)
    (State f tail k e final memory).
Proof.
  induction items as [|first rest IH]; intros controls ge e memory le final Hpath f k tail.
  - inversion Hpath; subst. constructor.
  - inversion Hpath; subst. cbn [ocn_prepend].
    eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_seq]|].
    eapply sb_steps_trans; [eapply sb_readonly_steps; eassumption|].
    eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_skip_seq]|].
    eapply IH; eassumption.
Qed.

Theorem tbd_whole_body_executes : forall version controls le memory ab ao a bb bo b k,
  sb_controls_ok controls -> sqrtf_operand_domain (td_squared a b) ->
  le ! TD._obj1 = Some (Vptr ab ao) -> le ! TD._obj2 = Some (Vptr bb bo) ->
  td_position memory ab ao a -> td_position memory bb bo b ->
  SqrtfLinkedSteps controls (Clight.globalenv (selected_clight_target version))
    (State (ts_distance_body version) (fn_body (ts_distance_body version)) k empty_env le memory)
    (Returnstate (Vsingle (Float32.sqrt (td_squared a b))) (call_cont k) memory).
Proof.
  intros version controls le memory ab ao a bb bo b k Hcontrols Hdomain Ha Hb Hpa Hpb.
  destruct (td_source version) as (_ & Hbody & Hreadonly & _).
  pose proof (td_reads_execute version empty_env le memory ab ao a bb bo b Ha Hb Hpa Hpb) as Hreads.
  destruct (sb_readonly_bigstep_path _ _ _ _ _ _ _ _ _ Hreadonly Hreads)
    as (_ & _ & _ & Hpath).
  rewrite Hbody. eapply sb_steps_trans.
  - eapply tbd_prepend_steps. exact Hpath.
  - destruct (sbr_selected_sqrtf_resolves version) as [fb [Hsymbol Hfunction]].
    eapply sb_distance_tail_completes; eauto.
Qed.

Definition tbd_entry_locals version ab ao bb bo :=
  PTree.set TD._obj2 (Vptr bb bo)
    (PTree.set TD._obj1 (Vptr ab ao)
      (create_undef_temps (fn_temps (ts_distance_body version)))).

Lemma tbd_function_entry : forall version ge memory ab ao bb bo,
  function_entry2 ge (ts_distance_body version) [Vptr ab ao; Vptr bb bo] memory
    empty_env (tbd_entry_locals version ab ao bb bo) memory.
Proof.
  intros version ge memory ab ao bb bo. constructor.
  - destruct version; repeat constructor.
  - destruct version; repeat constructor; cbn; intuition discriminate.
  - destruct version; vm_compute; intuition congruence.
  - destruct version; constructor.
  - destruct version; reflexivity.
Qed.

(** Constructive whole-call execution, from the two Object pointers through
    their six actual reads, the real expression, the linked instruction
    routine and the C return. There is no assumed external execution to
    match after the fact. *)
Theorem tbd_distance_call_executes : forall version controls memory ab ao a bb bo b k,
  sb_controls_ok controls -> sqrtf_operand_domain (td_squared a b) ->
  td_position memory ab ao a -> td_position memory bb bo b ->
  is_call_cont k ->
  SqrtfLinkedSteps controls (Clight.globalenv (selected_clight_target version))
    (Callstate (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] k memory)
    (Returnstate (Vsingle (Float32.sqrt (td_squared a b))) k memory).
Proof.
  intros version controls memory ab ao a bb bo b k Hcontrols Hdomain Ha Hb Hk.
  eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_internal_function;
    apply tbd_function_entry]|].
  rewrite <- (is_call_cont_call_cont _ Hk) at 2.
  eapply tbd_whole_body_executes; eauto.
  - unfold tbd_entry_locals. rewrite PTree.gso by discriminate. apply PTree.gss.
  - unfold tbd_entry_locals. apply PTree.gss.
Qed.

Definition TripletBoundDistanceExecution : Prop :=
  forall version memory ab ao y bb bo b,
  let a := {| vec_x := ts_float 3181; vec_y := y; vec_z := ts_float 3587 |} in
  td_position memory ab ao a -> td_position memory bb bo b ->
  ts_in_base (vec_x b) (vec_z b) ->
  rank9cf_finite (Float32.sub y (vec_y b)) ->
  (-16384 <= rank9cf_real (Float32.sub y (vec_y b)) <= 16384)%R ->
  exists distance,
    SqrtfLinkedSteps sb_normal_controls (Clight.globalenv (selected_clight_target version))
      (Callstate (Internal (ts_distance_body version)) [Vptr ab ao; Vptr bb bo] Kstop memory)
      (Returnstate (Vsingle distance) Kstop memory) /\
    Float32.cmp Clt distance ts_threshold = false.

Theorem tbd_bound_distance_call_rejects : TripletBoundDistanceExecution.
Proof.
  intros version memory ab ao y bb bo b a Ha Hb Hbase Fy Hy.
  exists (Float32.sqrt (td_squared a b)). split.
  - apply tbd_distance_call_executes; try assumption.
    + exact sb_normal_controls_checked.
    + exact (proj1 (tsp_actual_argument_is_normal _ _ Hbase Fy Hy)).
    + exact I.
  - exact (ts_elevator_distance_rejects_native_guard _ _ _ Hbase Fy Hy).
Qed.

Definition TripletBoundSqrtBoundary : Prop :=
  TripletBoundDistanceExecution /\
  (forall version, exists fb,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some sb_declaration) /\
  (forall controls ge argument memory k trace s',
    sb_controls_ok controls ->
    SqrtfLinkedStep controls ge (Callstate sb_declaration [Vsingle argument] k memory) trace s' ->
    trace = E0 /\ s' = Returnstate (Vsingle (Float32.sqrt argument)) k memory) /\
  (forall before after,
    SqrtfWordExecution jp_sqrtf_words before after ->
    sqrtf_rounding after = sqrtf_rounding before /\
    sqrtf_cop1_usable after = sqrtf_cop1_usable before /\
    sqrtf_inexact_enabled after = sqrtf_inexact_enabled before).

Theorem tbd_bound_sqrt_boundary_checked : TripletBoundSqrtBoundary.
Proof.
  split; [exact tbd_bound_distance_call_rejects|].
  split; [exact sbr_selected_sqrtf_resolves|].
  split; [exact sb_external_step_has_unique_result|exact sb_instruction_controls_preserved].
Qed.
