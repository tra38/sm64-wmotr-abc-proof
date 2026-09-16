(** An explicit foreign-function binding for the actual generated sqrtf
    declaration. This is a local linked runtime: ordinary Clight2 steps are
    retained verbatim, while an external Callstate executes the authenticated
    instruction routine. It does NOT redefine Events.external_functions_sem
    or claim that an arbitrary run of the old oracle has this behavior.
    Unsupported externals and Sbuiltin are outside this local segment. *)
From Coq Require Import Bool List String ZArith Lia.
From Flocq Require Import BinarySingleNaN.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_helpers jp_object_helpers.
From LessThanOneAPress.Proofs Require Import SqrtfMachine
  InkTimer131RetailMipsCode ReadOnlyClightPaths ObjectContactReadback
  ObjectContactNecessity Area2TripletDistance Area2TripletSpawner
  EyerokRank15LiveMovement GameTypes SelectedClightTarget SecretContactExecution.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition sb_declaration : Clight.fundef :=
  External (EF_external "sqrtf" (mksignature [AST.Xsingle] AST.Xsingle cc_default))
    [tfloat] tfloat cc_default.

Definition sb_find_declaration (definitions : list (ident * globdef Clight.fundef type)) :=
  find (fun entry => Pos.eqb (fst entry) TD._sqrtf) definitions.
Theorem sb_generated_declarations_checked :
  sb_find_declaration us_object_helpers.global_definitions =
    Some (TD._sqrtf, Gfun sb_declaration) /\
  sb_find_declaration jp_object_helpers.global_definitions =
    Some (TD._sqrtf, Gfun sb_declaration).
Proof. vm_compute; split; reflexivity. Qed.

(** Decode the actual Status/Cause-control bits, rather than silently
    choosing a different floating-point mode at the call. The normal
    profile is the relevant projection of osInitialize/osCreateThread;
    arbitrary preceding gameplay/OS control preservation is NOT assumed. *)
Record SqrtfControls := { sb_status : Z; sb_fcsr : Z }.
Definition sb_rounding c := match Z.land (sb_fcsr c) 3 with
  | 0 => mode_NE | 1 => mode_ZR | 2 => mode_UP | _ => mode_DN end.
Definition sb_controls_ok c :=
  sb_rounding c = mode_NE /\ Z.testbit (sb_status c) 29 = true /\
  Z.testbit (sb_fcsr c) 7 = false.
Definition sb_normal_controls :=
  {| sb_status := 536870912; sb_fcsr := 16779264 |}.
Theorem sb_normal_controls_checked : sb_controls_ok sb_normal_controls.
Proof. vm_compute; repeat split; reflexivity. Qed.

Definition sb_entry c argument memory return_address : SqrtfMachineState :=
  {| sqrtf_pc := jp_mips_range_start jp_sqrtf_range;
     sqrtf_next_pc := jp_mips_range_start jp_sqrtf_range + 4;
     sqrtf_gpr := fun r => if r =? 31 then return_address else 0;
     sqrtf_fpr := fun r => if r =? 12 then argument else Float32.zero;
     sqrtf_memory := memory; sqrtf_rounding := sb_rounding c;
     sqrtf_cop1_usable := Z.testbit (sb_status c) 29;
     sqrtf_inexact_enabled := Z.testbit (sb_fcsr c) 7 |}.

(** The adapter marshals the C value into f12 and reads f0 on return.
    Its rule contains instruction execution, not an assumed sqrt result or
    memory frame. The caller's return address is arbitrary and preserved. *)
Inductive SqrtfBoundCall (controls : SqrtfControls) :
    Clight.fundef -> list val -> mem -> trace -> val -> mem -> Prop :=
| sb_call : forall argument memory return_address finish,
    SqrtfWordExecution jp_sqrtf_words
      (sb_entry controls argument memory return_address) finish ->
    sqrtf_pc finish = return_address ->
    SqrtfBoundCall controls sb_declaration [Vsingle argument] memory E0
      (Vsingle (sqrtf_fpr finish 0)) (sqrtf_memory finish).

Theorem sb_binding_value_and_frame : forall controls argument memory trace result after,
  sb_controls_ok controls ->
  SqrtfBoundCall controls sb_declaration [Vsingle argument] memory trace result after ->
  result = Vsingle (Float32.sqrt argument) /\ after = memory /\ trace = E0.
Proof.
  intros controls argument memory trace result after [Hmode _] Hcall.
  inversion Hcall; subst.
  match goal with Hrun : SqrtfWordExecution _ ?entry ?finish |- _ =>
    destruct (sqrtf_actual_routine_result entry finish Hmode Hrun) as (_ & Hr & Hm & _) end.
  cbn [sb_entry sqrtf_fpr sqrtf_memory] in Hr, Hm.
  rewrite Hr, Hm. repeat split; reflexivity.
Qed.

Theorem sb_binding_exists : forall controls argument memory,
  sb_controls_ok controls -> sqrtf_operand_domain argument ->
  SqrtfBoundCall controls sb_declaration [Vsingle argument] memory E0
    (Vsingle (Float32.sqrt argument)) memory.
Proof.
  intros controls argument memory Hcontrols Hdomain.
  destruct Hcontrols as [Hmode [Hcop Htrap]].
  destruct (sqrtf_actual_routine_exists (sb_entry controls argument memory 0)
    Hcop Htrap Hdomain) as [finish Hrun].
  destruct (sqrtf_actual_routine_result (sb_entry controls argument memory 0)
    finish Hmode Hrun) as (Hpc & Hr & Hm & _).
  change (sqrtf_pc finish = 0) in Hpc.
  change (sqrtf_fpr finish 0 = Float32.sqrt argument) in Hr.
  change (sqrtf_memory finish = memory) in Hm.
  pose proof (sb_call controls argument memory 0 finish Hrun Hpc) as Hcall.
  now rewrite Hr, Hm in Hcall.
Qed.

Theorem sb_instruction_controls_preserved : forall before after,
  SqrtfWordExecution jp_sqrtf_words before after ->
  sqrtf_rounding after = sqrtf_rounding before /\
  sqrtf_cop1_usable after = sqrtf_cop1_usable before /\
  sqrtf_inexact_enabled after = sqrtf_inexact_enabled before.
Proof.
  intros before after Hrun.
  assert (forall words s s', SqrtfWordExecution words s s' ->
    sqrtf_rounding s' = sqrtf_rounding s /\
    sqrtf_cop1_usable s' = sqrtf_cop1_usable s /\
    sqrtf_inexact_enabled s' = sqrtf_inexact_enabled s) as Hgeneral.
  { intros words s s' H. induction H; [repeat split; reflexivity|].
    inversion H; subst; cbn [sqrtf_jump sqrtf_write] in *; exact IHSqrtfWordExecution. }
  eapply Hgeneral; exact Hrun.
Qed.

Definition sb_ordinary_source (s : Clight.state) : bool := match s with
  | Callstate (External _ _ _ _) _ _ _ => false
  | State _ (Sbuiltin _ _ _ _) _ _ _ _ => false
  | _ => true end.
Inductive SqrtfLinkedStep (controls : SqrtfControls) (ge : genv) :
    Clight.state -> trace -> Clight.state -> Prop :=
| sb_ordinary : forall s trace s', sb_ordinary_source s = true ->
    Clight.step2 ge s trace s' -> SqrtfLinkedStep controls ge s trace s'
| sb_external : forall fd args k memory trace result after,
    SqrtfBoundCall controls fd args memory trace result after ->
    SqrtfLinkedStep controls ge (Callstate fd args k memory) trace
      (Returnstate result k after).

Inductive SqrtfLinkedSteps (controls : SqrtfControls) (ge : genv) :
    Clight.state -> Clight.state -> Prop :=
| sb_done : forall s, SqrtfLinkedSteps controls ge s s
| sb_next : forall s middle final,
    SqrtfLinkedStep controls ge s E0 middle ->
    SqrtfLinkedSteps controls ge middle final ->
    SqrtfLinkedSteps controls ge s final.

Lemma sb_steps_trans : forall controls ge a b c,
  SqrtfLinkedSteps controls ge a b -> SqrtfLinkedSteps controls ge b c ->
  SqrtfLinkedSteps controls ge a c.
Proof. intros controls ge a b c H; induction H; intros; eauto using sb_next. Qed.

(** Every ordinary transition in the local runtime is literally a Clight2
    transition; the only added transition is the explicit foreign call. *)
Theorem sb_ordinary_step_is_clight : forall controls ge s trace s',
  sb_ordinary_source s = true -> SqrtfLinkedStep controls ge s trace s' ->
  Clight.step2 ge s trace s'.
Proof.
  intros controls ge s trace s' Hordinary Hstep. inversion Hstep; subst; auto.
  inversion H; subst. discriminate.
Qed.

Theorem sb_external_step_has_unique_result : forall controls ge argument memory k trace s',
  sb_controls_ok controls ->
  SqrtfLinkedStep controls ge (Callstate sb_declaration [Vsingle argument] k memory) trace s' ->
  trace = E0 /\ s' = Returnstate (Vsingle (Float32.sqrt argument)) k memory.
Proof.
  intros controls ge argument memory k trace s' Hcontrols Hstep.
  inversion Hstep; subst; [discriminate|].
  match goal with Hcall : SqrtfBoundCall _ _ _ _ _ _ _ |- _ =>
    destruct (sb_binding_value_and_frame _ _ _ _ _ _ Hcontrols Hcall)
      as (-> & -> & ->) end. auto.
Qed.

Lemma sb_readonly_steps : forall controls ge e m le s final,
  readonly_path ge e m le s final -> forall f k,
  SqrtfLinkedSteps controls ge (State f s k e le m) (State f Sskip k e final m).
Proof.
  intros controls ge e m le s final Hpath. induction Hpath; intros f k.
  - constructor.
  - eapply sb_next; [apply sb_ordinary; [reflexivity|constructor; eauto]|constructor].
  - eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_seq]|].
    eapply sb_steps_trans; [apply IHHpath1|].
    eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_skip_seq]|apply IHHpath2].
  - eapply sb_next; [apply sb_ordinary; [reflexivity|eapply step_ifthenelse; eauto]|].
    apply IHHpath.
Qed.

Lemma sb_readonly_bigstep_path : forall s ge e le m t le' after out,
  ocr_readonly_prefix s = true ->
  ClightBigstep.Clight2.exec_stmt ge e le m s t le' after out ->
  t = E0 /\ after = m /\ out = Out_normal /\ readonly_path ge e m le s le'.
Proof.
  induction s; intros ge env le m t le' after out Hshape Hrun;
    cbn in Hshape; try discriminate; inversion Hrun; subst.
  - repeat split; constructor.
  - repeat split; constructor; assumption.
  - apply andb_true_iff in Hshape as [Ha Hb].
    match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _ |- _ =>
      destruct (IHs1 _ _ _ _ _ _ _ _ Ha Hfirst) as (-> & -> & _ & Hpa) end.
    match goal with Hlast : ClightBigstep.exec_stmt _ _ _ _ _ s2 _ _ _ _ |- _ =>
      destruct (IHs2 _ _ _ _ _ _ _ _ Hb Hlast) as (-> & -> & -> & Hpb) end.
    repeat split; eauto using ro_seq.
  - apply andb_true_iff in Hshape as [Ha Hb].
    match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ s1 _ _ _ _ |- _ =>
      destruct (IHs1 _ _ _ _ _ _ _ _ Ha Hfirst) as (_ & _ & Heq & _) end.
    contradiction.
Qed.

(** The actual generated return suffix executes across the binding. Its
    argument comes from the generated expression, its result from f0, and
    its memory is the same memory at each adjacent endpoint. *)
Theorem sb_distance_tail_completes : forall version controls le memory a b fb k,
  sb_controls_ok controls -> sqrtf_operand_domain (td_squared a b) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb ->
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some sb_declaration ->
  SqrtfLinkedSteps controls (Clight.globalenv (selected_clight_target version))
    (State (ts_distance_body version) td_tail k empty_env (td_locals le a b) memory)
    (Returnstate (Vsingle (Float32.sqrt (td_squared a b))) (call_cont k) memory).
Proof.
  intros version controls le memory a b fb k Hcontrols Hdomain Hsymbol Hfunction.
  unfold td_tail.
  eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_seq]|].
  eapply sb_next; [apply sb_ordinary; [reflexivity|eapply step_call]|].
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [apply PTree.gempty|exact Hsymbol].
    + apply deref_loc_reference. reflexivity.
  - econstructor.
    + unfold td_squared. apply ts_squared_expression_evaluates; unfold td_locals; rank15_temporary.
    + reflexivity.
    + constructor.
  - exact Hfunction.
  - reflexivity.
  - eapply sb_next; [apply sb_external; apply sb_binding_exists; assumption|].
    eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_returnstate]|].
    eapply sb_next; [apply sb_ordinary; [reflexivity|apply step_skip_seq]|].
    eapply sb_next; [apply sb_ordinary; [reflexivity|eapply step_return_1]|].
    + apply eval_Etempvar. apply PTree.gss.
    + destruct version; reflexivity.
    + reflexivity.
    + constructor.
Qed.
