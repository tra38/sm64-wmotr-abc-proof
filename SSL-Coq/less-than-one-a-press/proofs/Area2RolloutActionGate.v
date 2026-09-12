(** Finishing a rollout animation does not make ordinary freefall available.
    This is an execution theorem for the actual US/JP rollout endings and
    airborne dispatch, not a theorem that every elevator history stays there.
    The animation helper is resolved and proved read-only, including entry and
    return. Earlier movement, interactions and later scheduling remain outside
    this segment; no frame condition for those calls is assumed. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Coqlib
  Ctypes Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario jp_mario
  us_mario_actions_airborne jp_mario_actions_airborne.
From LessThanOneAPress.Proofs Require Import GameTypes ASTFacts
  Area2Rank10AGroundPound Area2Rank12BContact UpperElevatorQueryResolution
  InkBackwardSource InkBackwardExecution InkBodyResetFrame InkCopyCaller
  InkControllerSource InkControllerEdge ObjectContactNecessity
  Area2RolloutSource SecretContactExecution InkActionPassStart InkActionTimerReset
  ContactConsumerExecution EyerokRank15LiveMovement
  SelectedClightTarget CleanedClightPrograms ClightLinkExecution
  GlobalInterfaceStructural JPSourceSymbolTransport JPWarpLevelEntryResolution
  LinkedClightPrograms NormalizedClightPrograms SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.


Definition rag_finish version direction := rank12b_drop_sequences 4
  (fn_body (rag_body version (RGRollout direction))).
Definition rag_state := ics_field RGA._m RGA._MarioState RGA._actionState tushort.
Definition rag_action := ics_field RGA._m RGA._MarioState RGA._action tuint.
Definition rag_dispatch version := ibk_head (rank12b_drop_sequences 2
  (fn_body (rag_body version RGDispatch))).
Definition rag_cases version := match rag_dispatch version with
| Ssequence _ (Sswitch _ cases) => cases | _ => LSnil end.
Definition rag_action_code direction := match direction with
| RolloutForward => 16779430 | RolloutBackward => 16779437 end.

Lemma rag_source : forall version direction,
  fn_body (rag_body version (RGRollout direction)) =
    ocn_prepend (ocn_prefix_items 4 (fn_body (rag_body version (RGRollout direction))))
      (rag_finish version direction) /\
  rag_finish version direction = Ssequence (ibk_head (rag_finish version direction))
    (Sreturn (Some (Econst_int Int.zero tint))) /\
  ibk_normal (ibk_head (rag_finish version direction)) = true /\
  rag_dispatch version = Ssequence (Sset RGA._t'46 rag_action)
    (Sswitch (Etempvar RGA._t'46 tuint) (rag_cases version)).
Proof. intros [] []; repeat split; reflexivity. Qed.
Lemma rag_layout : forall version,
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) RGA._MarioState RGA._actionState 24 = true /\
  ibcc_field_ok (Clight.globalenv (selected_clight_target version)) RGA._MarioState RGA._action 12 = true.
Proof.
  intro version. change (ibcc_field_ok (prog_comp_env (selected_clight_target version))
    RGA._MarioState RGA._actionState 24 = true /\
    ibcc_field_ok (prog_comp_env (selected_clight_target version)) RGA._MarioState RGA._action 12 = true).
  rewrite <- rank15_selected_header_environment_exact.
  destruct version; vm_compute; split; reflexivity.
Qed.

Lemma rag_animation_source : forall version,
  fn_vars (rag_body version RGAnimationEnd) = [] /\
  cce_readonly_keep RGA._m (fn_body (rag_body version RGAnimationEnd)) = true.
Proof. intros []; split; reflexivity. Qed.
Theorem rag_animation_call_preserves_memory : forall version m args t after result,
  ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
    m (Internal (rag_body version RGAnimationEnd)) args t after result ->
  t = E0 /\ after = m.
Proof.
  intros version m args t after result Hcall.
  destruct (rag_animation_source version) as [Hvars Hpure].
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Halloc : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Halloc; inversion Halloc; subst end.
  match goal with Hbody : ClightBigstep.exec_stmt _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hbody Hpure) as (-> & -> & _) end.
  match goal with Hfree : Mem.free_list ?before (blocks_of_env _ empty_env) = Some ?last |- _ =>
    change (Some before = Some last) in Hfree; inversion Hfree; subst end.
  split; reflexivity.
Qed.
Lemma rag_named_call : forall version native le m opt args t last after out,
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (Scall opt (Evar (rag_ident native)
      (Tfunction [tptr (Tstruct RGA._MarioState noattr)] tint cc_default)) args)
    t last after out ->
  exists values result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (rag_body version native)) values t after result.
Proof.
  intros version native le m opt args t last after out Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (rag_selected_bodies_resolve version native) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Evar ?id (Tfunction ?tys ?ret ?cc)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by
      (exact (sce_function_name_value ge env temps memory id tys ret cc fb vf eq_refl Hsymbol Hr));
    subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  eauto.
Qed.

(** Only the two bytes of actionState may change. This statement class is
    checked against both actual endings; it is not an assumed coverage rule. *)
Definition rag_frame mb m after := forall chunk b ofs,
  b <> mb \/ ofs + size_chunk chunk <= 24 \/ 26 <= ofs ->
  Mem.load chunk after b ofs = Mem.load chunk m b ofs.
Inductive rag_statement : statement -> Prop :=
| rag_readonly : forall s, cce_readonly_keep RGA._m s = true -> rag_statement s
| rag_write : rag_statement (Sassign rag_state (Econst_int (Int.repr 2) tint))
| rag_call : forall id args, id <> RGA._m -> rag_statement
    (Scall (Some id) (Evar (rag_ident RGAnimationEnd)
      (Tfunction [tptr (Tstruct RGA._MarioState noattr)] tint cc_default)) args)
| rag_seq : forall first rest, rag_statement first -> rag_statement rest ->
    rag_statement (Ssequence first rest)
| rag_if : forall cond yes no, rag_statement yes -> rag_statement no ->
    rag_statement (Sifthenelse cond yes no).
Lemma rag_finish_classified : forall version direction,
  rag_statement (rag_finish version direction).
Proof.
  intros [] []; cbn [rag_finish rank12b_drop_sequences rag_body fn_body].
  all: repeat first [apply rag_readonly; reflexivity | apply rag_write
    |apply rag_call; discriminate |apply rag_seq |apply rag_if].
Qed.
Theorem rag_statement_effect : forall s, rag_statement s ->
  forall version le m mb t last after out,
  le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m s t last after out ->
  t = E0 /\ last ! RGA._m = le ! RGA._m /\ rag_frame mb m after.
Proof.
  intros s Hshape. induction Hshape; intros version le m mb t last after out Hm Hrun.
  - destruct (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun H) as (-> & -> & Htemp).
    split; [reflexivity|]. split; [exact Htemp|]. unfold rag_frame; intros; reflexivity.
  - destruct (ibr_field_assignment_store _ empty_env le m RGA._m RGA._MarioState
      RGA._actionState tushort 24 Mint16unsigned (Econst_int (Int.repr 2) tint)
      t last after out mb Ptrofs.zero Hm (proj1 (rag_layout version)) eq_refl Hrun)
      as (-> & -> & -> & value & Hstore).
    split; [reflexivity|]. split; [reflexivity|]. intros chunk b ofs Hprotected.
    eapply Mem.load_store_other; [exact Hstore|].
    change (b <> mb \/ ofs + size_chunk chunk <= 24 \/ 24 + size_chunk Mint16unsigned <= ofs).
    cbn [size_chunk]. exact Hprotected.
  - destruct (rag_named_call _ _ _ _ _ _ _ _ _ _ Hrun) as (values & result & Hcall).
    destruct (rag_animation_call_preserves_memory _ _ _ _ _ _ Hcall) as (-> & ->).
    inversion Hrun; subst. split; [reflexivity|]. split.
    + apply PTree.gso. congruence.
    + unfold rag_frame; intros; reflexivity.
  - inversion Hrun; subst.
    + match goal with Hfirst : ClightBigstep.exec_stmt _ _ _ _ _ first _ _ _ _,
        Hrest : ClightBigstep.exec_stmt _ _ _ _ _ rest _ _ _ _ |- _ =>
        destruct (IHHshape1 _ _ _ _ _ _ _ _ Hm Hfirst) as (-> & Htemp1 & Hframe1);
        destruct (IHHshape2 _ _ _ _ _ _ _ _ (eq_trans Htemp1 Hm) Hrest)
          as (-> & Htemp2 & Hframe2) end.
      split; [reflexivity|]. split; [congruence|].
      intros chunk b ofs Hprotected. rewrite Hframe2, Hframe1; auto.
    + eapply IHHshape1; eauto.
  - inversion Hrun; subst. destruct b; [eapply IHHshape1|eapply IHHshape2]; eauto.
Qed.

Definition RolloutFinishPreservation : Prop := forall version direction le m mb t last after out,
  le ! RGA._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) empty_env le m
    (rag_finish version direction) t last after out ->
  t = E0 /\ out = Out_return (Some (Vint Int.zero, tint)) /\
  last ! RGA._m = le ! RGA._m /\ rag_frame mb m after.
Theorem rag_rollout_finish_preserves_action_and_position : RolloutFinishPreservation.
Proof.
  unfold RolloutFinishPreservation.
  intros version direction le m mb t last after out Hm Hrun.
  destruct (rag_statement_effect _ (rag_finish_classified version direction)
    _ _ _ _ _ _ _ _ Hm Hrun) as (Ht & Htemp & Hframe).
  destruct (rag_source version direction) as (_ & Htail & Hnormal & _).
  rewrite Htail in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suffix & Htrace & Hcondition & Hreturn).
  inversion Hreturn; subst.
  match goal with Hr : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply ocn_const_int_value in Hr; subst end.
  repeat split; assumption || reflexivity.
Qed.
