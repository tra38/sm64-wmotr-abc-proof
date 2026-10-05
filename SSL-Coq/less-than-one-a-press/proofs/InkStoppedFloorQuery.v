(** The stopped-quarter query is at the corrected intended vector, not at
    the remembered Mario floor. Its actual find_floor call returns a local
    height and cannot replace MarioState.floorHeight or movement Y. The
    wall/ceiling/water calls surrounding this query remain separate. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkFloorHistorySource
  InkFloorHistoryQuery InkFloorHistoryExecution InkFloorCallEffects InkCopyEntry
  InkCopyCaller InkFloorResetExecution InkBackwardExecution InkBackwardSource
  Area2Rank12BContact ObjectContactNecessity
  SecretContactExecution ContactConsumerExecution UpperElevatorQueryResolution
  SelectedClightTarget InkPlatformWriteFrame.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition isfq_query version := ibk_head
  (rank12b_drop_sequences 2 (fn_body (ifh_quarter_body version))).
Definition isfq_call := Scall (Some IFH._t'3)
  (Evar IFH._find_floor (Tfunction
    [tfloat; tfloat; tfloat; tptr (tptr (Tstruct IFH._Surface noattr))]
    tfloat cc_default))
  [Etempvar IFH._t'24 tfloat; Etempvar IFH._t'25 tfloat;
   Etempvar IFH._t'26 tfloat;
   Eaddrof (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr)))
     (tptr (tptr (Tstruct IFH._Surface noattr)))].

Lemma isfq_source : forall version,
  isfq_query version = Ssequence
    (Ssequence (Sset IFH._t'24 (ifh_next 0))
      (Ssequence (Sset IFH._t'25 (ifh_next 1))
        (Ssequence (Sset IFH._t'26 (ifh_next 2)) isfq_call)))
    (Sset IFH._floorHeight (Etempvar IFH._t'3 tfloat)).
Proof. intros []; reflexivity. Qed.

Lemma isfq_next_read : forall ge e le m nb no n f answer,
  le ! IFH._nextPos = Some (Vptr nb no) ->
  Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no
    (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))))) =
      Some (Vsingle f) ->
  eval_expr ge e le m (ifh_next n) answer -> answer = Vsingle f.
Proof.
  intros ge e le m nb no n f answer Hnext Hload Hread.
  pose proof (ibc_float_read _ _ _ _ IFH._nextPos n _ _ _ Hnext Hread).
  congruence.
Qed.

Lemma isfq_output_address : forall ge e le m fb answer,
  e ! IFH._floor = Some (fb, tptr (Tstruct IFH._Surface noattr)) ->
  eval_expr ge e le m
    (Eaddrof (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr)))
      (tptr (tptr (Tstruct IFH._Surface noattr)))) answer ->
  answer = Vptr fb Ptrofs.zero.
Proof.
  intros ge e le m fb answer Hfloor Hread. inversion Hread; subst.
  - match goal with Hl : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
      destruct (ibc_local_location _ _ _ _ _ _ _ _ _ _ Hfloor Hl)
        as (Hb & Ho & Hbf); subst end. reflexivity.
  - match goal with Hl : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion Hl end.
Qed.

Definition InkStoppedQuarterRealQuery : Prop :=
  forall version e le m nb no fb values t le' m' out,
  e ! IFH._find_floor = None ->
  e ! IFH._floor = Some (fb, tptr (Tstruct IFH._Surface noattr)) ->
  le ! IFH._nextPos = Some (Vptr nb no) ->
  (forall n, 0 <= n <= 2 ->
    Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no
      (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))))) =
      Some (Vsingle (values n))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (isfq_query version) t le' m' out ->
  exists floor,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values 0); Vsingle (values 1); Vsingle (values 2);
       Vptr fb Ptrofs.zero] t m' floor /\
    le' ! IFH._floorHeight = Some floor /\ out = Out_normal.

Theorem isfq_corrected_vector_reaches_real_floor_call : InkStoppedQuarterRealQuery.
Proof.
  unfold InkStoppedQuarterRealQuery.
  intros version e le m nb no fb values t le' m' out
    Hlocal Hfloor Hnext Hvalues Hrun.
  rewrite isfq_source in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: try solve [match goal with
    Hc : ClightBigstep.exec_stmt _ _ _ _ _ isfq_call _ _ _ ?o,
    Hbad : ?o <> Out_normal |- _ => inversion Hc; subst; contradiction end].
  all: repeat match goal with
  | Hr : eval_expr ?ge ?env ?temps ?memory (ifh_next ?n) ?v |- _ =>
    assert (v = Vsingle (values n)) by
      (eapply (isfq_next_read ge env temps memory nb no n (values n) v);
       [repeat rewrite PTree.gso by discriminate; exact Hnext
       |apply Hvalues; lia|exact Hr]); subst v; clear Hr
  end.
  match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ isfq_call _ _ _ _ |- _ =>
    inversion Hc; subst; clear Hc end.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  destruct (upper_elevator_selected_query_body_resolves version UEQRFindFloor)
    as (queryb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr queryb Ptrofs.zero) by
      (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version))
      queryb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Hr; subst; clear Hr end.
  repeat match goal with
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._t'24 _) ?v |- _ =>
    assert (v = Vsingle (values 0)) by (eapply ocn_temp_value;
      [exact Hr|repeat rewrite PTree.gso by discriminate; apply PTree.gss]);
    subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._t'25 _) ?v |- _ =>
    assert (v = Vsingle (values 1)) by (eapply ocn_temp_value;
      [exact Hr|repeat rewrite PTree.gso by discriminate; apply PTree.gss]);
    subst v; clear Hr
  | Hr : eval_expr _ _ _ _ (Etempvar IFH._t'26 _) ?v |- _ =>
    assert (v = Vsingle (values 2)) by (eapply ocn_temp_value;
      [exact Hr|apply PTree.gss]); subst v; clear Hr
  end.
  match goal with Hr : eval_expr _ _ _ _ (Eaddrof _ _) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by
      (eapply isfq_output_address; eauto); subst v end.
  repeat match goal with Hcast : sem_cast ?value ?ty tfloat ?memory = Some ?answer |- _ =>
    change (sem_cast value tfloat tfloat memory = Some answer) in Hcast;
    destruct (ifh_float_cast_identity _ _ _ Hcast) as (? & ? & ?);
    subst; clear Hcast end.
  repeat match goal with Heq : Vsingle _ = Vsingle _ |- _ =>
    inversion Heq; subst; clear Heq end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IFH._t'3 _) ?v |- _ =>
    lazymatch goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ ?r |- _ =>
      assert (v = r) by (eapply ocn_temp_value;
        [exact Hr|cbn [set_opttemp]; apply PTree.gss]); subst v end end.
  unfold Eapp, E0. rewrite ?app_nil_r.
  match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ ?r |- _ =>
    exists r end.
  split; [eassumption|]. split; [apply PTree.gss|reflexivity].
Qed.

(** In particular, this lookup cannot install its lower answer into the
    remembered height that the later alignment reads. The stack output's
    separation follows from fresh allocation at the real quarter entry,
    as checked below; it is unrelated to live floor-list integrity. *)
Definition InkStoppedQueryCacheFrame : Prop :=
  forall version e le m nb no fb values mb t le' m' out,
  e ! IFH._find_floor = None ->
  e ! IFH._floor = Some (fb, tptr (Tstruct IFH._Surface noattr)) ->
  le ! IFH._nextPos = Some (Vptr nb no) ->
  (forall n, 0 <= n <= 2 ->
    Mem.load Mfloat32 m nb (Ptrofs.unsigned (Ptrofs.add no
      (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int Signed (Int.repr n))))) =
      Some (Vsingle (values n))) ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Mem.valid_block m mb -> fb <> mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (isfq_query version) t le' m' out ->
  t = E0 /\
  Mem.load Mfloat32 m' mb 64 = Mem.load Mfloat32 m mb 64 /\
  Mem.load Mfloat32 m' mb 112 = Mem.load Mfloat32 m mb 112.

Theorem isfq_query_preserves_remembered_height : InkStoppedQueryCacheFrame.
Proof.
  intros version e le m nb no fb values mb t le' m' out
    Hlocal Hfloor Hnext Hvalues Hsymbol Hvalid Hdifferent Hrun.
  destruct (isfq_corrected_vector_reaches_real_floor_call version e le m nb no fb values
    t le' m' out Hlocal Hfloor Hnext Hvalues Hrun) as (floor & Hcall & _).
  assert (forall ofs,
    t = E0 /\ Mem.load Mfloat32 m' mb ofs = Mem.load Mfloat32 m mb ofs) as Hframe.
  { intro ofs. eapply ifc_completed_floor_preserves_other_cells; eauto.
    - intros id Hin Hsame.
      assert (us_object_list_processor._gMarioStates <> id) as Hids by
        (destruct Hin as [<-|[<-|[<-|[]]]]; discriminate).
      assert (mb <> mb) as Hcontra by
        (eapply Genv.global_addresses_distinct; eauto). exact (Hcontra eq_refl).
    - left. congruence. }
  split; [exact (proj1 (Hframe 64))|]. split; apply Hframe.
Qed.

Definition InkStoppedFloorQueryBoundary : Prop :=
  InkStoppedQuarterRealQuery /\ InkStoppedQueryCacheFrame.
Theorem isfq_stopped_floor_query_checked : InkStoppedFloorQueryBoundary.
Proof. split; [exact isfq_corrected_vector_reaches_real_floor_call|
  exact isfq_query_preserves_remembered_height]. Qed.

(** No arbitrary safe-output premise is needed at a normal reached entry:
    every actual local belongs to fresh storage outside the existing State. *)
Theorem isfq_actual_quarter_entry_separates_floor_output :
  forall version ge m mb mo nb no e le entry fb,
  Mem.valid_block m mb ->
  function_entry2 ge (ifh_quarter_body version)
    [Vptr mb mo; Vptr nb no] m e le entry ->
  e ! IFH._floor = Some (fb, tptr (Tstruct IFH._Surface noattr)) ->
  fb <> mb.
Proof.
  intros version ge m mb mo nb no e le entry fb Hvalid Hentry Hfloor.
  inversion Hentry; subst.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha mb Hvalid
      ltac:(intros id b ty Hread; rewrite PTree.gempty in Hread; discriminate))
      as (Hlocals & _)
  end.
  eapply Hlocals; exact Hfloor.
Qed.
