(** The complete retry copy and its second floor call share one memory and
    one trace. The floor callee's result/effects are NOT postulated here.
    Its actual live traversal is the remaining boundary to the finite mesh
    certificate, along with clean reachability of the raised display. *)
From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyEntry InkCopyCaller InkCopyCompletion InkRetryCompletion
  InkFloorHistorySource InkFloorHistoryQuery InkFloorResetSource InkFloorResetExecution
  OrdinaryArea1EntryMemory ObjectContactNecessity ContactConsumerExecution
  SecretContactExecution UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition irq_call_prefix version := ibk_head (ibk_second_query version).
Definition irq_find_floor := Scall (Some IBM._t'2)
  (Evar IBM._find_floor (Tfunction
    [tfloat; tfloat; tfloat; tptr (tptr (Tstruct IBM._Surface noattr))] tfloat cc_default))
  [Etempvar IBM._t'42 tfloat; Etempvar IBM._t'43 tfloat; Etempvar IBM._t'44 tfloat;
   Eaddrof ibk_floor_read (tptr (tptr (Tstruct IBM._Surface noattr)))].

Lemma irq_source_shape : forall version,
  ibk_second_query version = Ssequence (irq_call_prefix version)
    (Sassign ifr_floor_read (Etempvar IBM._t'2 tfloat)) /\
  irq_call_prefix version = Ssequence (Sset IBM._t'42 (ifh_state_coord 0))
    (Ssequence (Sset IBM._t'43 (ifh_state_coord 1))
      (Ssequence (Sset IBM._t'44 (ifh_state_coord 2)) irq_find_floor)) /\
  ibk_normal (irq_call_prefix version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma irq_coordinate_read : forall version e le m mb axis value answer,
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mfloat32 m mb (60 + 4 * icp_number axis) = Some (Vsingle value) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_state_coord (icp_number axis)) answer -> answer = Vsingle value.
Proof.
  intros version e le m mb axis value answer Hm Hload Hread.
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m ibcc_destination v -> v = Vptr mb (Ptrofs.repr 60)) as Hbase by
    (intros v Hr; exact (ifr_state_position_value version e le m mb Ptrofs.zero v Hm Hr)).
  inversion Hread; subst.
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ =>
    destruct (ifr_array_index_location _ _ _ _ ibcc_destination _ _ _ _ _ _
      eq_refl Hbase Hl) as (-> & -> & ->) end.
  match goal with Hd : deref_loc _ _ _ _ _ _ |- _ => inversion Hd; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hr : Mem.loadv _ _ _ = Some answer |- _ =>
    change (Mem.load Mfloat32 m mb (icp_offset (Ptrofs.repr 60) axis) = Some answer) in Hr;
    rewrite irc_plain_offset in Hr by (change (0 <= 60) || change (68 <= 4294967295); lia);
    congruence end.
Qed.

Definition InkRetryFloorCall : Prop :=
  forall version e le m mb values t le' m' out,
  e ! IBM._find_floor = None ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  (forall axis, Mem.load Mfloat32 m mb (60 + 4 * icp_number axis) =
    Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_second_query version) t le' m' out ->
  exists floor query_m,
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values ICPX); Vsingle (values ICPY); Vsingle (values ICPZ);
       Vptr mb (Ptrofs.repr 104)] t query_m (Vsingle floor) /\
    Mem.store Mfloat32 query_m mb 112 (Vsingle floor) = Some m' /\
    Mem.load Mfloat32 m' mb 64 = Mem.load Mfloat32 query_m mb 64 /\ out = Out_normal.

Theorem irq_second_floor_call_uses_completed_position : InkRetryFloorCall.
Proof.
  unfold InkRetryFloorCall.
  intros version e le m mb values t le' m' out Hlocal Hm Hvalues Hrun.
  destruct (irq_source_shape version) as (Hshape & Hprefix & Hnormal).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (store_le & query_m & query_trace & store_trace & Htrace & Hcall & Hwrite).
  rewrite Hprefix in Hcall.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hcall.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  all: lazymatch goal with Hr : eval_expr ?ge ?env ?temps ?memory (ifh_state_coord 0) ?v |- _ =>
    assert (v = Vsingle (values ICPX)) by
      (eapply (irq_coordinate_read version env temps memory mb ICPX);
        [exact Hm|exact (Hvalues ICPX)|exact Hr]); subst v end.
  all: lazymatch goal with Hr : eval_expr ?ge ?env ?temps ?memory (ifh_state_coord 1) ?v |- _ =>
    assert (v = Vsingle (values ICPY)) by
      (eapply (irq_coordinate_read version env temps memory mb ICPY);
        [rewrite PTree.gso by discriminate; exact Hm|exact (Hvalues ICPY)|exact Hr]); subst v end.
  all: lazymatch goal with Hr : eval_expr ?ge ?env ?temps ?memory (ifh_state_coord 2) ?v |- _ =>
    assert (v = Vsingle (values ICPZ)) by
      (eapply (irq_coordinate_read version env temps memory mb ICPZ);
        [repeat rewrite PTree.gso by discriminate; exact Hm|exact (Hvalues ICPZ)|exact Hr]); subst v end.
  match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ irq_find_floor _ _ _ _ |- _ =>
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
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._t'42 _) ?v |- _ =>
    assert (v = Vsingle (values ICPX)) by (eapply ocn_temp_value;
      [exact Hr|repeat rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._t'43 _) ?v |- _ =>
    assert (v = Vsingle (values ICPY)) by (eapply ocn_temp_value;
      [exact Hr|rewrite PTree.gso by discriminate; apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IBM._t'44 _) ?v |- _ =>
    assert (v = Vsingle (values ICPZ)) by (eapply ocn_temp_value;
      [exact Hr|apply PTree.gss]); subst v end.
  match goal with Hr : eval_expr ?ge ?env ?temps ?memory (Eaddrof ibk_floor_read _) ?v |- _ =>
    assert (v = Vptr mb (Ptrofs.repr 104)) by
      (eapply (ifh_floor_output_address version env temps memory mb v);
      [repeat rewrite PTree.gso by discriminate; exact Hm|exact Hr]); subst v end.
  repeat match goal with Hcast : sem_cast (Vsingle _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst; clear Hcast end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  lazymatch type of Hwrite with ocn_exec ?ge ?env ?temps ?memory _ ?tr ?last ?final ?o =>
    destruct (ifh_floor_result_store version env temps memory mb IBM._t'2 _ tr last final o
      ltac:(cbn [set_opttemp]; repeat rewrite PTree.gso by discriminate; exact Hm)
      ltac:(cbn [set_opttemp]; apply PTree.gss) Hwrite)
      as (floor & Hresult & Hstored & Hloaded & Hmovement & Ht & Hl & Ho) end.
  subst. unfold Eapp, E0. rewrite ?app_nil_r.
  exists floor, query_m. repeat apply conj; try reflexivity; eassumption.
Qed.

(** Unlike a pair of independently assumed calls, this statement extracts
    the copy and floor call from ONE taken retry and joins their memories.
    It neither assumes a non-null floor result nor assigns a behavior to it. *)
Definition InkRetrySameRunFloorCall : Prop :=
  forall version e le m mb ob slot values t le' m' out,
  e ! IBM._vec3f_copy = None -> e ! IBM._find_floor = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version))
    us_object_list_processor._gObjectPool = Some ob ->
  (slot < object_pool_capacity)%nat ->
  le ! IBM._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  (forall axis, Mem.load Mfloat32 m ob (object_slot_offset slot + 32 + 4 * icp_number axis) =
    Some (Vsingle (values axis))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ibk_retry version) t le' m' out ->
  exists copied query_m copy_trace query_trace result floor,
    t = copy_trace ++ query_trace /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      m (Internal (ibk_copy_body version))
      [Vptr mb (Ptrofs.repr 60); Vptr ob (Ptrofs.repr (object_slot_offset slot + 32))]
      copy_trace copied result /\
    (forall axis, Mem.load Mfloat32 copied mb (60 + 4 * icp_number axis) =
      Some (Vsingle (values axis))) /\
    ClightBigstep.Clight2.eval_funcall (Clight.globalenv (selected_clight_target version))
      copied (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values ICPX); Vsingle (values ICPY); Vsingle (values ICPZ);
       Vptr mb (Ptrofs.repr 104)] query_trace query_m (Vsingle floor) /\
    Mem.store Mfloat32 query_m mb 112 (Vsingle floor) = Some m' /\
    Mem.load Mfloat32 m' mb 64 = Mem.load Mfloat32 query_m mb 64 /\ out = Out_normal.

Theorem irq_retry_connects_display_to_real_floor_call : InkRetrySameRunFloorCall.
Proof.
  unfold InkRetrySameRunFloorCall.
  intros version e le m mb ob slot values t le' m' out
    HcopyLocal HfloorLocal Hmsym Hosym Hslot Hm Hobj Hvalues Hretry.
  destruct (irc_taken_retry_completes_before_second_query version e le m mb ob slot
    values t le' m' out HcopyLocal Hmsym Hosym Hslot Hm Hobj Hvalues Hretry)
    as (copied & copy_trace & query_trace & result & Htrace & Hcopy & Hposition & Hframe & Hquery).
  destruct (irq_second_floor_call_uses_completed_position version e
    (PTree.set IBM._t'45 (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le) copied mb values
    query_trace le' m' out HfloorLocal
    ltac:(rewrite PTree.gso by discriminate; exact Hm) Hposition Hquery)
    as (floor & query_m & Hfloor & Hstore & Hy & Hout).
  exists copied, query_m, copy_trace, query_trace, result, floor.
  repeat split; assumption.
Qed.
