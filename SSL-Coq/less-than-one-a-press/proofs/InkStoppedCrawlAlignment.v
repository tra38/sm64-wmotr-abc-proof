(** A stopped ground result really falls through to floor alignment in
    crawling.  The intervening speed check and, when taken, the complete
    real speed setter preserve positions and the cached floor height.

    This is a reached caller cut.  It does not grant a reachable stale
    cached floor or frame the later terrain-matrix/action-update tail. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_mario_actions_moving jp_mario_actions_moving.
From LessThanOneAPress.Proofs Require Import GameTypes InkBackwardSource
  InkBackwardExecution InkCopyCaller InkFloorResetSource InkFloorResetExecution
  InkMovingBackwardSource InkFloorAlignmentBackward InkWarpStop
  InkGroundBackwardSource InkGroundCallBackward InkGroundReturnFrame
  ObjectContactNecessity ContactConsumerExecution SecretContactExecution
  Area2Rank10AGroundPound Area2Rank12BContact OrdinaryArea1EntryMemory SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition isca_body version := match version with
| VersionUS => us_mario_actions_moving.f_act_crawling
| VersionJP => jp_mario_actions_moving.f_act_crawling end.
Definition isca_ground_dispatch version := ibk_head
  (rank12b_drop_sequences 8 (fn_body (isca_body version))).
Definition isca_dispatch version := match isca_ground_dispatch version with
| Ssequence _ dispatch => dispatch | _ => Sskip end.
Definition isca_cases version := match isca_dispatch version with
| Sswitch _ cases => cases | _ => LSnil end.
Definition isca_ground_call := Scall (Some IMB._t'8)
  (Evar IMB._perform_ground_step (Tfunction
    [tptr (Tstruct IMB._MarioState noattr)] tint cc_default))
  [Etempvar IMB._m (tptr (Tstruct IMB._MarioState noattr))].
Definition isca_two version := seq_of_labeled_statement (select_switch 2 (isca_cases version)).
Definition isca_speed_guard version := ibk_head (isca_two version).
Definition isca_speed_call := Scall None
  (Evar IMB._mario_set_forward_vel (Tfunction
    [tptr (Tstruct IMB._MarioState noattr);tfloat] tvoid cc_default))
  [Etempvar IMB._m (tptr (Tstruct IMB._MarioState noattr));
   Econst_single (Float32.of_bits (Int.repr 1092616192)) tfloat].
Definition isca_align_call := Scall None
  (Evar IMB._align_with_floor (Tfunction
    [tptr (Tstruct IMB._MarioState noattr)] tvoid cc_default))
  [Etempvar IMB._m (tptr (Tstruct IMB._MarioState noattr))].

Lemma isca_generated_cuts : forall version,
  isca_dispatch version = Sswitch (Etempvar IMB._t'8 tint) (isca_cases version) /\
  isca_two version = Ssequence (isca_speed_guard version)
    (Ssequence (Ssequence isca_align_call Sbreak) Sskip) /\
  isca_speed_guard version = Ssequence
    (Sset IMB._t'10 (Efield ibcc_state IMB._forwardVel tfloat))
    (Sifthenelse (Ebinop Ogt (Etempvar IMB._t'10 tfloat)
      (Econst_single (Float32.of_bits (Int.repr 1092616192)) tfloat) tint)
      isca_speed_call Sskip) /\
  ibk_normal (isca_speed_guard version) = true /\
  cce_keeps_temp IMB._m (isca_speed_guard version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma isca_generated_ground_call : forall version,
  isca_ground_dispatch version = Ssequence isca_ground_call (isca_dispatch version) /\
  ibk_normal isca_ground_call = true.
Proof. intros []; split; reflexivity. Qed.

(** The saved switch temporary is precisely the return of this reached
    call, whose receiver and internal implementation are both resolved. *)
Theorem isca_actual_ground_call_sets_its_result :
  forall version e le m mb t le' after out,
  e ! IMB._perform_ground_step = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    isca_ground_call t le' after out ->
  exists result,
    ClightBigstep.Clight2.eval_funcall
      (Clight.globalenv (selected_clight_target version)) m
      (Internal (igb_body version)) [Vptr mb Ptrofs.zero] t after result /\
    le' = PTree.set IMB._t'8 result le /\ out = Out_normal.
Proof.
  intros version e le m mb t le' after out Hlocal Hm Hrun.
  destruct (igb_selected_body_resolves version) as (fb & Hsymbol & Hfun).
  unfold isca_ground_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ =>
    cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by
      (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd)
      in Hfind; rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr mb Ptrofs.zero) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr mb Ptrofs.zero) = Some v) in Hcast;
    inversion Hcast; subst end.
  eexists. split; [eassumption|]. split; reflexivity.
Qed.

(** A real call/switch edge, retaining the completed callee's actual cuts.
    No condition independently supplies the caller's switch result. The
    ground prefix and its stopping reason still keep their reached effects. *)
Definition InkStoppedCrawlGroundReturnConnection : Prop :=
  forall version e le m mb t le' after out,
  let ge := Clight.globalenv (selected_clight_target version) in
  e ! IMB._perform_ground_step = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec ge e le m (isca_ground_dispatch version) t le' after out ->
  exists result returned caller_le ground_t dispatch_t ground_e entry_le entry_m
    cut_le cut_m copy_le copy_m last_le last_m pre copy_t suffix ground_out,
    t = ground_t ++ dispatch_t /\
    ClightBigstep.Clight2.eval_funcall ge m (Internal (igb_body version))
      [Vptr mb Ptrofs.zero] ground_t returned result /\
    caller_le = PTree.set IMB._t'8 result le /\
    caller_le ! IMB._t'8 = Some result /\
    caller_le ! IMB._m = Some (Vptr mb Ptrofs.zero) /\
    ocn_exec ge e caller_le returned (isca_dispatch version) dispatch_t le' after out /\
    ground_t = pre ++ (copy_t ++ suffix) /\
    function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero]
      m ground_e entry_le entry_m /\
    ocn_exec ge ground_e entry_le entry_m (igb_prefix version)
      pre cut_le cut_m Out_normal /\
    cut_le ! IFR._m = Some (Vptr mb Ptrofs.zero) /\
    ocn_exec ge ground_e cut_le cut_m (igb_refresh version)
      copy_t copy_le copy_m Out_normal /\
    ocn_exec ge ground_e copy_le copy_m (igb_tail version)
      suffix last_le last_m ground_out /\
    outcome_result_value ground_out (fn_return (igb_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge ground_e) = Some returned.

Theorem isca_actual_ground_call_connects_return_to_switch :
  InkStoppedCrawlGroundReturnConnection.
Proof.
  unfold InkStoppedCrawlGroundReturnConnection. cbn zeta.
  intros version e le m mb t le' after out Hname Hm Hrun.
  destruct (isca_generated_ground_call version) as [Hshape Hnormal].
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (caller_le & returned & ground_t & dispatch_t & Htrace & Hcall & Hdispatch).
  destruct (isca_actual_ground_call_sets_its_result version e le m mb
    ground_t caller_le returned Out_normal Hname Hm Hcall)
    as (result & Hreal & Hcaller & _).
  destruct (igb_completed_ground_call_reaches_display_refresh version m mb Ptrofs.zero
    ground_t returned result Hreal)
    as (ground_e & entry_le & entry_m & cut_le & cut_m & copy_le & copy_m &
      last_le & last_m & pre & copy_t & suffix & ground_out & HgroundTrace &
      Hentry & Hprefix & HcutM & HcopyName & Hcopy & Htail & Hresult & Hfree & HcopyWitness).
  exists result, returned, caller_le, ground_t, dispatch_t, ground_e, entry_le, entry_m,
    cut_le, cut_m, copy_le, copy_m, last_le, last_m, pre, copy_t, suffix, ground_out.
  repeat apply conj; try assumption.
  - rewrite Hcaller. apply PTree.gss.
  - rewrite Hcaller, PTree.gso by discriminate. exact Hm.
Qed.

Lemma isca_actual_speed_call_frame : forall version e le m mb t le' after out,
  e ! IMB._mario_set_forward_vel = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    isca_speed_call t le' after out ->
  forall chunk b offset, iws_outside_velocity mb chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m mb t le' after out Hlocal Hm Hrun.
  destruct (rank10a_selected_bodies_resolve version GPSetSpeed) as (fb & Hsymbol & Hfun).
  unfold isca_speed_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr mb Ptrofs.zero) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr mb Ptrofs.zero) = Some v) in Hcast;
    inversion Hcast; subst end.
  destruct (iws_speed_setter_preserves_position version _ mb _ _ _ _ ltac:(eassumption))
    as [_ Hframe]. exact Hframe.
Qed.

Lemma isca_speed_guard_frames_positions : forall version e le m mb t le' after out,
  e ! IMB._mario_set_forward_vel = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (isca_speed_guard version) t le' after out ->
  le' ! IMB._m = Some (Vptr mb Ptrofs.zero) /\
  (forall chunk b offset, iws_outside_velocity mb chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset).
Proof.
  intros version e le m mb t le' after out Hlocal Hm Hrun.
  split.
  - rewrite (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ _ Hrun
      (proj2 (proj2 (proj2 (proj2 (isca_generated_cuts version)))))). exact Hm.
  - pose proof Hrun as Hactual.
    rewrite (proj1 (proj2 (proj2 (isca_generated_cuts version)))) in Hrun.
    unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
    cce_unroll_loop_free_exec.
    all: try solve [intros chunk b offset Houtside;
      match goal with Hcall : ClightBigstep.exec_stmt _ _ _ ?temps ?before
        isca_speed_call ?trace ?lastTemps ?lastMemory ?callOut |- _ =>
        pose proof (isca_actual_speed_call_frame version e temps before mb
          trace lastTemps lastMemory callOut Hlocal
          ltac:(rewrite PTree.gso by discriminate; exact Hm) Hcall) as Hframe;
        exact (Hframe chunk b offset Houtside) end].
    all: intros; reflexivity.
Qed.

Lemma isca_actual_align_call : forall version e le m mb t le' after out,
  e ! IMB._align_with_floor = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    isca_align_call t le' after out ->
  exists result, ClightBigstep.Clight2.eval_funcall
    (Clight.globalenv (selected_clight_target version)) m
    (Internal (imb_body version IMBAlign)) [Vptr mb Ptrofs.zero] t after result.
Proof.
  intros version e le m mb t le' after out Hlocal Hm Hrun.
  destruct (imb_selected_bodies_resolve version IMBAlign) as (fb & Hsymbol & Hfun).
  unfold isca_align_call in Hrun. inversion Hrun; subst.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._m _) ?v |- _ =>
    assert (v = Vptr mb Ptrofs.zero) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hcast : sem_cast (Vptr mb Ptrofs.zero) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr mb Ptrofs.zero) = Some v) in Hcast;
    inversion Hcast; subst end.
  eexists; eassumption.
Qed.

Definition InkStoppedCrawlAlignmentCheckpoint : Prop :=
  forall version e le m mb ob floor t le' after out,
  let ge := Clight.globalenv (selected_clight_target version) in
  e ! IMB._mario_set_forward_vel = None -> e ! IMB._align_with_floor = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) -> le ! IMB._t'8 = Some (Vint (Int.repr 2)) ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.load Mfloat32 m mb 112 = Some (Vsingle floor) ->
  ocn_exec ge e le m (isca_dispatch version) t le' after out ->
  exists align_le align_m speed_t align_t align_result snap_le snap_m final_le final_out,
    t = speed_t ++ align_t /\
    ocn_exec ge e le m (isca_speed_guard version) speed_t align_le align_m Out_normal /\
    ClightBigstep.Clight2.eval_funcall ge align_m (Internal (imb_body version IMBAlign))
      [Vptr mb Ptrofs.zero] align_t after align_result /\
    Mem.load Mfloat32 align_m mb 64 = Mem.load Mfloat32 m mb 64 /\
    Mem.load Mfloat32 align_m mb 112 = Some (Vsingle floor) /\
    Mem.store Mfloat32 align_m mb 64 (Vsingle floor) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle floor) /\
    (forall chunk offset, Mem.load chunk snap_m ob offset = Mem.load chunk m ob offset) /\
    ocn_exec ge empty_env snap_le snap_m (imb_align_tail version)
      align_t final_le after final_out.

Theorem isca_stopped_crawl_reaches_real_cached_floor_snap : InkStoppedCrawlAlignmentCheckpoint.
Proof.
  unfold InkStoppedCrawlAlignmentCheckpoint. cbn zeta.
  intros version e le m mb ob floor t le' after out
    HspeedName HalignName Hm Htwo Hstate Hpool Hfloor Hrun.
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hseparate.
  destruct (isca_generated_cuts version) as (Hdispatch & Hcase & Hguard & Hnormal & Hkeep).
  rewrite Hdispatch in Hrun. inversion Hrun; subst.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IMB._t'8 _) ?v |- _ =>
    assert (v = Vint (Int.repr 2)) by (eapply ocn_temp_value; eauto); subst v end.
  match goal with Hswitch : sem_switch_arg _ _ = Some ?n |- _ =>
    change (Some 2 = Some n) in Hswitch; inversion Hswitch; subst n end.
  match goal with Hr : ClightBigstep.exec_stmt _ ?ge ?env ?temps ?memory
    (seq_of_labeled_statement (select_switch 2 _)) ?rt ?rl ?rm ?ro |- _ =>
    change (ocn_exec ge env temps memory (isca_two version) rt rl rm ro) in Hr;
    rewrite Hcase in Hr;
    destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hr)
      as (align_le & align_m & speed_t & rest_t & Htrace & Hspeed & Hrest) end.
  destruct (isca_speed_guard_frames_positions _ _ _ _ _ _ _ _ _ HspeedName Hm Hspeed)
    as [HalignM HspeedFrame].
  assert (Mem.load Mfloat32 align_m mb 112 = Some (Vsingle floor)) as Hcached.
  { rewrite HspeedFrame; [exact Hfloor|right; right; lia]. }
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrest.
  cce_unroll_loop_free_exec.
  all: try solve [match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _
    isca_align_call _ _ _ ?bad, Hbad : ?bad <> Out_normal |- _ =>
    inversion Hcall; subst; contradiction end].
  all: match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _
    isca_align_call ?call_t _ ?call_after _ |- _ =>
    destruct (isca_actual_align_call version e align_le align_m mb call_t _ call_after _
      HalignName HalignM Hcall) as [result Hreal];
    destruct (imb_alignment_copies_entry_floor_and_preserves_object version align_m
      mb ob floor call_t call_after result Hstate Hpool Hcached Hreal)
      as (snap_le & snap_m & final_le & final_out & Hstore & Hsnap & Hobject & HsnapM & Htail);
    exists align_le, align_m, speed_t, call_t, result, snap_le, snap_m, final_le, final_out
    end.
  all: repeat apply conj; try assumption.
  all: try (rewrite E0_right; reflexivity).
  all: try (apply HspeedFrame; unfold iws_outside_velocity; right; left; cbn; lia).
  all: intros chunk offset; rewrite Hobject, HspeedFrame;
    [reflexivity|left; congruence].
Qed.

Theorem isca_stopped_crawl_alignment_checked : InkStoppedCrawlAlignmentCheckpoint.
Proof. exact isca_stopped_crawl_reaches_real_cached_floor_snap. Qed.

(** One continuous reached return/caller segment: the real ground refresh
    and return leave the old movement height in display, then stopped
    crawling copies the cached floor into movement.  Agreement with the
    cached floor is neither required nor inferred. *)
Definition InkStoppedCrawlReturnedGap : Prop :=
  forall version start mb ob slot height floor ground_e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t ground_last_le ground_last_m
    ground_out returned caller_e caller_le dispatch_t caller_last_le after caller_out,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block start mb -> Mem.valid_block start ob -> Mem.valid_block cut_m ob ->
  function_entry2 ge (igb_body version) [Vptr mb Ptrofs.zero]
    start ground_e entry_le entry_m ->
  cut_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
  Mem.load Mfloat32 cut_m mb 112 = Some (Vsingle floor) ->
  ocn_exec ge ground_e cut_le cut_m (igb_refresh version) copy_t copy_le copy_m Out_normal ->
  ocn_exec ge ground_e copy_le copy_m (igb_tail version)
    tail_t ground_last_le ground_last_m ground_out ->
  Mem.free_list ground_last_m (blocks_of_env ge ground_e) = Some returned ->
  caller_e ! IMB._mario_set_forward_vel = None -> caller_e ! IMB._align_with_floor = None ->
  caller_le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  caller_le ! IMB._t'8 = Some (Vint (Int.repr 2)) ->
  ocn_exec ge caller_e caller_le returned (isca_dispatch version)
    dispatch_t caller_last_le after caller_out ->
  exists align_m align_t align_result snap_m,
    ClightBigstep.Clight2.eval_funcall ge align_m (Internal (imb_body version IMBAlign))
      [Vptr mb Ptrofs.zero] align_t after align_result /\
    Mem.store Mfloat32 align_m mb 64 (Vsingle floor) = Some snap_m /\
    Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle floor) /\
    Mem.load Mfloat32 snap_m ob (object_slot_offset slot + 36) = Some (Vsingle height).

Theorem isca_ground_return_then_stopped_crawl_has_exact_gap : InkStoppedCrawlReturnedGap.
Proof.
  unfold InkStoppedCrawlReturnedGap. cbn zeta.
  intros version start mb ob slot height floor ground_e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t ground_last_le ground_last_m
    ground_out returned caller_e caller_le dispatch_t caller_last_le after caller_out
    Hslot Hstate Hpool HstartM HstartO HcutO Hentry Hm Hobject Hheight Hfloor
    Hcopy Htail Hfree HspeedName HalignName HcallerM Htwo Hdispatch.
  pose proof (ibcc_ordinary_storage_separate _ _ _ Hstate Hpool) as Hsep.
  destruct (igr_refresh_and_return_keep_the_cut_heights version start mb ob slot height floor
    ground_e entry_le entry_m cut_le cut_m copy_t copy_le copy_m tail_t
    ground_last_le ground_last_m ground_out returned Hslot Hsep HstartM HstartO HcutO
    Hentry Hm Hobject Hheight Hfloor Hcopy Htail Hfree) as (HreturnedM & HreturnedFloor & Hdisplay).
  destruct (isca_stopped_crawl_reaches_real_cached_floor_snap version caller_e caller_le
    returned mb ob floor dispatch_t caller_last_le after caller_out HspeedName HalignName
    HcallerM Htwo Hstate Hpool HreturnedFloor Hdispatch)
    as (align_le & align_m & speed_t & align_t & align_result & snap_le & snap_m &
      final_le & final_out & Htrace & Hspeed & Hcall & Hmove & Hcached & Hstore &
      Hsnap & HobjectFrame & Hmatrix).
  exists align_m, align_t, align_result, snap_m.
  repeat split; try assumption. rewrite HobjectFrame. exact Hdisplay.
Qed.

Theorem isca_stopped_crawl_returned_gap_checked : InkStoppedCrawlReturnedGap.
Proof. exact isca_ground_return_then_stopped_crawl_has_exact_gap. Qed.

(** A result of two from that same completed ground callee feeds the
    real switch and alignment. The cached-height premise is read in the
    actual returned memory; it is not the queried local height. *)
Definition InkStoppedCrawlActualResultAlignment : Prop :=
  forall version e le m mb ob t le' after out,
  let ge := Clight.globalenv (selected_clight_target version) in
  e ! IMB._perform_ground_step = None ->
  e ! IMB._mario_set_forward_vel = None -> e ! IMB._align_with_floor = None ->
  le ! IMB._m = Some (Vptr mb Ptrofs.zero) ->
  Genv.find_symbol ge us_object_list_processor._gMarioStates = Some mb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  ocn_exec ge e le m (isca_ground_dispatch version) t le' after out ->
  exists result returned caller_le ground_t dispatch_t,
    t = ground_t ++ dispatch_t /\
    ClightBigstep.Clight2.eval_funcall ge m (Internal (igb_body version))
      [Vptr mb Ptrofs.zero] ground_t returned result /\
    caller_le ! IMB._t'8 = Some result /\
    ocn_exec ge e caller_le returned (isca_dispatch version) dispatch_t le' after out /\
    (result = Vint (Int.repr 2) ->
      forall floor, Mem.load Mfloat32 returned mb 112 = Some (Vsingle floor) ->
      exists align_m align_t align_result snap_m,
        ClightBigstep.Clight2.eval_funcall ge align_m (Internal (imb_body version IMBAlign))
          [Vptr mb Ptrofs.zero] align_t after align_result /\
        Mem.load Mfloat32 align_m mb 64 = Mem.load Mfloat32 returned mb 64 /\
        Mem.store Mfloat32 align_m mb 64 (Vsingle floor) = Some snap_m /\
        Mem.load Mfloat32 snap_m mb 64 = Some (Vsingle floor) /\
        (forall chunk offset,
          Mem.load chunk snap_m ob offset = Mem.load chunk returned ob offset)).

Theorem isca_real_ground_result_two_reaches_alignment :
  InkStoppedCrawlActualResultAlignment.
Proof.
  unfold InkStoppedCrawlActualResultAlignment. cbn zeta.
  intros version e le m mb ob t le' after out
    HgroundName HspeedName HalignName Hm Hstate Hpool Hrun.
  destruct (isca_actual_ground_call_connects_return_to_switch version e le m mb
    t le' after out HgroundName Hm Hrun)
    as (result & returned & caller_le & ground_t & dispatch_t & ground_e &
      entry_le & entry_m & cut_le & cut_m & copy_le & copy_m & last_le & last_m &
      pre & copy_t & suffix & ground_out & Htrace & Hreal & Hcaller & Hresult &
      HcallerM & Hdispatch & Hcuts).
  exists result, returned, caller_le, ground_t, dispatch_t.
  repeat apply conj; try assumption.
  intros Htwo floor Hcached.
  assert (caller_le ! IMB._t'8 = Some (Vint (Int.repr 2))) as Hstopped by
    (rewrite Hresult; now rewrite Htwo).
  destruct (isca_stopped_crawl_reaches_real_cached_floor_snap version e caller_le
    returned mb ob floor dispatch_t le' after out HspeedName HalignName HcallerM
    Hstopped Hstate Hpool Hcached Hdispatch)
    as (align_le & align_m & speed_t & align_t & align_result & snap_le & snap_m &
      final_le & final_out & HdispatchTrace & Hspeed & Halign & Hmove & Hfloor &
      Hstore & Hsnap & HobjectFrame & Htail).
  exists align_m, align_t, align_result, snap_m. repeat split; assumption.
Qed.

Theorem isca_actual_ground_return_connection_checked :
  InkStoppedCrawlGroundReturnConnection /\ InkStoppedCrawlActualResultAlignment.
Proof. split; [exact isca_actual_ground_call_connects_return_to_switch|
  exact isca_real_ground_result_two_reaches_alignment]. Qed.
