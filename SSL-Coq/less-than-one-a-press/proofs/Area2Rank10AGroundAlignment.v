(** Conditional Rank-10A ground alignment. The live query answers remain
    premises; the generated vector setter and post-alignment wall handling
    do not. No assumption says that a completed quarter aligns Mario. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_math_util jp_math_util.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank10ABlockedStep Area2Rank12BContact
  InkFloorHistorySource InkFloorHistoryExecution InkFloorHistoryCall InkFloorHistoryQuery
  InkBackwardSource InkBackwardExecution InkCopyEntry InkCopyCaller
  InkCopyCompletion InkRetryCompletion InkFloorResetExecution InkFloorResetSource
  InkInputContinuationSource InkInputAngleFrame ObjectContactNecessity
  ContactConsumerExecution SecretContactExecution SelectedClightTarget
  UpperElevatorQueryResolution ContactConsumerSource CleanedClightPrograms
  ClightLinkExecution GlobalInterfaceStructural JPSourceSymbolTransport
  JPWarpLevelEntryResolution LinkedClightPrograms NormalizedClightPrograms
  SuccessfulMakeProgramResolution USViewportRepairedNamesNorepet
  USViewportRepairedProgramSelection USWarpLevelRepairReceipt
  USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

From LessThanOneAPress.Proofs Require Import Area2GroundVectorSetSource.

Definition rank10g_set_temp axis := match axis with
| ICPX => IBV._t'3 | ICPY => IBV._t'2 | ICPZ => IBV._t'1 end.
Definition rank10g_set_arg axis := match axis with
| ICPX => IBV._x | ICPY => IBV._y | ICPZ => IBV._z end.
Definition rank10g_set_stage version axis := ibk_head
  (rank12b_drop_sequences (match axis with ICPX => 1 | ICPY => 2 | ICPZ => 3 end)
    (fn_body (rank10g_set_body version))).
Definition rank10g_set_return version :=
  rank12b_drop_sequences 4 (fn_body (rank10g_set_body version)).
Lemma rank10g_set_source : forall version,
  fn_body (rank10g_set_body version) = Ssequence ibc_local_init
    (Ssequence (rank10g_set_stage version ICPX)
      (Ssequence (rank10g_set_stage version ICPY)
        (Ssequence (rank10g_set_stage version ICPZ) (rank10g_set_return version)))).
Proof. intros []; reflexivity. Qed.
Lemma rank10g_set_stage_source : forall version axis,
  rank10g_set_stage version axis = Ssequence
    (Sset (rank10g_set_temp axis) (Evar IBV._dest (tptr tfloat)))
    (Sassign (ibc_index (rank10g_set_temp axis) (icp_number axis))
      (Etempvar (rank10g_set_arg axis) tfloat)) /\
  ibk_normal (rank10g_set_stage version axis) = true.
Proof. intros [] []; split; reflexivity. Qed.

Lemma rank10g_set_entry : forall version ge m destination x y z e le entry,
  function_entry2 ge (rank10g_set_body version)
    [destination; Vsingle x; Vsingle y; Vsingle z] m e le entry ->
  exists local, Mem.alloc m 0 (sizeof ge (tptr tfloat)) = (entry,local) /\
    e = PTree.set IBV._dest (local,tptr tfloat) empty_env /\
    le ! IBV._dest = Some destination /\ le ! IBV._x = Some (Vsingle x) /\
    le ! IBV._y = Some (Vsingle y) /\ le ! IBV._z = Some (Vsingle z).
Proof.
  intros version ge m destination x y z e le entry Hentry.
  assert (fn_vars (rank10g_set_body version) = [(IBV._dest,tptr tfloat)]) as Hv
    by (destruct version; reflexivity).
  inversion Hentry; subst.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hv in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  match goal with Hb : bind_parameter_temps _ _ _ = Some le |- _ =>
    destruct version; cbn in Hb; inversion Hb; subst le end;
    eexists; repeat split; eauto; reflexivity.
Qed.

Lemma rank10g_set_stage_store : forall version axis ge e le m local db d value t le' m' out,
  e ! IBV._dest = Some (local,tptr tfloat) ->
  Mem.load Mint32 m local 0 = Some (Vptr db (Ptrofs.repr d)) ->
  le ! (rank10g_set_arg axis) = Some (Vsingle value) ->
  0 <= d -> d + 8 <= Ptrofs.max_unsigned ->
  ocn_exec ge e le m (rank10g_set_stage version axis) t le' m' out ->
  Mem.store Mfloat32 m db (d + 4 * icp_number axis) (Vsingle value) = Some m'.
Proof.
  intros version axis ge e le m local db d value t le' m' out
    Hlocal Hdest Hvalue Hd Hrange Hrun.
  rewrite (proj1 (rank10g_set_stage_source version axis)) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ (Evar IBV._dest _) ?v |- _ =>
    assert (v = Vptr db (Ptrofs.repr d)) by (eapply ibc_pointer_local_read; eauto); subst v end.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  match goal with Hl : eval_lvalue _ _ _ _ (ibc_index _ _) _ _ _ |- _ =>
    destruct (ibc_index_location _ _ _ _ _ _ _ _ _ _ _ (PTree.gss _ _ _) Hl)
      as (-> & -> & ->) end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar (rank10g_set_arg axis) _) ?v |- _ =>
    assert (v = Vsingle value) by (eapply ocn_temp_value;
      [exact Hr|rewrite PTree.gso by (destruct axis; discriminate); exact Hvalue]); subst v end.
  match goal with Hc : sem_cast _ _ _ _ = Some _ |- _ => cbn in Hc; inversion Hc; subst end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  match goal with Hs : Mem.storev _ ?memory _ _ = Some ?final |- _ =>
    change (Mem.store Mfloat32 memory db (icp_offset (Ptrofs.repr d) axis)
      (Vsingle value) = Some final) in Hs;
    rewrite irc_plain_offset in Hs by assumption; exact Hs end.
Qed.

(** Complete the real allocation, all three writes, return and local free.
    This is an effect of an actual call, not a supplied vec3f_set contract. *)
Theorem rank10g_completed_set_y : forall version ge m db d x y z t after result,
  Mem.valid_block m db -> 0 <= d -> d + 8 <= Ptrofs.max_unsigned ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (rank10g_set_body version))
    [Vptr db (Ptrofs.repr d); Vsingle x; Vsingle y; Vsingle z] t after result ->
  Mem.load Mfloat32 after db (d + 4) = Some (Vsingle y).
Proof.
  intros version ge m db d x y z t after result Hvalid Hd Hrange Hcall.
  inversion Hcall; subst.
  match goal with He : function_entry2 _ _ _ _ _ _ _ |- _ =>
    destruct (rank10g_set_entry _ _ _ _ _ _ _ _ _ _ He)
      as (local & Halloc & -> & Hdest & Hxarg & Hyarg & Hzarg) end.
  assert (local <> db) as Hsep by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  match goal with Hr : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    rewrite rank10g_set_source in Hr;
    destruct (ibk_split_sequence _ _ _ _ ibc_local_init _ _ _ _ _ eq_refl Hr)
      as (il & im & it & rt & Htrace & Hinit & Hrest) end.
  destruct (ibc_local_init_store _ _ _ _ _ _ _ _ _ _ (PTree.gss _ _ _) Hdest
    ltac:(do 2 eexists; reflexivity) Hinit) as (HinitStore & -> & -> & _).
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (rank10g_set_stage_source version ICPX)) Hrest)
    as (xl & xm & xt & yz & Hxt & Hx & Hyz).
  pose proof (rank10g_set_stage_store version ICPX _ _ _ _ local db d x _ _ _ _
    (PTree.gss _ _ _) (Mem.load_store_same _ _ _ _ _ _ HinitStore) Hxarg Hd Hrange Hx) as Hxs.
  assert (Mem.load Mint32 xm local 0 = Some (Vptr db (Ptrofs.repr d))) as HlocalX.
  { erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ HinitStore)|
      exact Hxs|left; congruence]. }
  assert (xl ! IBV._y = Some (Vsingle y) /\ xl ! IBV._z = Some (Vsingle z))
    as [HyargX HzargX].
  { split; (erewrite ifr_execution_keeps_temp; [eassumption|exact Hx|destruct version; reflexivity]). }
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (rank10g_set_stage_source version ICPY)) Hyz)
    as (yl & ym & yt & zr & Hyt & Hy & Hzr).
  pose proof (rank10g_set_stage_store version ICPY _ _ _ _ local db d y _ _ _ _
    (PTree.gss _ _ _) HlocalX HyargX Hd Hrange Hy) as Hys.
  assert (Mem.load Mint32 ym local 0 = Some (Vptr db (Ptrofs.repr d))) as HlocalY.
  { erewrite Mem.load_store_other; [exact HlocalX|exact Hys|left; congruence]. }
  assert (yl ! IBV._z = Some (Vsingle z)) as HzargY.
  { erewrite ifr_execution_keeps_temp; [exact HzargX|exact Hy|destruct version; reflexivity]. }
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _
    (proj2 (rank10g_set_stage_source version ICPZ)) Hzr)
    as (zl & zm & zt & ret_trace & Hzt & Hz & Hreturn).
  pose proof (rank10g_set_stage_store version ICPZ _ _ _ _ local db d z _ _ _ _
    (PTree.gss _ _ _) HlocalY HzargY Hd Hrange Hz) as Hzs.
  assert (rank10g_set_return version = Sreturn (Some (Eaddrof
    (Evar IBV._dest (tptr tfloat)) (tptr (tptr tfloat))))) as Hret
    by (destruct version; reflexivity).
  rewrite Hret in Hreturn. inversion Hreturn; subst.
  match goal with Hfree : Mem.free_list ?last (blocks_of_env _ _) = Some ?answer |- _ =>
    change (Mem.free_list last [(local,0,4)] = Some answer) in Hfree;
    cbn [Mem.free_list] in Hfree;
    destruct (Mem.free last local 0 4) as [freed|] eqn:HfreeOne; try discriminate;
    inversion Hfree; subst end.
  erewrite Mem.load_free; [|exact HfreeOne|left; congruence].
  erewrite Mem.load_store_other; [|exact Hzs|right; left; cbn [size_chunk icp_number]; lia].
  exact (Mem.load_store_same _ _ _ _ _ _ Hys).
Qed.

(** This suffix can call atan2s, whose complete selected-body frame is
    already proved. Arbitrary outside-call preservation is not a premise. *)
Inductive rank10g_post_statement : statement -> Prop :=
| rank10g_readonly : forall s, cce_readonly_keep IFH._m s = true -> rank10g_post_statement s
| rank10g_angle : forall opt args, rank10g_post_statement
    (Scall opt (Evar (iis_ident IIAngle) (Tfunction [tfloat;tfloat] tshort cc_default)) args)
| rank10g_seq : forall a b, rank10g_post_statement a -> rank10g_post_statement b ->
    rank10g_post_statement (Ssequence a b)
| rank10g_if : forall c yes no, rank10g_post_statement yes -> rank10g_post_statement no ->
    rank10g_post_statement (Sifthenelse c yes no).
Lemma rank10g_post_classified : forall version,
  rank10g_post_statement (ifh_accept_after version).
Proof.
  intros []; cbn [ifh_accept_after ifh_accept rank12b_drop_sequences ifh_quarter_body fn_body].
  all: repeat first [apply rank10g_readonly; reflexivity | apply rank10g_angle |
    apply rank10g_seq | apply rank10g_if].
Qed.
Lemma rank10g_post_frame : forall s, rank10g_post_statement s ->
  forall version e le m t le' after out,
  e ! IFH._atan2s = None ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m s t le' after out ->
  after = m.
Proof.
  intros s Hshape. induction Hshape; intros version e le m t le' after out Hlocal Hrun.
  - exact (proj1 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrun H))).
  - inversion Hrun; subst.
    match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
    destruct (iis_selected_helpers_resolve version IIAngle) as (fb & Hsymbol & Hfunction).
    match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
      assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
    match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
      change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
      rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
    match goal with Hcall : ClightBigstep.eval_funcall _ _ _ _ _ _ _ _ |- _ =>
      exact (proj2 (iia_angle_call_preserves_memory _ _ _ _ _ _ Hcall)) end.
  - inversion Hrun; subst.
    + match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ a _ _ _ _,
        Hb : ClightBigstep.exec_stmt _ _ _ _ _ b _ _ _ _ |- _ =>
        rewrite (IHHshape2 _ _ _ _ _ _ _ _ Hlocal Hb);
        exact (IHHshape1 _ _ _ _ _ _ _ _ Hlocal Ha) end.
    + eapply IHHshape1; eauto.
  - inversion Hrun; subst. destruct b; [eapply IHHshape1|eapply IHHshape2]; eauto.
Qed.

Definition rank10g_set_call := Scall None (Evar IFH._vec3f_set
  (Tfunction [tptr tfloat;tfloat;tfloat;tfloat] (tptr tvoid) cc_default))
  [ibcc_destination;Etempvar IFH._t'14 tfloat;Etempvar IFH._floorHeight tfloat;
   Etempvar IFH._t'15 tfloat].
Lemma rank10g_move_source : forall version,
  ifh_accept_move version = Ssequence (Sset IFH._t'14 (ifh_next 0))
    (Ssequence (Sset IFH._t'15 (ifh_next 2)) rank10g_set_call).
Proof. intros []; reflexivity. Qed.
Theorem rank10g_move_completes_y : forall version e le m mb floor t le' after out,
  e ! IFH._vec3f_set = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._floorHeight = Some (Vsingle floor) ->
  Mem.valid_block m mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_accept_move version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle floor).
Proof.
  intros version e le m mb floor t le' after out Hlocal Hm Hfloor Hvalid Hrun.
  rewrite rank10g_move_source in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: try contradiction.
  match goal with Hc : ClightBigstep.exec_stmt _ _ _ _ _ rank10g_set_call _ _ _ _ |- _ =>
    inversion Hc; subst; clear Hc end.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  destruct (rank10g_selected_set_resolves version) as (fb & Hsymbol & Hfunction).
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?vf |- _ =>
    assert (vf = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst vf end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfunction in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Hr : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Hr; subst; clear Hr end.
  lazymatch goal with Hr : eval_expr _ ?environment ?temps ?memory ibcc_destination ?v |- _ =>
    assert (v = Vptr mb (Ptrofs.repr 60)) by
      (eapply (ifr_state_position_value version environment temps memory mb Ptrofs.zero);
      [repeat rewrite PTree.gso by discriminate; exact Hm|exact Hr]); subst v end.
  match goal with Hr : eval_expr _ _ _ _ (Etempvar IFH._floorHeight _) ?v |- _ =>
    assert (v = Vsingle floor) by (eapply ocn_temp_value;
      [exact Hr|repeat rewrite PTree.gso by discriminate; exact Hfloor]); subst v end.
  repeat match goal with Hcast : sem_cast ?value ?ty tfloat ?memory = Some ?answer |- _ =>
    change (sem_cast value tfloat tfloat memory = Some answer) in Hcast;
    destruct (ifh_float_cast_identity _ _ _ Hcast) as (? & ? & ?); subst; clear Hcast end.
  repeat match goal with Heq : Vsingle _ = Vsingle _ |- _ => inversion Heq; subst; clear Heq end.
  match goal with Hcast : sem_cast (Vptr _ _) _ _ _ = Some _ |- _ =>
    cbn in Hcast; inversion Hcast; subst end.
  eapply (rank10g_completed_set_y version _ _ mb 60).
  - exact Hvalid.
  - lia.
  - change (68 <= 4294967295). lia.
  - eassumption.
Qed.

Lemma rank10g_floor_pointer_frame : forall version e le m mb t le' after out,
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_accept_floor version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Mem.load Mfloat32 m mb 64.
Proof.
  intros version e le m mb t le' after out Hm Hrun.
  assert (ifh_accept_floor version = Ssequence
    (Sset IFH._t'13 (Evar IFH._floor (tptr (Tstruct IFH._Surface noattr))))
    (Sassign ibk_floor_read (Etempvar IFH._t'13 (tptr (Tstruct IFH._Surface noattr))))) as Hshape
    by (destruct version; reflexivity).
  rewrite Hshape in Hrun. unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Ha : ClightBigstep.exec_stmt _ _ _ _ _ (Sassign _ _) _ _ _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  all: try contradiction.
  lazymatch goal with Hl : eval_lvalue ?ge ?environment ?temps ?memory ibk_floor_read _ _ _ |- _ =>
    destruct (ibcc_field_location ge environment temps memory ibcc_state IBM._MarioState IBM._floor
      (tptr (Tstruct IBM._Surface noattr)) mb Ptrofs.zero 104 _ _ _ eq_refl
      ltac:(intros; eapply (ibcc_deref_struct ge environment temps memory
        IFH._m IFH._MarioState mb Ptrofs.zero);
        [rewrite PTree.gso by discriminate; exact Hm|eassumption])
      (ifh_selected_floor_pointer_field version) Hl) as (-> & -> & ->) end.
  match goal with Ha : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion Ha; subst; try discriminate end.
  match goal with Hmode : access_mode _ = By_value _ |- _ => cbn in Hmode; inversion Hmode; subst end.
  lazymatch goal with Hs : Mem.storev _ ?memory _ ?value = Some ?final |- _ =>
    change (Mem.store Mint32 memory mb 104 value = Some final) in Hs;
    eapply Mem.load_store_other; [exact Hs|right; left; cbn; lia] end.
Qed.

Theorem rank10g_accept_completes_y : forall version e le m mb floor t le' after out,
  e ! IFH._vec3f_set = None -> e ! IFH._atan2s = None ->
  le ! IFH._m = Some (Vptr mb Ptrofs.zero) ->
  le ! IFH._floorHeight = Some (Vsingle floor) -> Mem.valid_block m mb ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (ifh_accept version) t le' after out ->
  Mem.load Mfloat32 after mb 64 = Some (Vsingle floor).
Proof.
  intros version e le m mb floor t le' after out Hset Hangle Hm Hfloor Hvalid Hrun.
  assert (ifh_accept version = Ssequence (ifh_accept_move version)
    (Ssequence (ifh_accept_floor version)
      (Ssequence (ifh_accept_height version) (ifh_accept_after version)))) as Hshape
    by (destruct version; reflexivity).
  rewrite Hshape in Hrun.
  destruct (ibk_split_sequence _ _ _ _ (ifh_accept_move version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrun) as (ml & mm & mt & rt & Ht & Hmove & Hrest).
  pose proof (rank10g_move_completes_y _ _ _ _ _ _ _ _ _ _ Hset Hm Hfloor Hvalid Hmove) as Hy.
  assert (ml ! IFH._m = Some (Vptr mb Ptrofs.zero) /\
    ml ! IFH._floorHeight = Some (Vsingle floor)) as [Hm1 Hf1].
  { split; (erewrite ifr_execution_keeps_temp; [eassumption|exact Hmove|destruct version; reflexivity]). }
  destruct (ibk_split_sequence _ _ _ _ (ifh_accept_floor version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrest) as (fl & fm & ft & ht & Hft & Hfp & Hrest2).
  pose proof (rank10g_floor_pointer_frame _ _ _ _ _ _ _ _ _ Hm1 Hfp) as Hframe1.
  assert (fl ! IFH._m = Some (Vptr mb Ptrofs.zero) /\
    fl ! IFH._floorHeight = Some (Vsingle floor)) as [Hm2 Hf2].
  { split; (erewrite ifr_execution_keeps_temp; [eassumption|exact Hfp|destruct version; reflexivity]). }
  destruct (ibk_split_sequence _ _ _ _ (ifh_accept_height version) _ _ _ _ _
    ltac:(destruct version; reflexivity) Hrest2) as (hl & hm & ht' & at' & Hht & Hheight & Hafter).
  assert (ifh_accept_height version = Sassign ifr_floor_read
    (Etempvar IFH._floorHeight tfloat)) as Hh by (destruct version; reflexivity).
  rewrite Hh in Hheight.
  destruct (ifh_floor_result_store _ _ _ _ _ _ _ _ _ _ _ Hm2 Hf2 Hheight)
    as (f & Heq & Hstore & Hload & Hframe2 & _).
  rewrite (rank10g_post_frame _ (rank10g_post_classified version) _ _ _ _ _ _ _ _ Hangle Hafter).
  rewrite Hframe2, Hframe1. exact Hy.
Qed.
