(** The compulsory air-step refresh survives the real angle setter, return
    and local free. It equates display and movement Y, while leaving the raw
    collision record at the copy cut unchanged. No actor height is assumed. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkAirCallBackward
  InkGroundReturnFrame InkCopyCompletion InkCopyCaller InkBackwardSource
  InkBackwardExecution InkFloorResetSource InkFloorResetExecution
  ContactConsumerExecution SecretContactExecution ObjectContactNecessity
  OrdinaryArea1EntryMemory Area2Rank12BContact SelectedClightTarget.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition iar_air_angle version := ibk_head (iaf_tail version).
Definition iar_after_angle version := rank12b_drop_sequences 9 (fn_body (iaf_body version)).
Definition iar_air_object := Ederef
  (Etempvar IFR._t'6 (tptr (Tstruct IFR._Object noattr))) (Tstruct IFR._Object noattr).
Definition iar_air_header := Efield iar_air_object IFR._header (Tstruct IFR._ObjectNode noattr).
Definition iar_air_graphics := Efield iar_air_header IFR._gfx (Tstruct IFR._GraphNodeObject noattr).
Definition iar_air_angles := Efield iar_air_graphics IFR._angle (tarray tshort 3).
Definition iar_air_angle_call := Scall None
  (Evar IFR._vec3s_set (Tfunction [tptr tshort;tshort;tshort;tshort] (tptr tvoid) cc_default))
  [iar_air_angles;Econst_int Int.zero tint;Etempvar IFR._t'7 tshort;Econst_int Int.zero tint].

Lemma iar_air_tail_source : forall version,
  iaf_tail version = Ssequence (iar_air_angle version) (iar_after_angle version) /\
  iar_air_angle version = Ssequence (Sset IFR._t'6 ibk_object_read)
    (Ssequence
      (Sset IFR._t'7 (Ederef (Ebinop Oadd
        (Efield ibcc_state IFR._faceAngle (tarray tshort 3))
        (Econst_int (Int.repr 1) tint) (tptr tshort)) tshort)) iar_air_angle_call) /\
  ibk_normal (iar_air_angle version) = true /\
  cce_readonly_keep IFR._m (iar_after_angle version) = true.
Proof. intros []; repeat split; reflexivity. Qed.

Lemma iar_air_angle_address : forall version e le m ob oo answer,
  le ! IFR._t'6 = Some (Vptr ob oo) ->
  eval_expr (Clight.globalenv (selected_clight_target version)) e le m
    iar_air_angles answer -> answer = Vptr ob (Ptrofs.add oo (Ptrofs.repr 26)).
Proof.
  intros version e le m ob oo answer Hobject Hr.
  destruct (ibcc_selected_fields version) as (_ & _ & Hheader & Hgfx & _).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iar_air_object v -> v = Vptr ob oo) as Hobj
    by (intros; eapply ibcc_deref_struct; eauto).
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iar_air_header v -> v = Vptr ob oo) as Hhead.
  { intros v Hread. pose proof (ibcc_aggregate_field _ _ _ _ iar_air_object
      IFR._Object IFR._header (Tstruct IFR._ObjectNode noattr) ob oo 0 v
      eq_refl Hobj Hheader (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  assert (forall v, eval_expr (Clight.globalenv (selected_clight_target version))
    e le m iar_air_graphics v -> v = Vptr ob oo) as Hgraph.
  { intros v Hread. pose proof (ibcc_aggregate_field _ _ _ _ iar_air_header
      IFR._ObjectNode IFR._gfx (Tstruct IFR._GraphNodeObject noattr) ob oo 0 v
      eq_refl Hhead Hgfx (or_intror eq_refl) Hread) as H.
    rewrite Ptrofs.add_zero in H. exact H. }
  exact (ibcc_aggregate_field _ _ _ _ iar_air_graphics
    IFR._GraphNodeObject IFR._angle (tarray tshort 3) ob oo 26 answer
    eq_refl Hgraph (igr_selected_angle_field version) (or_introl eq_refl) Hr).
Qed.

Definition InkAirRefreshCompleted : Prop :=
  forall version e le m mb ob slot height t le' after out,
  (slot < object_pool_capacity)%nat -> mb <> ob -> Mem.valid_block m ob ->
  e ! IFR._vec3f_copy = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 m mb 64 = Some (Vsingle height) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iaf_refresh version) t le' after out ->
  Mem.load Mfloat32 after ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
  (forall chunk b offset, Mem.valid_block m b -> icp_outside_display ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset).

Theorem iar_air_refresh_completes_without_old_display : InkAirRefreshCompleted.
Proof.
  unfold InkAirRefreshCompleted.
  intros version e le m mb ob slot height t le' after out Hslot Hsep Hvalid Hname Hm Hobj Hy Hr.
  destruct (iaf_refresh_calls_selected_copy version e le m mb Ptrofs.zero ob
    (Ptrofs.repr (object_slot_offset slot)) t le' after out Hname Hm Hobj Hr)
    as (result & Hcall).
  eapply icp_completed_copy_forgets_old_display; eauto.
Qed.

Lemma iar_actual_air_angle_frames : forall version e le m mb ob slot t le' after out,
  (slot < object_pool_capacity)%nat -> Mem.valid_block m ob ->
  e ! IFR._vec3s_set = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iar_air_angle version) t le' after out ->
  forall chunk b offset, Mem.valid_block m b -> igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m mb ob slot t le' after out Hslot Hobject Hlocal Hm Hobj Hrun.
  rewrite (proj1 (proj2 (iar_air_tail_source version))) in Hrun.
  unfold ocn_exec, ClightBigstep.Clight2.exec_stmt in Hrun.
  cce_unroll_loop_free_exec.
  all: match goal with Hr : eval_expr _ _ _ _ ibk_object_read ?v |- _ =>
    assert (v = Vptr ob (Ptrofs.repr (object_slot_offset slot))) by
      (eapply ibcc_actual_object_read; eauto); subst v end.
  all: try contradiction.
  destruct (igr_selected_set_resolves version) as (fb & Hsymbol & Hfun).
  match goal with Hcall : ClightBigstep.exec_stmt _ _ _ _ _ iar_air_angle_call _ _ _ _ |- _ =>
    unfold iar_air_angle_call in Hcall; inversion Hcall; subst; clear Hcall end.
  match goal with Hclass : classify_fun _ = _ |- _ => cbn in Hclass; inversion Hclass; subst end.
  match goal with Hr : eval_expr _ _ _ _ (Evar _ (Tfunction _ _ _)) ?v |- _ =>
    assert (v = Vptr fb Ptrofs.zero) by (eapply sce_function_name_value; eauto); subst v end.
  match goal with Hfind : Genv.find_funct _ (Vptr _ _) = Some ?fd |- _ =>
    change (Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some fd) in Hfind;
    rewrite Hfun in Hfind; inversion Hfind; subst fd end.
  repeat match goal with Ha : eval_exprlist _ _ _ _ _ _ _ |- _ => inversion Ha; subst; clear Ha end.
  pose proof (iar_air_angle_address version e
    (PTree.set IFR._t'7 v (PTree.set IFR._t'6
      (Vptr ob (Ptrofs.repr (object_slot_offset slot))) le)) m2 ob
    (Ptrofs.repr (object_slot_offset slot)) v1
    ltac:(rewrite PTree.gso by discriminate; apply PTree.gss) H6) as Haddress.
  subst v1.
  match goal with Hcast : sem_cast (Vptr ob _) _ _ _ = Some ?v |- _ =>
    change (Some (Vptr ob (Ptrofs.add (Ptrofs.repr (object_slot_offset slot)) (Ptrofs.repr 26))) = Some v)
      in Hcast; inversion Hcast; subst end.
  eapply igr_complete_short_setter_frames_positions; [exact Hslot|exact Hobject|eassumption].
Qed.

Theorem iar_post_refresh_tail_frames_positions : forall version e le m mb ob slot t le' after out,
  (slot < object_pool_capacity)%nat -> Mem.valid_block m ob ->
  e ! IFR._vec3s_set = None -> le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (iaf_tail version) t le' after out ->
  forall chunk b offset, Mem.valid_block m b -> igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk m b offset.
Proof.
  intros version e le m mb ob slot t le' after out Hslot Hobject Hlocal Hm Hobj Hrun.
  destruct (iar_air_tail_source version) as (Hbody & _ & Hnormal & Hreadonly).
  rewrite Hbody in Hrun.
  destruct (ibk_split_sequence _ _ _ _ _ _ _ _ _ _ Hnormal Hrun)
    as (middle & memory & pre & suffix & Htrace & Hangle & Hrest).
  pose proof (proj1 (proj2 (cce_readonly_frame _ _ _ _ _ _ _ _ _ _ Hrest Hreadonly))) as Hsame.
  subst after. eapply iar_actual_air_angle_frames; eauto.
Qed.

Lemma iar_air_entry_has_fresh_local : forall version ge m mb arg e le entry,
  function_entry2 ge (iaf_body version) [Vptr mb Ptrofs.zero;Vint arg] m e le entry ->
  exists local, Mem.alloc m 0 (sizeof ge (tarray tfloat 3)) = (entry,local) /\
    e = PTree.set IFR._intendedPos (local,tarray tfloat 3) empty_env.
Proof.
  intros version ge m mb arg e le entry He.
  destruct (iaf_source_cuts version) as (Hvars & _).
  inversion He; subst; clear He.
  match goal with Ha : alloc_variables _ _ _ _ _ _ |- _ =>
    rewrite Hvars in Ha; inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ => inversion Ha; subst; clear Ha end.
  eexists. split; eauto.
Qed.

Definition InkAirReturnedPositionFrame : Prop :=
  forall version start mb arg e entry_le entry_m refreshed_le refreshed ob slot
      t last_le last_m out after,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat -> Mem.valid_block start ob ->
  function_entry2 ge (iaf_body version) [Vptr mb Ptrofs.zero;Vint arg]
    start e entry_le entry_m ->
  Mem.valid_block refreshed ob ->
  refreshed_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 refreshed mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  ocn_exec ge e refreshed_le refreshed (iaf_tail version) t last_le last_m out ->
  Mem.free_list last_m (blocks_of_env ge e) = Some after ->
  forall chunk b offset, Mem.valid_block start b -> Mem.valid_block refreshed b ->
    igr_outside_angles ob slot chunk b offset ->
    Mem.load chunk after b offset = Mem.load chunk refreshed b offset.

Theorem iar_actual_air_return_keeps_refreshed_positions : InkAirReturnedPositionFrame.
Proof.
  unfold InkAirReturnedPositionFrame. cbn zeta.
  intros version start mb arg e entry_le entry_m refreshed_le refreshed ob slot
    t last_le last_m out after Hslot Hstart Hentry Hvalid Hm Hobject Htail Hfree.
  destruct (iar_air_entry_has_fresh_local _ _ _ _ _ _ _ _ Hentry) as (local & Halloc & ->).
  assert ((PTree.set IFR._intendedPos (local,tarray tfloat 3) empty_env) ! IFR._vec3s_set = None)
    as Hname by (rewrite PTree.gso by discriminate; apply PTree.gempty).
  pose proof (iar_post_refresh_tail_frames_positions version _ refreshed_le refreshed mb ob slot
    t last_le last_m out Hslot Hvalid Hname Hm Hobject Htail) as Hframe.
  change (Mem.free_list last_m [(local,0,12)] = Some after) in Hfree.
  cbn [Mem.free_list] in Hfree.
  destruct (Mem.free last_m local 0 12) as [freed|] eqn:HfreeOne; try discriminate.
  inversion Hfree; subst after.
  intros chunk b offset Hbefore Hnow Houtside.
  assert (b <> local) as Hfresh by (intro; subst; eapply Mem.fresh_block_alloc; eauto).
  erewrite Mem.load_free; [apply Hframe; assumption|exact HfreeOne|left; congruence].
Qed.

(** The read conditions are at the reached copy cut, AFTER the real quarter,
    terrain, gravity and wind executions. They impose no initial display,
    velocity, actor location or floor-success condition. *)
Theorem iar_refresh_and_return_keep_cut_positions :
  forall version start mb arg ob slot height raw e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t last_le last_m out returned,
  let ge := Clight.globalenv (selected_clight_target version) in
  (slot < object_pool_capacity)%nat -> mb <> ob ->
  Mem.valid_block start mb -> Mem.valid_block start ob -> Mem.valid_block cut_m ob ->
  function_entry2 ge (iaf_body version) [Vptr mb Ptrofs.zero;Vint arg]
    start e entry_le entry_m ->
  cut_le ! IFR._m = Some (Vptr mb Ptrofs.zero) ->
  Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
  Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
  Mem.load Mfloat32 cut_m ob (object_slot_offset slot + 164) = Some (Vsingle raw) ->
  ocn_exec ge e cut_le cut_m (iaf_refresh version) copy_t copy_le copy_m Out_normal ->
  ocn_exec ge e copy_le copy_m (iaf_tail version) tail_t last_le last_m out ->
  Mem.free_list last_m (blocks_of_env ge e) = Some returned ->
  Mem.load Mfloat32 returned mb 64 = Some (Vsingle height) /\
  Mem.load Mfloat32 returned ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
  Mem.load Mfloat32 returned ob (object_slot_offset slot + 164) = Some (Vsingle raw).
Proof.
  cbn zeta.
  intros version start mb arg ob slot height raw e entry_le entry_m
    cut_le cut_m copy_t copy_le copy_m tail_t last_le last_m out returned
    Hslot Hsep HstartM HstartO HcutO Hentry Hm Hobj Hy Hraw Hcopy Htail Hfree.
  destruct (iaf_entry_keeps_argument _ _ _ _ _ _ _ _ Hentry) as [_ Hname].
  destruct (iar_air_refresh_completes_without_old_display version e cut_le cut_m
    mb ob slot height copy_t copy_le copy_m Out_normal Hslot Hsep HcutO Hname
    Hm Hobj Hy Hcopy) as [Hdisplay HcopyFrame].
  assert (Mem.load Mfloat32 copy_m mb 64 = Some (Vsingle height)) as HcopiedM.
  { rewrite HcopyFrame; [exact Hy|eapply ibcc_loaded_block_valid; eauto|
      unfold icp_outside_display; left; exact Hsep]. }
  assert (Mem.load Mfloat32 copy_m ob (object_slot_offset slot + 164) = Some (Vsingle raw))
    as HcopiedRaw.
  { rewrite HcopyFrame; [exact Hraw|exact HcutO|
      unfold icp_outside_display; right; right; cbn; lia]. }
  assert (Mem.load Mint32 copy_m mb 136 = Some
    (Vptr ob (Ptrofs.repr (object_slot_offset slot)))) as HcopiedObject.
  { rewrite HcopyFrame; [exact Hobj|eapply ibcc_loaded_block_valid; eauto|
      unfold icp_outside_display; left; exact Hsep]. }
  assert (copy_le ! IFR._m = Some (Vptr mb Ptrofs.zero)) as HcopyM.
  { rewrite (cce_argument_temporary_is_preserved _ _ _ _ _ _ _ _ _ IFR._m Hcopy
      ltac:(destruct version; reflexivity)). exact Hm. }
  assert (Mem.valid_block copy_m ob) as HcopyO by (eapply ibcc_loaded_block_valid; eauto).
  assert (Mem.valid_block copy_m mb) as HcopyState by (eapply ibcc_loaded_block_valid; eauto).
  pose proof (iar_actual_air_return_keeps_refreshed_positions version start mb arg e
    entry_le entry_m copy_le copy_m ob slot tail_t last_le last_m out returned
    Hslot HstartO Hentry HcopyO HcopyM HcopiedObject Htail Hfree) as HreturnFrame.
  repeat split.
  - rewrite HreturnFrame; [exact HcopiedM|exact HstartM|exact HcopyState|
      unfold igr_outside_angles; left; exact Hsep].
  - rewrite HreturnFrame; [exact Hdisplay|exact HstartO|exact HcopyO|
      unfold igr_outside_angles; right; right; cbn; lia].
  - rewrite HreturnFrame; [exact HcopiedRaw|exact HstartO|exact HcopyO|
      unfold igr_outside_angles; right; right; cbn; lia].
Qed.

Definition InkAirCompletedCallPositions : Prop :=
  forall version start mb arg t returned result,
  let ge := Clight.globalenv (selected_clight_target version) in
  Mem.valid_block start mb ->
  ClightBigstep.Clight2.eval_funcall ge start (Internal (iaf_body version))
    [Vptr mb Ptrofs.zero;Vint arg] t returned result ->
  exists e entry_le entry_m cut_le cut_m copy_le copy_m last_le last_m pre copy_t suffix out,
    t = pre ++ (copy_t ++ suffix) /\
    function_entry2 ge (iaf_body version) [Vptr mb Ptrofs.zero;Vint arg]
      start e entry_le entry_m /\
    ocn_exec ge e entry_le entry_m (iaf_prefix version) pre cut_le cut_m Out_normal /\
    ocn_exec ge e cut_le cut_m (iaf_refresh version) copy_t copy_le copy_m Out_normal /\
    ocn_exec ge e copy_le copy_m (iaf_tail version) suffix last_le last_m out /\
    outcome_result_value out (fn_return (iaf_body version)) result last_m /\
    Mem.free_list last_m (blocks_of_env ge e) = Some returned /\
    (forall ob slot height raw, (slot < object_pool_capacity)%nat -> mb <> ob ->
      Mem.valid_block start ob -> Mem.valid_block cut_m ob ->
      Mem.load Mint32 cut_m mb 136 = Some (Vptr ob (Ptrofs.repr (object_slot_offset slot))) ->
      Mem.load Mfloat32 cut_m mb 64 = Some (Vsingle height) ->
      Mem.load Mfloat32 cut_m ob (object_slot_offset slot + 164) = Some (Vsingle raw) ->
      Mem.load Mfloat32 returned mb 64 = Some (Vsingle height) /\
      Mem.load Mfloat32 returned ob (object_slot_offset slot + 36) = Some (Vsingle height) /\
      Mem.load Mfloat32 returned ob (object_slot_offset slot + 164) = Some (Vsingle raw)).

Theorem iar_completed_air_call_forgets_display_gap : InkAirCompletedCallPositions.
Proof.
  unfold InkAirCompletedCallPositions. cbn zeta.
  intros version start mb arg t returned result Hvalid Hcall.
  destruct (iaf_completed_air_call_reaches_display_refresh version start mb Ptrofs.zero
    arg t returned result Hcall)
    as (e & entry_le & entry_m & cut_le & cut_m & copy_le & copy_m & last_le & last_m &
      pre & copy_t & suffix & out & Htrace & Hentry & Hprefix & Hm & Hname & Hcopy &
      Htail & Hresult & Hfree & Hcallee).
  exists e, entry_le, entry_m, cut_le, cut_m, copy_le, copy_m, last_le, last_m,
    pre, copy_t, suffix, out.
  repeat match goal with |- _ /\ _ => split; [assumption|] end.
  intros ob slot height raw Hslot Hsep HstartO HcutO Hobj Hy Hraw.
  eapply iar_refresh_and_return_keep_cut_positions; eauto.
Qed.

Definition InkAirRefreshBoundary : Prop :=
  InkAirCallRefreshCut /\ InkAirRefreshCompleted /\
  InkAirReturnedPositionFrame /\ InkAirCompletedCallPositions.

Theorem iar_air_refresh_boundary_checked : InkAirRefreshBoundary.
Proof.
  split; [exact iaf_completed_air_call_reaches_display_refresh|].
  split; [exact iar_air_refresh_completes_without_old_display|].
  split; [exact iar_actual_air_return_keeps_refreshed_positions|].
  exact iar_completed_air_call_forgets_display_gap.
Qed.

