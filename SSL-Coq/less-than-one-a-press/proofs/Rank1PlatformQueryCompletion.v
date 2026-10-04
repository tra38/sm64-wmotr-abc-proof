(** Full-call clearing, including real find_floor effects and local frees.
    The selected floor is not prescribed. If its returned finite height is
    high, a low raw query clears both pointers even if the owner is stale. *)
From Coq Require Import List ZArith Reals.
From Flocq Require Import Binary.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_object_list_processor.
From LessThanOneAPress.Proofs Require Import GameTypes Rank1CaptureGeometry
  Rank1FinalPlatformQuery InkPlatformDistance InkPlatformSource
  InkPlatformWriteFrame InkFloorCallEffects InkFloorListEffects InkCopyCaller
  InkCopyCompletion ObjectContactNecessity UpperElevatorQueryResolution SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

Lemma r1qc_variables : forall version,
  fn_vars (ipd_body version IPDUpdate) =
    [(IPD._floor, ipd_surface); (IPD._filler, tarray tuchar 4)].
Proof. intros []; reflexivity. Qed.

Lemma r1qc_allocated_floor : forall version ge m e allocated,
  alloc_variables ge empty_env m (fn_vars (ipd_body version IPDUpdate)) e allocated ->
  exists fb, e ! IPD._floor = Some (fb, ipd_surface).
Proof.
  intros version ge m e allocated Halloc.
  rewrite r1qc_variables in Halloc. inversion Halloc; subst; clear Halloc.
  match goal with Ha : alloc_variables _ _ _ (_ :: _) _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  match goal with Ha : alloc_variables _ _ _ [] _ _ |- _ =>
    inversion Ha; subst; clear Ha end.
  eexists. rewrite PTree.gso by discriminate. apply PTree.gss.
Qed.

Definition Rank1LowQueryCallClearing : Prop :=
  forall version m pb gb ob oo values t after result,
  let ge := Clight.globalenv (selected_clight_target version) in
  Genv.find_symbol ge IPD._gMarioPlatform = Some pb ->
  Genv.find_symbol ge IPD._gMarioObject = Some gb ->
  Genv.find_symbol ge us_object_list_processor._gObjectPool = Some ob ->
  Mem.valid_block m pb ->
  Mem.load Mptr m gb 0 = Some (Vptr ob oo) ->
  (forall axis, Mem.load Mfloat32 m ob
    (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (160 + 4 * icp_number axis)))) =
    Some (Vsingle (values axis))) ->
  is_finite 24 128 (values ICPY) = true -> (B2R 24 128 (values ICPY) <= 818)%R ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal (ipd_body version IPDUpdate))
    [] t after result ->
  exists allocated fb query_m floor_result query_trace,
    ClightBigstep.Clight2.eval_funcall ge allocated
      (Internal (ueqr_native_body version UEQRFindFloor))
      [Vsingle (values ICPX); Vsingle (values ICPY); Vsingle (values ICPZ); Vptr fb Ptrofs.zero]
      query_trace query_m floor_result /\
    (forall height, floor_result = Vsingle height ->
      is_finite 24 128 height = true -> (1281 <= B2R 24 128 height)%R ->
      t = E0 /\
      Mem.load Mptr after pb 0 = Some (Vint Int.zero) /\
      Mem.load Mptr after ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532))) =
        Some (Vint Int.zero)).

Theorem r1qc_completed_low_query_call_clears_both : Rank1LowQueryCallClearing.
Proof.
  unfold Rank1LowQueryCallClearing.
  intros version m pb gb ob oo values t after result. cbn zeta.
  intros Hps Hgs Hos Hpv Hobject Hvalues Fy Hy Hcall.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ Hobject) as Hgv.
  pose proof (ibcc_loaded_block_valid _ _ _ _ _ (Hvalues ICPY)) as Hov.
  assert (pb <> ob) as Hpo by (eapply Genv.global_addresses_distinct; eauto; discriminate).
  inversion Hcall; subst.
  match goal with Hentry : function_entry2 _ _ _ _ _ _ _ |- _ =>
    inversion Hentry; subst; clear Hentry end.
  match goal with Ha : alloc_variables ?ge empty_env _ _ ?e ?allocated |- _ =>
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha ob Hov
      ltac:(intros id b ty Hread; rewrite PTree.gempty in Hread; discriminate))
      as (HlocalsObject & HallocObject & _);
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha gb Hgv
      ltac:(intros id b ty Hread; rewrite PTree.gempty in Hread; discriminate))
      as (HlocalsGlobal & HallocGlobal & Houtside);
    destruct (ipw_alloc_frame _ _ _ _ _ _ Ha pb Hpv
      ltac:(intros id b ty Hread; rewrite PTree.gempty in Hread; discriminate))
      as (HlocalsPlatform & _ & _);
    destruct (r1qc_allocated_floor _ _ _ _ _ Ha) as [fb Hfloor];
    assert (e ! IPD._gMarioObject = None) as Hml by
      (rewrite Houtside; [apply PTree.gempty|rewrite r1qc_variables; cbn; intuition discriminate]);
    assert (e ! IPD._find_floor = None) as Hfind by
      (rewrite Houtside; [apply PTree.gempty|rewrite r1qc_variables; cbn; intuition discriminate]);
    assert (e ! ipdist_abs_id = None) as Habs by
      (rewrite Houtside; [apply PTree.gempty|rewrite r1qc_variables; cbn; intuition discriminate]);
    assert (e ! IPD._gMarioPlatform = None) as Hpl by
      (rewrite Houtside; [apply PTree.gempty|rewrite r1qc_variables; cbn; intuition discriminate]);
    assert (Mem.load Mptr allocated gb 0 = Some (Vptr ob oo)) as HentryObject
      by (rewrite HallocGlobal; exact Hobject);
    assert (forall axis, Mem.load Mfloat32 allocated ob
      (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr (160 + 4 * icp_number axis)))) =
      Some (Vsingle (values axis))) as HentryValues
      by (intros axis; rewrite HallocObject; apply Hvalues)
  end.
  match goal with Hrun : ClightBigstep.exec_stmt _ _ _ _ _ (fn_body _) _ _ _ _ |- _ =>
    pose proof (r1q_nonnull_body_reaches_segment _ _ _ _ _ _ _ _ _ _ _
      Hml Hgs HentryObject Hrun) as Hsegment end.
  destruct (r1q_final_query_uses_raw_position _ _ _ _ _ _ _ _ _ _ _ _ _
    Hml Hfind Hfloor Hgs HentryObject HentryValues Hsegment)
    as (query_trace & tail_trace & query_m & floor_result & Htrace & Hquery & Htail).
  lazymatch type of Hquery with ClightBigstep.Clight2.eval_funcall _ ?allocated _ _ _ _ _ =>
    exists allocated, fb, query_m, floor_result, query_trace end.
  split; [exact Hquery|].
  intros height Hresult Fh Hh. subst floor_result.
  lazymatch type of Hquery with ClightBigstep.Clight2.eval_funcall _ ?allocated _ _ _ _ _ =>
  destruct (ifc_completed_floor_preserves_other_cells version allocated
    (Vsingle (values ICPX)) (Vsingle (values ICPY)) (Vsingle (values ICPZ))
    fb Ptrofs.zero query_trace query_m (Vsingle height) Mptr gb 0
    (ibcc_loaded_block_valid _ _ _ _ _ HentryObject)
    ltac:(intros id Hin Hsame;
      assert (IPD._gMarioObject <> id) as Hids by
        (destruct Hin as [<-|[<-|[<-|[]]]]; discriminate);
      assert (gb <> gb) as Hbad by (eapply Genv.global_addresses_distinct; eauto);
      exact (Hbad eq_refl))
    ltac:(left; intro E; exact ((HlocalsGlobal _ _ _ Hfloor) (eq_sym E)))
    Hquery) as [HqueryTrace HglobalFrame]
  end.
  assert (Mem.load Mptr query_m gb 0 = Some (Vptr ob oo)) as HqueriedObject
    by (rewrite HglobalFrame; exact HentryObject).
  lazymatch type of Htail with ocn_exec _ ?locals ?temps _ _ _ ?last_temps ?last_m ?last_out =>
  destruct (ipdist_failed_distance_clears_support version locals temps query_m
    (values ICPY) height pb gb ob oo tail_trace last_temps last_m last_out
    Habs ltac:(unfold r1q_temps; repeat rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(apply PTree.gss) (r1cg_low_raw_cannot_capture_high_floor _ _ Fy Fh Hy Hh)
    Hpl Hml Hps Hgs Hpo HqueriedObject Htail)
    as (HtailTrace & _ & Hplatform & HobjectPlatform & _)
  end.
  split; [rewrite Htrace, HqueryTrace, HtailTrace; reflexivity|].
  split.
  - lazymatch goal with Hfree : Mem.free_list ?last (blocks_of_env ?ge ?e) = Some after |- _ =>
      rewrite (ifc_free_list_frame (blocks_of_env ge e) last after Mptr pb 0
        ltac:(apply Forall_forall; intros [[target lo] hi] Hin;
          unfold blocks_of_env in Hin; apply in_map_iff in Hin;
          destruct Hin as [[id [b ty]] [E Hbinding]];
          cbn [block_of_binding] in E; inversion E; subst;
          eapply HlocalsPlatform; eapply PTree.elements_complete; exact Hbinding) Hfree)
    end. exact Hplatform.
  - lazymatch goal with Hfree : Mem.free_list ?last (blocks_of_env ?ge ?e) = Some after |- _ =>
      rewrite (ifc_free_list_frame (blocks_of_env ge e) last after Mptr ob
        (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 532)))
        ltac:(apply Forall_forall; intros [[target lo] hi] Hin;
          unfold blocks_of_env in Hin; apply in_map_iff in Hin;
          destruct Hin as [[id [b ty]] [E Hbinding]];
          cbn [block_of_binding] in E; inversion E; subst;
          eapply HlocalsObject; eapply PTree.elements_complete; exact Hbinding) Hfree)
    end. exact HobjectPlatform.
Qed.
