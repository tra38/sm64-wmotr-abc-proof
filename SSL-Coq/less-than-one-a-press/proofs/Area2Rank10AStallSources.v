(** Rank 10A stall producers: exclude static geometry throughout the wall
    query corridor, and execute the real time-stop clearing guard. A stopped
    loader during time stop does NOT imply that its earlier floor was erased.

    These are a finite complete source-mesh certificate and a conditional
    selected-Clight body execution. Dynamic-list production, object scheduling
    and a controller-preserved interior remain distinct obligations. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_surface_load jp_surface_load.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank12BContact
  Area2Rank10ASupportChange ObjectContactNecessity UpperElevatorQueryResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Module SS := us_surface_load.

(** The strict query interior, enlarged horizontally by radius 50. Y includes
    bases 128..4966, gaps 0..110, offsets -10..60, and five extra units for the
    source surface's lowerY/upperY padding. No orientation filter is needed. *)
Definition rank10t_meets vertices := let '(a,b,c) := vertices in
  rank12b_axis_meets (SD.x_of a) (SD.x_of b) (SD.x_of c) (-509) 510 &&
  rank12b_axis_meets (SD.y_of a) (SD.y_of b) (SD.y_of c) 113 5141 &&
  rank12b_axis_meets (SD.z_of a) (SD.z_of b) (SD.z_of c) (-253) 766.
Definition rank10t_candidates version := filter (fun face =>
  match snd face with Some vertices => rank10t_meets vertices | None => false end)
  (rank12b_faces version).
Theorem rank10t_static_corridor_certificate : forall version,
  rank10t_candidates version = [].
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem rank10t_no_static_triangle_in_corridor : forall version ordinal vertices x y z,
  In (ordinal, Some vertices) (rank12b_faces version) ->
  rank12b_point_in_vertex_box (x,y,z) vertices ->
  (-509 <= x <= 510)%R -> (113 <= y <= 5141)%R ->
  (-253 <= z <= 766)%R -> False.
Proof.
  intros version ordinal vertices x y z Hin Hbox Hx Hy Hz.
  assert (Hcandidate : In (ordinal, Some vertices) (rank10t_candidates version)).
  { apply filter_In. split; [exact Hin|]. cbn [snd].
    unfold rank10t_meets. destruct vertices as [[a b] c].
    unfold rank12b_point_in_vertex_box in Hbox.
    destruct Hbox as [Bx [By Bz]]. repeat rewrite andb_true_iff.
    repeat split; eapply rank12b_axis_meets_sound; eauto. }
  rewrite rank10t_static_corridor_certificate in Hcandidate. contradiction.
Qed.

(** This arithmetical connection is explicit: the census is not just an
    unrelated empty box. Any proposed wall point within these componentwise
    bounds of a query lies in that box. Actual wall-list acceptance still
    needs to be connected to such a point; this is NOT assumed here. *)
Theorem rank10t_static_wall_point_excluded : forall version ordinal vertices
  base gap offset qx qz px py pz,
  In (ordinal, Some vertices) (rank12b_faces version) ->
  rank12b_point_in_vertex_box (px,py,pz) vertices ->
  (128 <= base <= 4966)%R -> (0 <= gap <= 110)%R ->
  (-10 <= offset <= 60)%R -> (-459 <= qx <= 460)%R -> (-203 <= qz <= 716)%R ->
  (qx-50 <= px <= qx+50)%R -> (qz-50 <= pz <= qz+50)%R ->
  (base+gap+offset-5 <= py <= base+gap+offset+5)%R -> False.
Proof.
  intros. eapply rank10t_no_static_triangle_in_corridor; eauto; lra.
Qed.

Definition rank10t_clear_body version := match version with
| VersionUS => us_surface_load.f_clear_dynamic_surfaces
| VersionJP => jp_surface_load.f_clear_dynamic_surfaces end.
Lemma rank10t_us_source :
  nth_error SS.global_definitions
    (ueqr_definition_index SS._clear_dynamic_surfaces SS.global_definitions) =
  Some (SS._clear_dynamic_surfaces, Gfun (Internal (rank10t_clear_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma rank10t_us_member :
  In (SS._clear_dynamic_surfaces, Gfun (Internal (rank10t_clear_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 32 us_units).
  - exact (us_nlist_at_nIn _ 32 us_units).
  - eapply nth_error_In. exact rank10t_us_source.
Qed.
Lemma rank10t_us_selection :
  us_normalized_global_definition_map ! SS._clear_dynamic_surfaces =
    Some (Gfun (Internal (rank10t_clear_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact rank10t_us_member.
Qed.
Lemma rank10t_us_no_repair : us_selected_definition_needs_viewport_repair
  (SS._clear_dynamic_surfaces, Gfun (Internal (rank10t_clear_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma rank10t_us_selected_member :
  In (SS._clear_dynamic_surfaces, Gfun (Internal (rank10t_clear_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite rank10t_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact rank10t_us_selection.
Qed.
Lemma rank10t_jp_source :
  (prog_defmap (nlist_at 32 jp_cleaned_units)) ! SS._clear_dynamic_surfaces =
    Some (Gfun (Internal (rank10t_clear_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem rank10t_selected_clear_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SS._clear_dynamic_surfaces = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (rank10t_clear_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact rank10t_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 32 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 32 jp_cleaned_units).
    + exact rank10t_jp_source.
Qed.

Definition rank10t_time_test := Eunop Onotbool
  (Ebinop Oand (Etempvar SS._t'1 tuint)
    (Ebinop Oshl (Econst_int (Int.repr 1) tint)
      (Econst_int (Int.repr 6) tint) tint) tuint) tint.
Definition rank10t_clear_taken := match fn_body (rank10t_clear_body VersionUS) with
| Ssequence _ (Sifthenelse _ yes _) => yes | _ => Sskip end.
Lemma rank10t_clear_source : forall version,
  fn_body (rank10t_clear_body version) = Ssequence
    (Sset SS._t'1 (Evar SS._gTimeStopState tuint))
    (Sifthenelse rank10t_time_test rank10t_clear_taken Sskip).
Proof. intros []; reflexivity. Qed.

Lemma rank10t_time_test_false : forall ge e le m state,
  le ! SS._t'1 = Some (Vint state) ->
  Int.eq (Int.and state (Int.repr 64)) Int.zero = false ->
  eval_expr ge e le m rank10t_time_test (Vint Int.zero).
Proof.
  intros ge e le m state Hstate Hactive. unfold rank10t_time_test.
  eapply eval_Eunop.
  - eapply eval_Ebinop.
    + apply eval_Etempvar. exact Hstate.
    + eapply eval_Ebinop; [constructor|constructor|reflexivity].
    + reflexivity.
  - cbn.
    assert (Hshift : Int.shl (Int.repr 1) (Int.repr 6) = Int.repr 64)
      by (vm_compute; reflexivity).
    rewrite Hshift, Hactive. reflexivity.
Qed.

Definition Rank10TTimeStopPreservesCollisionMemory : Prop :=
  forall version e le m time_block state,
  e ! SS._gTimeStopState = None ->
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SS._gTimeStopState = Some time_block ->
  Mem.load Mint32 m time_block 0 = Some (Vint state) ->
  Int.eq (Int.and state (Int.repr 64)) Int.zero = false ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (fn_body (rank10t_clear_body version)) E0
    (PTree.set SS._t'1 (Vint state) le) m Out_normal.
Theorem rank10t_time_stop_does_not_erase_collision : Rank10TTimeStopPreservesCollisionMemory.
Proof.
  unfold Rank10TTimeStopPreservesCollisionMemory.
  intros version e le m time_block state Hlocal Hsymbol Hload Hactive.
  rewrite rank10t_clear_source.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - apply exec_Sset. eapply eval_Elvalue with (ofs := Ptrofs.zero) (bf := Full).
    + apply eval_Evar_global; [exact Hlocal|exact Hsymbol].
    + eapply deref_loc_value with (chunk := Mint32); [reflexivity|exact Hload].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply rank10t_time_test_false; [apply PTree.gss|exact Hactive].
    + reflexivity.
    + constructor.
Qed.

Definition Rank10AStallSourcesBoundary : Prop :=
  (forall version, rank10t_candidates version = []) /\
  (forall version ordinal vertices x y z,
    In (ordinal, Some vertices) (rank12b_faces version) ->
    rank12b_point_in_vertex_box (x,y,z) vertices ->
    (-509 <= x <= 510)%R -> (113 <= y <= 5141)%R ->
    (-253 <= z <= 766)%R -> False) /\
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) SS._clear_dynamic_surfaces = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (rank10t_clear_body version))) /\
  Rank10TTimeStopPreservesCollisionMemory.
Theorem rank10t_stall_sources_boundary_checked : Rank10AStallSourcesBoundary.
Proof.
  split; [exact rank10t_static_corridor_certificate|].
  split; [exact rank10t_no_static_triangle_in_corridor|].
  split; [exact rank10t_selected_clear_body_resolves|].
  exact rank10t_time_stop_does_not_erase_collision.
Qed.
