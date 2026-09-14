(** The elevator underside cannot act as an exposed ceiling at the ordinary
    base-relative query. Execute the real list-loop rejection guard, with
    explicit one-unit bounds on the query and the loaded underside height.
    The live loader, list traversal and caller's query projection are NOT
    assumed proved by this theorem. *)
From Coq Require Import Bool Lia List Reals Lra ZArith.
From Flocq Require Import Binary Core.
From compcert Require Import AST Clight ClightBigstep Clightdefs Cop Ctypes
  Events Floats Globalenvs IEEE754_extra Integers Maps Memory Values.
From LessThanOneAPress.Generated Require Import us_surface_collision jp_surface_collision.
From LessThanOneAPress.Proofs Require Import GameTypes Area2Rank9ACoinFlight
  Area2Rank12BContact ObjectContactNecessity UpperElevatorQueryResolution
  CleanedClightPrograms ClightLinkExecution GlobalInterfaceStructural
  JPSourceSymbolTransport JPWarpLevelEntryResolution LinkedClightPrograms
  NormalizedClightPrograms SelectedClightTarget SuccessfulMakeProgramResolution
  USViewportRepairedNamesNorepet USViewportRepairedProgramSelection
  USWarpLevelRepairReceipt USWarpLevelSourceUnionReceipt USWholeASTTagRepair.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Float32.cmp Float32.compare.
Module CR := us_surface_collision.

Definition rank10c_body version := match version with
| VersionUS => us_surface_collision.f_find_ceil_from_list
| VersionJP => jp_surface_collision.f_find_ceil_from_list end.
Lemma rank10c_us_source :
  nth_error CR.global_definitions
    (ueqr_definition_index CR._find_ceil_from_list CR.global_definitions) =
  Some (CR._find_ceil_from_list, Gfun (Internal (rank10c_body VersionUS))).
Proof. vm_compute; reflexivity. Qed.
Lemma rank10c_us_member :
  In (CR._find_ceil_from_list, Gfun (Internal (rank10c_body VersionUS)))
    (unit_global_definitions us_units).
Proof.
  eapply source_unit_definition_enters_source_union with (unit := us_nlist_at 31 us_units).
  - exact (us_nlist_at_nIn _ 31 us_units).
  - eapply nth_error_In. exact rank10c_us_source.
Qed.
Lemma rank10c_us_selection :
  us_normalized_global_definition_map ! CR._find_ceil_from_list =
    Some (Gfun (Internal (rank10c_body VersionUS))).
Proof.
  eapply (checked_internal_selection_is_exact
    (unit_global_definitions us_units) us_normalized_global_definition_map).
  - exact us_internal_identifiers_are_unique_checked.
  - exact us_all_internal_identifiers_selected_checked.
  - exact (normalized_definition_map_has_source_provenance (unit_global_definitions us_units)).
  - exact rank10c_us_member.
Qed.
Lemma rank10c_us_no_repair : us_selected_definition_needs_viewport_repair
  (CR._find_ceil_from_list, Gfun (Internal (rank10c_body VersionUS))) = false.
Proof. vm_compute; reflexivity. Qed.
Local Opaque normalize_global_definition_map.
Lemma rank10c_us_selected_member :
  In (CR._find_ceil_from_list, Gfun (Internal (rank10c_body VersionUS)))
    us_viewport_repaired_global_definitions.
Proof.
  unfold us_viewport_repaired_global_definitions. apply fixed_point_enters_mapped_list.
  - unfold repair_us_selected_global_definition. rewrite rank10c_us_no_repair. reflexivity.
  - apply every_selected_internal_body_is_preserved_verbatim. exact rank10c_us_selection.
Qed.
Lemma rank10c_jp_source :
  (prog_defmap (nlist_at 31 jp_cleaned_units)) ! CR._find_ceil_from_list =
    Some (Gfun (Internal (rank10c_body VersionJP))).
Proof. vm_compute; reflexivity. Qed.
Theorem rank10c_selected_ceiling_list_body_resolves : forall version, exists b,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) CR._find_ceil_from_list = Some b /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
    Some (Internal (rank10c_body version)).
Proof.
  intros [].
  - eapply program_definitions_resolve_internal_globalenv.
    + exact us_viewport_repaired_program_definitions_checked.
    + exact us_viewport_repaired_definition_names_norepet.
    + exact rank10c_us_selected_member.
  - eapply (official_link_resolves_internal_globalenv jp_cleaned_units
      jp_official_cleaned_slice jp_cleaned_units_official_link (nlist_at 31 jp_cleaned_units)).
    + exact (nlist_at_nIn _ 31 jp_cleaned_units).
    + exact rank10c_jp_source.
Qed.

Definition rank10c_negative_78 :=
  Float32.neg (Float32.of_bits (Int.repr 1117519872)).
Definition rank10c_difference j ceiling :=
  Float32.sub (rank9cf_integer j) (Float32.sub ceiling rank10c_negative_78).
Definition rank10c_rejected j ceiling :=
  Float32.cmp Cgt (rank10c_difference j ceiling) (Float32.of_bits (Int.repr 0)).
Definition rank10c_test := Ebinop Ogt
  (Ebinop Osub (Etempvar CR._y tint)
    (Ebinop Osub (Etempvar CR._height tfloat)
      (Eunop Oneg (Econst_single (Float32.of_bits (Int.repr 1117519872)) tfloat) tfloat)
      tfloat) tfloat)
  (Econst_single (Float32.of_bits (Int.repr 0)) tfloat) tint.
Fixpoint rank10c_find_test (s : statement) : option statement := match s with
| Sifthenelse (Ebinop Ogt (Ebinop Osub (Etempvar id _) _ _) (Econst_single _ _) _) Scontinue Sskip =>
    if Pos.eqb id CR._y then Some s else None
| Ssequence a b | Sloop a b | Sifthenelse _ a b =>
    match rank10c_find_test a with Some found => Some found | None => rank10c_find_test b end
| _ => None end.
Definition rank10c_guard version := match rank10c_find_test (fn_body (rank10c_body version)) with
| Some s => s | None => Sskip end.
Theorem rank10c_rejection_is_generated : forall version,
  rank10c_find_test (fn_body (rank10c_body version)) =
    Some (Sifthenelse rank10c_test Scontinue Sskip) /\
  rank10c_guard version = Sifthenelse rank10c_test Scontinue Sskip.
Proof. intros []; split; reflexivity. Qed.

Theorem rank10c_underside_is_rejected : forall base j ceiling,
  0 <= base <= 5000 -> base+79 <= j <= base+81 ->
  rank9cf_finite ceiling ->
  (IZR (base-51) <= rank9cf_real ceiling <= IZR (base-49))%R ->
  rank10c_rejected j ceiling = true.
Proof.
  intros base j ceiling Hb Hj Fc Hc.
  assert (H78 : rank10c_negative_78 = rank9cf_integer (-78))
    by (apply rank9cf_bits_injective; vm_compute; reflexivity).
  assert (Hz : Float32.of_bits (Int.repr 0) = rank9cf_integer 0)
    by (apply rank9cf_bits_injective; vm_compute; reflexivity).
  destruct (rank9cf_integer_exact (-78) ltac:(lia)) as [R78 F78].
  destruct (rank9cf_integer_exact 0 ltac:(lia)) as [R0 F0].
  destruct (rank9cf_integer_exact j ltac:(lia)) as [Rj Fj].
  destruct (rank12b_sub_range ceiling (rank9cf_integer (-78)) (base+27) (base+29)
    Fc F78 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R78; repeat rewrite plus_IZR; repeat rewrite minus_IZR in Hc; lra)) as [Fb Hbuffer].
  assert (Hjreal : (IZR (base+79) <= IZR j <= IZR (base+81))%R)
    by (split; apply IZR_le; lia).
  destruct (rank12b_sub_range (rank9cf_integer j)
    (Float32.sub ceiling (rank9cf_integer (-78))) 50 54
    Fj Fb ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Rj; repeat rewrite plus_IZR in Hbuffer, Hjreal; lra)) as [Fd Hd].
  assert (Hpositive : (rank9cf_real (rank9cf_integer 0) < rank9cf_real
    (Float32.sub (rank9cf_integer j) (Float32.sub ceiling (rank9cf_integer (-78)))))%R)
    by (rewrite R0; lra).
  unfold rank10c_rejected, rank10c_difference. rewrite H78, Hz.
  unfold Float32.cmp, Float32.compare.
  rewrite Bcompare_correct by assumption. rewrite Rcompare_Gt by exact Hpositive. reflexivity.
Qed.

Lemma rank10c_test_value : forall ge e le m j ceiling,
  le ! CR._y = Some (Vint (Int.repr j)) ->
  le ! CR._height = Some (Vsingle ceiling) ->
  eval_expr ge e le m rank10c_test (Val.of_bool (rank10c_rejected j ceiling)).
Proof.
  intros ge e le m j ceiling Hy Hheight. unfold rank10c_test.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + apply eval_Etempvar. exact Hy.
    + eapply eval_Ebinop.
      * apply eval_Etempvar. exact Hheight.
      * eapply eval_Eunop; [constructor|reflexivity].
      * reflexivity.
    + reflexivity.
  - constructor.
  - reflexivity.
Qed.

Definition Rank10CUndersideRejection : Prop :=
  forall version e le m base j ceiling,
  0 <= base <= 5000 -> base+79 <= j <= base+81 ->
  rank9cf_finite ceiling ->
  (IZR (base-51) <= rank9cf_real ceiling <= IZR (base-49))%R ->
  le ! CR._y = Some (Vint (Int.repr j)) ->
  le ! CR._height = Some (Vsingle ceiling) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    (rank10c_guard version) E0 le m Out_continue.
Theorem rank10c_actual_query_skips_underside : Rank10CUndersideRejection.
Proof.
  unfold Rank10CUndersideRejection.
  intros version e le m base j ceiling Hb Hj Fc Hc Hy Hheight.
  rewrite (proj2 (rank10c_rejection_is_generated version)).
  pose proof (rank10c_test_value (Clight.globalenv (selected_clight_target version))
    e le m j ceiling Hy Hheight) as Htest.
  rewrite (rank10c_underside_is_rejected base j ceiling Hb Hj Fc Hc) in Htest.
  eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
  - exact Htest.
  - reflexivity.
  - constructor.
Qed.

Definition Rank10ACeilingRejectionBoundary : Prop :=
  (forall version, exists b,
    Genv.find_symbol (Clight.globalenv (selected_clight_target version)) CR._find_ceil_from_list = Some b /\
    Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) b =
      Some (Internal (rank10c_body version))) /\
  (forall version, rank10c_find_test (fn_body (rank10c_body version)) =
    Some (Sifthenelse rank10c_test Scontinue Sskip)) /\
  Rank10CUndersideRejection.
Theorem rank10c_ceiling_rejection_boundary_checked : Rank10ACeilingRejectionBoundary.
Proof.
  split; [exact rank10c_selected_ceiling_list_body_resolves|].
  split; [intro version; exact (proj1 (rank10c_rejection_is_generated version))|].
  exact rank10c_actual_query_skips_underside.
Qed.
