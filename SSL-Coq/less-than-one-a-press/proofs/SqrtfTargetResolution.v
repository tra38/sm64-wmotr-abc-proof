(** Exact sqrtf declaration resolution in both selected generated programs.
    The computations scan only declarations at this identifier, not the
    large linked global environment or the whole program's execution. *)
From Coq Require Import List.
From compcert Require Import AST Clight Coqlib Ctypes Globalenvs Maps.
From LessThanOneAPress.Proofs Require Import SqrtfClightBinding
  Area2TripletSpawner GameTypes SelectedClightTarget
  LinkedClightPrograms NormalizedClightPrograms CleanedClightPrograms
  ClightGlobalMemoryRefinement ClightLinkExecution JPSourceSymbolTransport
  JPWarpLevelEntryResolution
  USWholeASTTagRepair USWarpLevelRepairReceipt
  USViewportRepairedProgramSelection USViewportRepairedNamesNorepet.
Import ListNotations.
Local Opaque us_viewport_repaired_program jp_official_cleaned_slice.

Lemma sbr_us_selection :
  us_normalized_global_definition_map ! TD._sqrtf = Some (Gfun sb_declaration).
Proof.
  unfold us_normalized_global_definition_map.
  rewrite normalized_global_definition_map_get_scan.
  vm_compute; reflexivity.
Qed.

Definition sbr_at_name definitions :=
  filter (fun entry : ident * globdef Clight.fundef type =>
    Pos.eqb (fst entry) TD._sqrtf) definitions.
Lemma sbr_jp_source_declarations :
  sbr_at_name (unit_global_definitions jp_units) =
  repeat (TD._sqrtf, Gfun sb_declaration)
    (length (sbr_at_name (unit_global_definitions jp_units))).
Proof. vm_compute; reflexivity. Qed.

Lemma sbr_jp_source_exact : forall definition,
  In (TD._sqrtf, definition) (unit_global_definitions jp_units) ->
  definition = Gfun sb_declaration.
Proof.
  intros definition Hin.
  assert (In (TD._sqrtf, definition)
    (sbr_at_name (unit_global_definitions jp_units))) as Hfiltered.
  { apply filter_In. split; [exact Hin|apply Pos.eqb_refl]. }
  rewrite sbr_jp_source_declarations in Hfiltered.
  apply repeat_spec in Hfiltered. inversion Hfiltered; reflexivity.
Qed.

Lemma sbr_jp_symbol : exists fb,
  Genv.find_symbol (Clight.globalenv jp_official_cleaned_slice) TD._sqrtf = Some fb.
Proof.
  eapply jp_source_definition_has_official_symbol with (unit := nlist_at 19 jp_units)
    (definition := Gfun sb_declaration).
  - apply nlist_at_nIn.
  - change (In (TD._sqrtf, Gfun sb_declaration) jp_object_helpers.global_definitions).
    pose proof (proj2 sb_generated_declarations_checked) as H.
    unfold sb_find_declaration in H. apply find_some in H. exact (proj1 H).
Qed.

Theorem sbr_selected_sqrtf_resolves : forall version, exists fb,
  Genv.find_symbol (Clight.globalenv (selected_clight_target version)) TD._sqrtf = Some fb /\
  Genv.find_funct_ptr (Clight.globalenv (selected_clight_target version)) fb = Some sb_declaration.
Proof.
  intros version.
  assert ((prog_defmap (selected_clight_target version)) ! TD._sqrtf =
    Some (Gfun sb_declaration)) as Hmap.
  { destruct version.
    - apply prog_defmap_norepet.
      + change (list_norepet (map fst (prog_defs us_viewport_repaired_program))).
        rewrite us_viewport_repaired_program_definitions_checked.
        exact us_viewport_repaired_definition_names_norepet.
      + change (In (TD._sqrtf, Gfun sb_declaration) (prog_defs us_viewport_repaired_program)).
        rewrite us_viewport_repaired_program_definitions_checked.
        unfold us_viewport_repaired_global_definitions.
        apply fixed_point_enters_mapped_list; [reflexivity|].
        apply PTree.elements_correct. exact sbr_us_selection.
    - destruct sbr_jp_symbol as [fb Hsymbol].
      pose proof (Genv.find_symbol_inversion _ _ Hsymbol) as Hname.
      destruct (prog_defmap_dom _ _ Hname) as [definition Hdefinition].
      assert (definition = Gfun sb_declaration) as ->.
      { apply sbr_jp_source_exact.
        apply jp_official_source_definition_provenance.
        apply in_prog_defmap in Hdefinition. exact Hdefinition. }
      exact Hdefinition. }
  apply (proj1 (Genv.find_def_symbol (selected_clight_target version)
    TD._sqrtf (Gfun sb_declaration))) in Hmap.
  destruct Hmap as [fb [Hsymbol Hdefinition]].
  exists fb. split; [exact Hsymbol|apply Genv.find_funct_ptr_iff; exact Hdefinition].
Qed.
