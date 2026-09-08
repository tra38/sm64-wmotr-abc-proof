From Pedro.Proofs Require Import GameTypes CloneFloorExecution CloneFloorPartition
  CloneFloorRefresh TTCCloneCandidates.

(** The cloning/floor frontier consumes real Clight execution and generated
    source receipts. A published triangle is searchable independently of its
    parent Object fields; a fully cleared partition yields no such floor.
    The source replacement branch and BREAK loop explain the non-holdable
    candidate restriction. Reachable script installation, all surrounding
    frame updates, surface republishing and a preserving dust event remain
    separate obligations. This is not a universal no-cloning theorem. *)
Definition ttc_cog_clone_floor_frontier_claim : Prop :=
  clone_query_layout_receipt /\
  clone_partition_layout_receipt /\
  clone_mario_floor_layout_receipt /\
  clone_carry_scripts_claim /\
  clone_nonholdable_source_claim /\
  (forall version, clone_floor_search_source_claim version) /\
  (forall version, clone_break_dispatch_claim version) /\
  (forall version, published_cog_floor_execution_claim version) /\
  (forall version, clone_cleared_partition_query_claim version) /\
  (forall version, clone_floor_reset_execution_claim version) /\
  (forall version, clone_floor_refresh_source_claim version) /\
  (forall version, clone_time_stop_execution_claim version) /\
  ttc_clone_candidate_catalogue_claim.

Theorem checked_ttc_cog_clone_floor_frontier_us_jp : ttc_cog_clone_floor_frontier_claim.
Proof.
  refine (conj clone_query_layout_generated_us_jp _).
  refine (conj clone_partition_layout_generated_us_jp _).
  refine (conj clone_mario_floor_layout_generated_us_jp _).
  refine (conj generated_clone_carry_scripts_us_jp _).
  refine (conj generated_nonholdable_script_replacement_us_jp _).
  refine (conj generated_clone_floor_search_source_us_jp _).
  refine (conj generated_clone_break_dispatch_us_jp _).
  refine (conj generated_published_cog_floor_selected_us_jp _).
  refine (conj generated_cleared_partition_has_no_floor_us_jp _).
  refine (conj generated_floor_query_resets_mario_floor_us_jp _).
  refine (conj generated_clone_floor_refresh_source_us_jp _).
  exact (conj generated_time_stop_retains_dynamic_lists_us_jp
    checked_ttc_clone_candidate_catalogue_us_jp).
Qed.
