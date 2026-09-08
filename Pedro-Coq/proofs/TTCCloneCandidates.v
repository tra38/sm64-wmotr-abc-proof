From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Integers.
From Pedro.Generated Require Import
  us_behavior_data jp_behavior_data us_macro_special_objects jp_macro_special_objects
  us_obj_behaviors jp_obj_behaviors us_obj_behaviors_2 jp_obj_behaviors_2
  us_object_helpers jp_object_helpers.
From Pedro.Proofs Require Import ASTFacts GameTypes TTCRNGCensus TTCRNGWindow.
Import ListNotations.
Open Scope Z_scope.
Module TC := us_behavior_data.

(** All TTC descriptors assigned to the surface-object list, including the
    six decorative gear variants. Object-list membership is a conservative
    candidate filter, not a proof that every candidate publishes a floor. *)
Definition ttc_clone_surface_descriptors version : list ident :=
  behaviors_in_object_list version 9 (ttc_static_behavior_ids version).

Definition ttc_clone_surface_families : list ident :=
  [TC._bhvThwomp; TC._bhvTTCRotatingSolid; TC._bhvTTCPendulum;
   TC._bhvTTCTreadmill; TC._bhvTTCMovingBar; TC._bhvTTCCog;
   TC._bhvTTCPitBlock; TC._bhvTTCElevator; TC._bhvTTC2DRotator;
   TC._bhvTTCSpinner; TC._bhvExclamationBox; TC._bhvBlueCoinSwitch].

Definition ttc_clone_surface_inventory_claim version : Prop :=
  length (ttc_clone_surface_descriptors version) = 79%nat /\
  forallb (fun behavior => existsb (Pos.eqb behavior) ttc_clone_surface_families)
    (ttc_clone_surface_descriptors version) = true /\
  map (fun behavior => count_occ Pos.eq_dec (ttc_clone_surface_descriptors version) behavior)
    ttc_clone_surface_families = [1; 8; 4; 7; 12; 8; 1; 2; 8; 14; 13; 1]%nat.

Theorem generated_ttc_clone_surface_inventory_us_jp :
  forall version, ttc_clone_surface_inventory_claim version.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

(** Decode only at authenticated behavior-command boundaries. Extract the
    immediate SET_INT/OR_INT writes to field 1 (oFlags). Unexpected/truncated
    command sequences fail closed. This is about script writes; native code
    and runtime memory still require their own invariants. *)
Fixpoint clone_script_flag_words (fuel : nat) (words : list init_data)
    : option (list Z) :=
  match words, fuel with
  | [], _ => Some []
  | _, O => None
  | Init_int32 word :: rest, S remaining =>
      match behavior_command_entry_count (command_opcode word) with
      | Some (S tail_size) =>
          if Nat.leb tail_size (length rest) then
            match clone_script_flag_words remaining (skipn tail_size rest) with
            | Some flags =>
                if ((Z.eqb (command_opcode word) 16 || Z.eqb (command_opcode word) 17)
                    && Z.eqb (Z.land (Z.shiftr (Int.unsigned word) 16) 255) 1)%bool
                then Some (Z.land (Int.unsigned word) 65535 :: flags)
                else Some flags
            | None => None
            end
          else None
      | _ => None
      end
  | _, _ => None
  end.

Definition clone_behavior_flag_words version behavior : option (list Z) :=
  match behavior_initializer version behavior with
  | Some words =>
      match behavior_script_scan_result version behavior with
      | Some _ => clone_script_flag_words (length words) words
      | None => None
      end
  | None => None
  end.

Definition clone_script_never_sets_holdable version behavior : bool :=
  match clone_behavior_flag_words version behavior with
  | Some flags => forallb (fun word => Z.eqb (Z.land word 1024) 0) flags
  | None => false
  end.

Theorem generated_ttc_surface_scripts_do_not_set_holdable_us_jp :
  forall version,
    forallb (clone_script_never_sets_holdable version) ttc_clone_surface_families = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Definition clone_script_sets_holdable version behavior : bool :=
  match clone_behavior_flag_words version behavior with
  | Some flags => existsb (fun word => negb (Z.eqb (Z.land word 1024) 0)) flags
  | None => false
  end.

Theorem generated_ttc_holdable_script_descriptors_us_jp :
  forall version,
    filter (clone_script_sets_holdable version) (ttc_static_behavior_ids version) =
      [TC._bhvHeaveHo; TC._bhvBobomb; TC._bhvBobomb] /\
    count_occ Pos.eq_dec (ttc_static_behavior_ids version) TC._bhvBreakableBox = 0%nat /\
    count_occ Pos.eq_dec (ttc_static_behavior_ids version) TC._bhvBreakableBoxSmall = 0%nat.
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.

(** Each TTC exclamation-box descriptor has no parameter override. Its preset
    selects walking 1-Up (7), ten coins (6), or three coins (5). This excludes
    shell/cap/star contents from these stock TTC boxes, but not from arbitrary
    changes to their runtime parameters. *)
Definition ttc_clone_box_records version : list (list Z) :=
  filter (fun record =>
    match macro_code_behavior version (macro_record_code record) with
    | Some behavior => Pos.eqb behavior TC._bhvExclamationBox
    | None => false end) (ttc_exact_macro_records version).

Definition ttc_clone_box_preset_parameter version record : option Z :=
  let entries := gvar_init (match version with
    | VersionUS => us_macro_special_objects.v_sMacroObjectPresets
    | VersionJP => jp_macro_special_objects.v_sMacroObjectPresets end) in
  match nth_error entries (3 * Z.to_nat (macro_record_code record - 31) + 2)%nat with
  | Some (Init_int16 value) => Some (Int.unsigned value)
  | _ => None
  end.

Theorem generated_ttc_clone_box_contents_us_jp :
  forall version,
    map (fun record => nth 4 record 0) (ttc_clone_box_records version) = repeat 0 13 /\
    map (ttc_clone_box_preset_parameter version) (ttc_clone_box_records version) =
      map (@Some Z) [7; 7; 6; 6; 5; 5; 6; 5; 5; 6; 5; 5; 6].
Proof. intros []; vm_compute; split; reflexivity. Qed.

Definition ttc_clone_candidate_catalogue_claim : Prop :=
  (forall version, ttc_clone_surface_inventory_claim version) /\
  (forall version,
    forallb (clone_script_never_sets_holdable version) ttc_clone_surface_families = true) /\
  (forall version,
    filter (clone_script_sets_holdable version) (ttc_static_behavior_ids version) =
      [TC._bhvHeaveHo; TC._bhvBobomb; TC._bhvBobomb] /\
    count_occ Pos.eq_dec (ttc_static_behavior_ids version) TC._bhvBreakableBox = 0%nat /\
    count_occ Pos.eq_dec (ttc_static_behavior_ids version) TC._bhvBreakableBoxSmall = 0%nat) /\
  (forall version,
    map (fun record => nth 4 record 0) (ttc_clone_box_records version) = repeat 0 13 /\
    map (ttc_clone_box_preset_parameter version) (ttc_clone_box_records version) =
      map (@Some Z) [7; 7; 6; 6; 5; 5; 6; 5; 5; 6; 5; 5; 6]).

Theorem checked_ttc_clone_candidate_catalogue_us_jp : ttc_clone_candidate_catalogue_claim.
Proof.
  refine (conj generated_ttc_clone_surface_inventory_us_jp _).
  refine (conj generated_ttc_surface_scripts_do_not_set_holdable_us_jp _).
  exact (conj generated_ttc_holdable_script_descriptors_us_jp
    generated_ttc_clone_box_contents_us_jp).
Qed.
