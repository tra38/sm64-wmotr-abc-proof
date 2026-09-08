From Coq Require Import Lia List ZArith.
From compcert Require Import AST Clight Clightdefs ClightBigstep Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import us_spawn_object jp_spawn_object us_memory.
From Pedro.Proofs Require Import GameTypes TTCCogExecution DustAllocationBoundary
  N64AddressRefinement N64DustImage.
Import ListNotations.
Open Scope Z_scope.

Definition n64_create_function version :=
  match version with VersionUS => us_spawn_object.f_create_object
                   | VersionJP => jp_spawn_object.f_create_object end.

(** The two actual leading statements: retain the behavior argument and
    classify its first word. Allocation and object writes follow this prefix. *)
Definition n64_create_header version :=
  match fn_body (n64_create_function version) with
  | Ssequence first (Ssequence second _) => Ssequence first second
  | _ => Sskip
  end.
Definition n64_create_header_entry version block :=
  PTree.set us_spawn_object._bhvScript (Vptr block Ptrofs.zero)
    (create_undef_temps (fn_temps (n64_create_function version))).
Definition n64_dust_object_list script :=
  match script with N64Mist | N64Puff1 => Int.repr 8 | N64Puff2 => Int.repr 12 end.

Lemma generated_n64_header_entry_us_jp : forall version block,
  bind_parameter_temps (fn_params (n64_create_function version))
    [Vptr block Ptrofs.zero] (create_undef_temps (fn_temps (n64_create_function version))) =
    Some (n64_create_header_entry version block).
Proof. intros []; reflexivity. Qed.

Definition n64_create_header_claim : Prop :=
  forall version script (ge : Clight.genv) memory behavior,
    Mem.load Mint32 memory behavior 0 = Some (Vint (n64_dust_first_word script)) ->
    exists locals,
      exec_stmt function_entry2 ge (PTree.empty (block * type))
        (n64_create_header_entry version behavior) memory (n64_create_header version)
        E0 locals memory Out_normal /\
      locals ! us_spawn_object._objListIndex = Some (Vint (n64_dust_object_list script)).

Theorem generated_n64_create_header_us_jp : n64_create_header_claim.
Proof.
  intros version script ge memory behavior Hword.
  destruct version, script; cbn [n64_dust_first_word] in Hword.
  all: eexists; split.
  all: lazymatch goal with
  | |- exec_stmt _ _ _ _ _ _ _ _ _ _ =>
      unfold n64_create_header, n64_create_header_entry, n64_create_function;
      cbn [fn_body fn_temps]; cog_reduce_statement; timeout 10 cog_stmt
  | _ => reflexivity
  end.
Qed.

(** Compose the numeric conversion, its explicit decoding boundary, and the
    original allocator header. This relation keeps the representation change
    visible: it does NOT assert an ordinary symbolic Clight call to the
    segmented converter, which DustAllocationBoundary proves impossible. *)
Definition n64_dust_header_refinement_claim : Prop :=
  forall version script (ge : Clight.genv) memory table base blocks,
    n64_dust_symbols version ge blocks ->
    Genv.find_symbol ge us_memory._sSegmentTable = Some table ->
    Mem.load Mint32 memory table 76 = Some (Vint (Int.repr base)) ->
    0 <= base -> base + 16777216 <= 536870912 ->
    Mem.load Mint32 memory (blocks script) 0 = Some (Vint (n64_dust_first_word script)) ->
    exists address locals,
      eval_funcall function_entry2 ge memory (Internal (dust_segment_function version))
        [Vint (n64_behavior_address (retail_n64_dust_offset script))]
        E0 memory (Vint address) /\
      n64_decode_dust base retail_n64_dust_offset blocks address =
        Some (Vptr (blocks script) Ptrofs.zero) /\
      n64_dust_load base blocks memory Mint32 address =
        Some (Vint (n64_dust_first_word script)) /\
      exec_stmt function_entry2 ge (PTree.empty (block * type))
        (n64_create_header_entry version (blocks script)) memory
        (n64_create_header version) E0 locals memory Out_normal /\
      locals ! us_spawn_object._objListIndex = Some (Vint (n64_dust_object_list script)).

Theorem generated_n64_dust_header_refinement_us_jp : n64_dust_header_refinement_claim.
Proof.
  intros version script ge memory table base blocks Hsymbols Htable Hload Hb Hsum Hword.
  pose proof (n64_dust_size_bounds script) as Hsize.
  destruct (generated_n64_dust_conversion_us_jp version ge memory table base blocks script 0
    Hsymbols Htable Hload Hb Hsum ltac:(lia)) as [address [Hrun [Hdecode [_ Hread]]]].
  rewrite Z.add_0_r in Hrun.
  destruct (generated_n64_create_header_us_jp version script ge memory (blocks script) Hword)
    as [locals [Hheader Hindex]].
  exists address, locals. split; [exact Hrun |].
  split; [exact Hdecode |]. split.
  - rewrite Hread. exact Hword.
  - split; assumption.
Qed.

Definition n64_initialized_header_claim : Prop :=
  forall version script (program : AST.program Clight.fundef type) memory behavior (ge : Clight.genv),
    Genv.find_var_info (Genv.globalenv program) behavior =
      Some (n64_dust_global version script) ->
    Genv.init_mem program = Some memory ->
    exists locals,
      exec_stmt function_entry2 ge (PTree.empty (block * type))
        (n64_create_header_entry version behavior) memory (n64_create_header version)
        E0 locals memory Out_normal /\
      locals ! us_spawn_object._objListIndex = Some (Vint (n64_dust_object_list script)).

Theorem generated_n64_initialized_header_us_jp : n64_initialized_header_claim.
Proof.
  intros version script program memory behavior ge Hvar Hinit.
  apply generated_n64_create_header_us_jp.
  eapply generated_n64_dust_initial_word; eassumption.
Qed.

Definition n64_flat_header_claim : Prop :=
  forall version script (ge : Clight.genv) symbols_memory flat_memory injection blocks ram base,
    0 <= base -> base + 16777216 <= 536870912 ->
    Mem.inject injection symbols_memory flat_memory ->
    injection (blocks script) = Some (ram, base + retail_n64_dust_offset script) ->
    Mem.load Mint32 symbols_memory (blocks script) 0 =
      Some (Vint (n64_dust_first_word script)) ->
    n64_kseg0_load flat_memory ram
      (n64_virtual_address (Int.repr base)
        (n64_behavior_address (retail_n64_dust_offset script))) =
      Some (Vint (n64_dust_first_word script)) /\
    exists locals,
      exec_stmt function_entry2 ge (PTree.empty (block * type))
        (n64_create_header_entry version (blocks script)) symbols_memory (n64_create_header version)
        E0 locals symbols_memory Out_normal /\
      locals ! us_spawn_object._objListIndex = Some (Vint (n64_dust_object_list script)).

Theorem generated_n64_flat_header_us_jp : n64_flat_header_claim.
Proof.
  intros version script ge symbols_memory flat_memory injection blocks ram base Hb Hsum Hinject Hmap Hword.
  split.
  - pose proof (n64_dust_size_bounds script) as Hsize.
    pose proof (n64_dust_scalar_word_injection base script 0 symbols_memory flat_memory
      injection blocks ram (n64_dust_first_word script) Hb Hsum ltac:(lia) Hinject Hmap Hword) as Hflat.
    rewrite Z.add_0_r in Hflat. exact Hflat.
  - apply generated_n64_create_header_us_jp. exact Hword.
Qed.

Definition n64_dust_address_frontier_claim : Prop :=
  n64_dust_conversion_claim /\
  n64_dust_header_refinement_claim /\
  n64_initialized_header_claim /\
  n64_flat_header_claim /\
  (forall version script ce,
    sizeof ce (gvar_info (n64_dust_global version script)) = n64_dust_size script /\
    init_data_list_size (gvar_init (n64_dust_global version script)) = n64_dust_size script /\
    hd_error (gvar_init (n64_dust_global version script)) =
      Some (Init_int32 (n64_dust_first_word script))) /\
  (forall version script,
    map (n64_relocate_initializer version) (gvar_init (n64_dust_global version script)) =
      map (fun word => Some (Int.repr word)) (retail_n64_dust_words version script) /\
    hd_error (retail_n64_dust_words version script) =
      Some (Int.unsigned (n64_dust_first_word script)) /\
    4 * Z.of_nat (length (retail_n64_dust_words version script)) = n64_dust_size script).

Theorem checked_n64_dust_address_frontier_us_jp : n64_dust_address_frontier_claim.
Proof.
  split; [exact generated_n64_dust_conversion_us_jp |].
  split; [exact generated_n64_dust_header_refinement_us_jp |].
  split; [exact generated_n64_initialized_header_us_jp |].
  split; [exact generated_n64_flat_header_us_jp |].
  split; [exact generated_n64_dust_storage_us_jp |].
  intros version script. split.
  - apply retail_n64_dust_words_refine_generated.
  - apply retail_n64_dust_headers_and_sizes.
Qed.
