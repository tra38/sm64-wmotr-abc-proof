From Coq Require Import List ZArith.
From compcert Require Import AST Integers.
From Pedro.Generated Require Import us_behavior_data jp_behavior_data.
From Pedro.Proofs Require Import GameTypes N64AddressRefinement.
Import ListNotations.
Open Scope Z_scope.

(** Finite big-endian word receipts, authenticated against the clean US/JP ROM
    hashes and generated initializers by check-n64-dust-addresses.py. Hashing
    is outside Coq. The theorem below checks the complete transcription,
    including relocation words; it does not identify native callback machine
    code with its Clight semantics. *)
Definition retail_n64_us_mist_words : list Z :=
  [524288; 857079808; 1; 889192448; 469762048; 142; 318776540;
   469762048; 150; 318776576; 16777217; 486539264].
Definition retail_n64_us_puff1_words : list Z :=
  [524288; 857079808; 1; 285278209; 553648128; 134217728; 201326592;
   2150375824; 150994944].
Definition retail_n64_us_puff2_words : list Z :=
  [786432; 285278211; 553648128; 270204927; 83886087; 201326592;
   2150376052; 253362177; 100663296; 486539264].
Definition retail_n64_jp_mist_words : list Z :=
  [524288; 857079808; 1; 889192448; 469762048; 142; 318776540;
   469762048; 150; 318776576; 16777217; 486539264].
Definition retail_n64_jp_puff1_words : list Z :=
  [524288; 857079808; 1; 285278209; 553648128; 134217728; 201326592;
   2150373316; 150994944].
Definition retail_n64_jp_puff2_words : list Z :=
  [786432; 285278211; 553648128; 270204927; 83886087; 201326592;
   2150373544; 253362177; 100663296; 486539264].

Definition retail_n64_dust_words version script :=
  match version, script with
  | VersionUS, N64Mist => retail_n64_us_mist_words
  | VersionUS, N64Puff1 => retail_n64_us_puff1_words
  | VersionUS, N64Puff2 => retail_n64_us_puff2_words
  | VersionJP, N64Mist => retail_n64_jp_mist_words
  | VersionJP, N64Puff1 => retail_n64_jp_puff1_words
  | VersionJP, N64Puff2 => retail_n64_jp_puff2_words
  end.

Definition n64_dust_relocations version : list (ident * int) :=
  match version with
  | VersionUS =>
    [(us_behavior_data._bhvWhitePuff1,
        n64_behavior_address (retail_n64_dust_offset N64Puff1));
     (us_behavior_data._bhvWhitePuff2,
        n64_behavior_address (retail_n64_dust_offset N64Puff2));
     (us_behavior_data._bhv_white_puff_1_loop, Int.repr 2150375824);
     (us_behavior_data._bhv_white_puff_2_loop, Int.repr 2150376052)]
  | VersionJP =>
    [(jp_behavior_data._bhvWhitePuff1,
        n64_behavior_address (retail_n64_dust_offset N64Puff1));
     (jp_behavior_data._bhvWhitePuff2,
        n64_behavior_address (retail_n64_dust_offset N64Puff2));
     (jp_behavior_data._bhv_white_puff_1_loop, Int.repr 2150373316);
     (jp_behavior_data._bhv_white_puff_2_loop, Int.repr 2150373544)]
  end.

Fixpoint n64_lookup_relocation id entries : option int :=
  match entries with
  | [] => None
  | (name, address) :: rest =>
      if Pos.eqb id name then Some address else n64_lookup_relocation id rest
  end.

Definition n64_relocate_initializer version data : option int :=
  match data with
  | Init_int32 word => Some word
  | Init_addrof id offset =>
      if Ptrofs.eq offset Ptrofs.zero then n64_lookup_relocation id (n64_dust_relocations version)
      else None
  | _ => None
  end.

Theorem retail_n64_dust_words_refine_generated : forall version script,
  map (n64_relocate_initializer version) (gvar_init (n64_dust_global version script)) =
    map (fun word => Some (Int.repr word)) (retail_n64_dust_words version script).
Proof. intros [] []; vm_compute; reflexivity. Qed.

Theorem retail_n64_dust_headers_and_sizes : forall version script,
  hd_error (retail_n64_dust_words version script) =
    Some (Int.unsigned (n64_dust_first_word script)) /\
  4 * Z.of_nat (length (retail_n64_dust_words version script)) = n64_dust_size script.
Proof. intros [] []; vm_compute; split; reflexivity. Qed.
