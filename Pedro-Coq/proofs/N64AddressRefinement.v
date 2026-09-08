From Coq Require Import Bool Lia List ZArith.
From compcert Require Import Archi AST Clight Clightdefs ClightBigstep Cop Ctypes
  Events Globalenvs Integers Maps Memory Values.
From Pedro.Generated Require Import us_memory jp_memory us_behavior_data jp_behavior_data.
From Pedro.Proofs Require Import GameTypes TTCCogExecution CogActionExecution
  DustAllocationBoundary.
Import ListNotations.
Open Scope Z_scope.

(** Numeric operations of the original generated address-conversion function.
    The execution below checks this formula against its complete Clight body.
    The table block still has the normal CompCert representation. *)
Definition n64_segment_index address := Int.shru address (Int.repr 24).
Definition n64_segment_offset address := Int.and address (Int.repr 16777215).
Definition n64_virtual_address base address :=
  Int.or (Int.add base (n64_segment_offset address)) (Int.repr (-2147483648)).
Definition n64_table_offset address :=
  Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4)
    (Ptrofs.of_intu (n64_segment_index address))).

Ltac n64_temp :=
  repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; reflexivity.
Ltac n64_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ => eapply eval_Etempvar; n64_temp
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop; [n64_expr | n64_expr | reflexivity]
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast; [n64_expr | reflexivity]
  | |- eval_expr _ _ _ _ _ _ =>
      eapply eval_Elvalue; [n64_lvalue |
        first [eapply deref_loc_reference; reflexivity |
          eapply deref_loc_value; [reflexivity |
            cbn -[Int.shru Int.and Int.or Int.add Ptrofs.mul Ptrofs.of_intu];
            first [eassumption |
              rewrite Ptrofs.add_zero_l; eassumption]]]]
  end
with n64_lvalue :=
  lazymatch goal with
  | |- eval_lvalue _ _ _ _ (Evar _ _) _ _ _ =>
      eapply eval_Evar_global; [reflexivity | eassumption]
  | |- eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ => eapply eval_Ederef; n64_expr
  end.
Ltac n64_stmt :=
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [n64_stmt | n64_stmt]
  | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ => eapply exec_Sset; n64_expr
  | |- exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      eapply exec_Sreturn_some; n64_expr
  end.

Theorem generated_segmented_numeric_execution_us_jp :
  forall version (ge : Clight.genv) memory table address base,
    Genv.find_symbol ge us_memory._sSegmentTable = Some table ->
    Mem.load Mint32 memory table (n64_table_offset address) = Some (Vint base) ->
    eval_funcall function_entry2 ge memory (Internal (dust_segment_function version))
      [Vint address] E0 memory (Vint (n64_virtual_address base address)).
Proof.
  intros version ge memory table address base Hsymbol Hload.
  unfold n64_table_offset, n64_segment_index in Hload.
  unfold n64_virtual_address, n64_segment_offset.
  destruct version; cbn [dust_segment_function].
  all: eapply eval_funcall_internal;
    [action_entry | simpl fn_body; timeout 15 n64_stmt |
     split; [discriminate | reflexivity] | reflexivity].
Qed.

Lemma n64_cached_address : forall low,
  0 <= low < 2147483648 ->
  Int.or (Int.repr low) (Int.repr (-2147483648)) =
    Int.repr (2147483648 + low).
Proof.
  intros low Hrange.
  assert (Hlow : Int.and (Int.repr low) (Int.repr 2147483647) = Int.repr low).
  { unfold Int.and.
    rewrite Int.unsigned_repr by (change (0 <= low <= 4294967295); lia).
    change (Int.repr (Z.land low (Z.ones 31)) = Int.repr low).
    rewrite Z.land_ones by lia.
    change (Int.repr (low mod 2147483648) = Int.repr low).
    rewrite Z.mod_small by lia. reflexivity. }
  assert (Hdisjoint : Int.and (Int.repr low) (Int.repr (-2147483648)) = Int.zero).
  { rewrite <- Hlow at 1. rewrite Int.and_assoc.
    change (Int.and (Int.repr low) Int.zero = Int.zero).
    apply Int.and_zero. }
  rewrite <- Int.add_is_or by exact Hdisjoint.
  unfold Int.add.
  rewrite Int.unsigned_repr by (change (0 <= low <= 4294967295); lia).
  change (Int.repr (low + 2147483648) = Int.repr (2147483648 + low)).
  f_equal. lia.
Qed.

Definition n64_behavior_address offset := Int.repr (318767104 + offset).

Lemma n64_behavior_index : forall offset,
  0 <= offset < 16777216 ->
  n64_segment_index (n64_behavior_address offset) = Int.repr 19.
Proof.
  intros offset Hrange. unfold n64_segment_index, n64_behavior_address.
  rewrite Int.shru_div_two_p.
  rewrite Int.unsigned_repr by (change (0 <= 318767104 + offset <= 4294967295); lia).
  change (Int.repr ((318767104 + offset) / 16777216) = Int.repr 19).
  replace (318767104 + offset) with (offset + 19 * 16777216) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma n64_behavior_offset : forall offset,
  0 <= offset < 16777216 ->
  n64_segment_offset (n64_behavior_address offset) = Int.repr offset.
Proof.
  intros offset Hrange. unfold n64_segment_offset, n64_behavior_address, Int.and.
  rewrite Int.unsigned_repr by (change (0 <= 318767104 + offset <= 4294967295); lia).
  change (Int.repr (Z.land (318767104 + offset) (Z.ones 24)) = Int.repr offset).
  rewrite Z.land_ones by lia.
  change (Int.repr ((318767104 + offset) mod 16777216) = Int.repr offset).
  replace (318767104 + offset) with (offset + 19 * 16777216) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma n64_behavior_table_offset : forall offset,
  0 <= offset < 16777216 ->
  n64_table_offset (n64_behavior_address offset) = 76.
Proof.
  intros offset Hrange. unfold n64_table_offset.
  rewrite n64_behavior_index by assumption. reflexivity.
Qed.

Lemma n64_behavior_table_access_in_bounds : forall offset,
  0 <= offset < 16777216 ->
  0 <= n64_table_offset (n64_behavior_address offset) /\
  n64_table_offset (n64_behavior_address offset) + 4 <= 128.
Proof.
  intros offset Hrange. rewrite n64_behavior_table_offset by assumption. lia.
Qed.

Lemma n64_behavior_virtual_address : forall base offset,
  0 <= base -> 0 <= offset < 16777216 -> base + offset < 536870912 ->
  n64_virtual_address (Int.repr base) (n64_behavior_address offset) =
    Int.repr (2147483648 + base + offset).
Proof.
  intros base offset Hbase Hoffset Hsum.
  unfold n64_virtual_address. rewrite n64_behavior_offset by assumption.
  unfold Int.add.
  rewrite (Int.unsigned_repr base) by (change (0 <= base <= 4294967295); lia).
  rewrite (Int.unsigned_repr offset) by (change (0 <= offset <= 4294967295); lia).
  rewrite n64_cached_address by lia. f_equal. lia.
Qed.

(** The finite address domain is the three generated scripts reached by dust.
    Placement is supplied by a loader/linker image; it is not inferred from a
    CompCert block number or from an unauthenticated emulator address. *)
Inductive N64DustScript := N64Mist | N64Puff1 | N64Puff2.

Definition n64_dust_global version script : globvar type :=
  match version, script with
  | VersionUS, N64Mist => us_behavior_data.v_bhvMistParticleSpawner
  | VersionUS, N64Puff1 => us_behavior_data.v_bhvWhitePuff1
  | VersionUS, N64Puff2 => us_behavior_data.v_bhvWhitePuff2
  | VersionJP, N64Mist => jp_behavior_data.v_bhvMistParticleSpawner
  | VersionJP, N64Puff1 => jp_behavior_data.v_bhvWhitePuff1
  | VersionJP, N64Puff2 => jp_behavior_data.v_bhvWhitePuff2
  end.
Definition n64_dust_symbol version script : ident :=
  match version, script with
  | VersionUS, N64Mist => us_behavior_data._bhvMistParticleSpawner
  | VersionUS, N64Puff1 => us_behavior_data._bhvWhitePuff1
  | VersionUS, N64Puff2 => us_behavior_data._bhvWhitePuff2
  | VersionJP, N64Mist => jp_behavior_data._bhvMistParticleSpawner
  | VersionJP, N64Puff1 => jp_behavior_data._bhvWhitePuff1
  | VersionJP, N64Puff2 => jp_behavior_data._bhvWhitePuff2
  end.
Definition n64_dust_size script : Z :=
  match script with N64Mist => 48 | N64Puff1 => 36 | N64Puff2 => 40 end.
Definition n64_dust_first_word script : int :=
  match script with N64Mist | N64Puff1 => Int.repr 524288
                 | N64Puff2 => Int.repr 786432 end.

Theorem generated_n64_dust_storage_us_jp : forall version script ce,
  sizeof ce (gvar_info (n64_dust_global version script)) = n64_dust_size script /\
  init_data_list_size (gvar_init (n64_dust_global version script)) = n64_dust_size script /\
  hd_error (gvar_init (n64_dust_global version script)) =
    Some (Init_int32 (n64_dust_first_word script)).
Proof. intros version script ce; destruct version, script; repeat split; reflexivity. Qed.

Theorem generated_n64_segment_table_storage_us_jp : forall ce,
  sizeof ce (gvar_info us_memory.v_sSegmentTable) = 128 /\
  sizeof ce (gvar_info jp_memory.v_sSegmentTable) = 128 /\
  gvar_init us_memory.v_sSegmentTable = [Init_space 128] /\
  gvar_init jp_memory.v_sSegmentTable = [Init_space 128] /\
  us_memory._sSegmentTable = jp_memory._sSegmentTable.
Proof. intros; repeat split; reflexivity. Qed.

Record N64DustPlacement (base : Z) (place : N64DustScript -> Z) : Prop := {
  n64_base_bound : 0 <= base /\ base + 16777216 <= 536870912;
  n64_script_bounds : forall script,
    0 <= place script /\ place script + n64_dust_size script <= 16777216;
  n64_script_disjoint : forall first second, first <> second ->
    place first + n64_dust_size first <= place second \/
    place second + n64_dust_size second <= place first
}.

Definition n64_decode_region base start length block address : option val :=
  let relative := Int.unsigned address - (2147483648 + base + start) in
  if (0 <=? relative) && (relative <? length)
  then Some (Vptr block (Ptrofs.repr relative)) else None.

Definition n64_decode_dust base place (blocks : N64DustScript -> block) address :=
  match n64_decode_region base (place N64Mist) (n64_dust_size N64Mist)
          (blocks N64Mist) address with
  | Some value => Some value
  | None =>
    match n64_decode_region base (place N64Puff1) (n64_dust_size N64Puff1)
            (blocks N64Puff1) address with
    | Some value => Some value
    | None => n64_decode_region base (place N64Puff2) (n64_dust_size N64Puff2)
                (blocks N64Puff2) address
    end
  end.

Lemma n64_dust_size_bounds : forall script, 0 < n64_dust_size script <= 48.
Proof. destruct script; cbn; lia. Qed.

Lemma n64_decode_region_hit : forall base start length block offset,
  0 <= base -> 0 <= start -> 0 <= offset < length ->
  base + start + offset < 536870912 ->
  n64_decode_region base start length block
    (Int.repr (2147483648 + base + start + offset)) =
    Some (Vptr block (Ptrofs.repr offset)).
Proof.
  intros base start length block offset Hb Hs Ho Hsum.
  unfold n64_decode_region.
  rewrite Int.unsigned_repr by
    (change (0 <= 2147483648 + base + start + offset <= 4294967295); lia).
  replace (2147483648 + base + start + offset - (2147483648 + base + start))
    with offset by lia.
  destruct (Z.leb_spec0 0 offset); [| lia].
  destruct (Z.ltb_spec0 offset length); [reflexivity | lia].
Qed.

Lemma n64_decode_region_miss : forall base place blocks script other offset,
  N64DustPlacement base place -> script <> other ->
  0 <= offset < n64_dust_size script ->
  n64_decode_region base (place other) (n64_dust_size other) (blocks other)
    (Int.repr (2147483648 + base + place script + offset)) = None.
Proof.
  intros base place blocks script other offset Hlayout Hne Ho.
  destruct Hlayout as [Hb Hbounds Hapart].
  pose proof (Hbounds script) as Hs. pose proof (Hbounds other) as Ht.
  specialize (Hapart script other Hne).
  unfold n64_decode_region.
  rewrite Int.unsigned_repr by
    (change (0 <= 2147483648 + base + place script + offset <= 4294967295); lia).
  destruct (Z.leb_spec0 0
    (2147483648 + base + place script + offset - (2147483648 + base + place other)));
    [| reflexivity].
  destruct (Z.ltb_spec0
    (2147483648 + base + place script + offset - (2147483648 + base + place other))
    (n64_dust_size other)); [lia | reflexivity].
Qed.

Theorem n64_dust_address_round_trip : forall base place blocks script offset,
  N64DustPlacement base place -> 0 <= offset < n64_dust_size script ->
  n64_decode_dust base place blocks
    (n64_virtual_address (Int.repr base)
      (n64_behavior_address (place script + offset))) =
    Some (Vptr (blocks script) (Ptrofs.repr offset)).
Proof.
  intros base place blocks script offset Hlayout Ho.
  pose proof (n64_base_bound _ _ Hlayout) as Hb.
  pose proof (n64_script_bounds _ _ Hlayout script) as Hs.
  rewrite n64_behavior_virtual_address by lia.
  replace (2147483648 + base + (place script + offset))
    with (2147483648 + base + place script + offset) by lia.
  destruct script; unfold n64_decode_dust.
  - rewrite n64_decode_region_hit by lia. reflexivity.
  - rewrite n64_decode_region_miss by (try assumption; discriminate).
    rewrite n64_decode_region_hit by lia. reflexivity.
  - rewrite n64_decode_region_miss by (try assumption; discriminate).
    rewrite n64_decode_region_miss by (try assumption; discriminate).
    apply n64_decode_region_hit; lia.
Qed.

(** These offsets are authenticated against both clean ROM images by
    pipeline/check-n64-dust-addresses.py. They are relative to segment 19,
    not runtime virtual addresses. The loader's physical base remains a
    memory-state premise. *)
Definition retail_n64_dust_offset script : Z :=
  match script with N64Mist => 9388 | N64Puff1 => 9436 | N64Puff2 => 9472 end.

Lemma retail_n64_dust_placement : forall base,
  0 <= base -> base + 16777216 <= 536870912 ->
  N64DustPlacement base retail_n64_dust_offset.
Proof.
  intros base Hb Hsum. constructor.
  - split; assumption.
  - destruct script; cbn; lia.
  - intros first second Hne. destruct first, second; cbn; try congruence; lia.
Qed.

Definition n64_dust_symbols version (ge : Clight.genv) blocks : Prop :=
  forall script, Genv.find_symbol ge (n64_dust_symbol version script) = Some (blocks script).

(** A memory observation THROUGH the explicitly bounded decoder. This is not
    CompCert's ordinary dereference of Vint. Its address calculation and its
    connection to the unchanged symbolic memory are proved below. *)
Definition n64_dust_load base blocks memory chunk address : option val :=
  match n64_decode_dust base retail_n64_dust_offset blocks address with
  | Some (Vptr script offset) => Mem.load chunk memory script (Ptrofs.unsigned offset)
  | _ => None
  end.

Lemma n64_dust_load_round_trip : forall base blocks script offset memory chunk,
  0 <= base -> base + 16777216 <= 536870912 ->
  0 <= offset < n64_dust_size script ->
  n64_dust_load base blocks memory chunk
    (n64_virtual_address (Int.repr base)
      (n64_behavior_address (retail_n64_dust_offset script + offset))) =
    Mem.load chunk memory (blocks script) offset.
Proof.
  intros base blocks script offset memory chunk Hb Hsum Ho.
  unfold n64_dust_load. rewrite n64_dust_address_round_trip;
    [| apply retail_n64_dust_placement; assumption | assumption].
  pose proof (n64_dust_size_bounds script).
  rewrite Ptrofs.unsigned_repr by (change (0 <= offset <= 4294967295); lia).
  reflexivity.
Qed.

Definition n64_dust_conversion_claim : Prop :=
  forall version (ge : Clight.genv) memory table base blocks script offset,
    n64_dust_symbols version ge blocks ->
    Genv.find_symbol ge us_memory._sSegmentTable = Some table ->
    Mem.load Mint32 memory table 76 = Some (Vint (Int.repr base)) ->
    0 <= base -> base + 16777216 <= 536870912 ->
    0 <= offset < n64_dust_size script ->
    exists address,
      eval_funcall function_entry2 ge memory (Internal (dust_segment_function version))
        [Vint (n64_behavior_address (retail_n64_dust_offset script + offset))]
        E0 memory (Vint address) /\
      n64_decode_dust base retail_n64_dust_offset blocks address =
        Some (Vptr (blocks script) (Ptrofs.repr offset)) /\
      Genv.find_symbol ge (n64_dust_symbol version script) = Some (blocks script) /\
      (forall chunk, n64_dust_load base blocks memory chunk address =
        Mem.load chunk memory (blocks script) offset).

(** The actual generated conversion is now an execution conclusion, not a
    callee-execution hypothesis. It returns a numeric address with identical
    memory and an empty trace; decoding that address gives precisely the
    original generated behavior symbol and byte offset. *)
Theorem generated_n64_dust_conversion_us_jp : n64_dust_conversion_claim.
Proof.
  intros version ge memory table base blocks script offset Hsymbols Htable Hload Hb Hsum Ho.
  pose proof (retail_n64_dust_placement base Hb Hsum) as Hlayout.
  pose proof (n64_script_bounds _ _ Hlayout script) as Hbounds.
  exists (n64_virtual_address (Int.repr base)
    (n64_behavior_address (retail_n64_dust_offset script + offset))).
  split.
  - eapply generated_segmented_numeric_execution_us_jp; [exact Htable |].
    rewrite n64_behavior_table_offset by lia. exact Hload.
  - split. { apply n64_dust_address_round_trip; assumption. }
    split. { apply Hsymbols. }
    intros chunk. apply n64_dust_load_round_trip; assumption.
Qed.

(** Real generated initializers provide the scalar word needed by
    create_object, via CompCert's standard initialization characterization. *)
Lemma generated_n64_dust_initial_word :
  forall version script (program : AST.program Clight.fundef type) memory block,
    Genv.find_var_info (Genv.globalenv program) block =
      Some (n64_dust_global version script) ->
    Genv.init_mem program = Some memory ->
    Mem.load Mint32 memory block 0 = Some (Vint (n64_dust_first_word script)).
Proof.
  intros version script program memory block Hvar Hinit.
  pose proof (Genv.init_mem_characterization program block Hvar Hinit) as Himage.
  destruct Himage as [_ [_ [Hwords _]]].
  destruct version, script; specialize (Hwords eq_refl); exact (proj1 Hwords).
Qed.

(** A second observation is in a flat RAM block, at the physical address
    corresponding to KSEG0. CompCert's memory injection supplies the byte and
    permission correspondence; no equality of the two memory images is assumed.
    This lemma covers scalar words. Pointer relocation words require their own
    representation relation and are not silently treated as scalar integers. *)
Definition n64_kseg0_load memory ram address : option val :=
  let address_z := Int.unsigned address in
  if (2147483648 <=? address_z) && (address_z <? 2684354560)
  then Mem.load Mint32 memory ram (address_z - 2147483648) else None.

Theorem n64_dust_scalar_word_injection :
  forall base script offset symbols_memory flat_memory injection blocks ram word,
    0 <= base -> base + 16777216 <= 536870912 ->
    0 <= offset < n64_dust_size script ->
    Mem.inject injection symbols_memory flat_memory ->
    injection (blocks script) = Some (ram, base + retail_n64_dust_offset script) ->
    Mem.load Mint32 symbols_memory (blocks script) offset = Some (Vint word) ->
    n64_kseg0_load flat_memory ram
      (n64_virtual_address (Int.repr base)
        (n64_behavior_address (retail_n64_dust_offset script + offset))) = Some (Vint word).
Proof.
  intros base script offset symbols_memory flat_memory injection blocks ram word
    Hb Hsum Ho Hinject Hmap Hword.
  pose proof (retail_n64_dust_placement base Hb Hsum) as Hlayout.
  pose proof (n64_script_bounds _ _ Hlayout script) as Hbounds.
  destruct (Mem.load_inject _ _ _ _ _ _ _ _ _ Hinject Hword Hmap)
    as [value [Hflat Hvalue]].
  inversion Hvalue; subst value.
  rewrite n64_behavior_virtual_address by lia.
  unfold n64_kseg0_load.
  rewrite Int.unsigned_repr by
    (change (0 <= 2147483648 + base + (retail_n64_dust_offset script + offset) <= 4294967295); lia).
  destruct (Z.leb_spec0 2147483648
    (2147483648 + base + (retail_n64_dust_offset script + offset))); [| lia].
  destruct (Z.ltb_spec0
    (2147483648 + base + (retail_n64_dust_offset script + offset)) 2684354560); [| lia].
  replace (2147483648 + base + (retail_n64_dust_offset script + offset) - 2147483648)
    with (offset + (base + retail_n64_dust_offset script)) by lia.
  exact Hflat.
Qed.
