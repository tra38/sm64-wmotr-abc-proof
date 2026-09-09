(** Backward from raw collision Y to the actual State-to-Object copy.
    The four earlier stores and the Y store are selected generated statements. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Cop Ctypes Integers Maps.
From LessThanOneAPress.Proofs Require Import GameTypes Area1Rank18CopyRead
  Area1Rank18CopyResolution Area1Rank18StateArrayBound EyerokRank15LiveMovement
  InkBackwardSource InkBackwardExecution InkFloorResetExecution
  ObjectContactNecessity Area2Rank12BContact.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Module IRC := R18U.
Definition irc_before_y version := ocn_prefix_items 4
  (rank12b_drop_sequences 2 (fn_body (rank18_copy_body version))).
Definition irc_y_stage version := ibk_head
  (rank12b_drop_sequences 6 (fn_body (rank18_copy_body version))).
Definition irc_after_y version := rank12b_drop_sequences 7
  (fn_body (rank18_copy_body version)).

Definition irc_float_stage version receiver value source index :=
  Ssequence (Sset receiver rank15_current_object_expression)
    (Ssequence (Sset value source)
      (Sassign (rank15_raw_float_expression version receiver index)
        (Etempvar value tfloat))).

Definition irc_constant (e : expr) : option int := match e with
| Econst_int n (Tint I32 Signed _) => Some n
| Ebinop Oadd (Econst_int x (Tint I32 Signed _))
    (Econst_int y (Tint I32 Signed _)) (Tint I32 Signed _) => Some (Int.add x y)
| _ => None end.

Definition irc_before_stage_ok version s : Prop :=
  exists receiver value source index number,
    s = irc_float_stage version receiver value source index /\
    receiver <> value /\ receiver <> IRC._i /\ value <> IRC._i /\
    typeof index = tint /\
    irc_constant index = Some (Int.repr number) /\ In number [9; 10; 11; 6].

Ltac irc_stage_receipt number :=
  unfold irc_before_stage_ok; do 4 eexists; exists number;
  split; [reflexivity|]; repeat split; try discriminate; try reflexivity; cbn; auto.

Theorem irc_generated_cuts : forall version,
  fn_vars (rank18_copy_body version) = [] /\
  fn_body (rank18_copy_body version) =
    Ssequence (Sset IRC._i (Econst_int Int.zero tint))
      (Ssequence rank18_index_test
        (ocn_prepend (irc_before_y version)
          (Ssequence (irc_y_stage version) (irc_after_y version)))) /\
  Forall (irc_before_stage_ok version) (irc_before_y version) /\
  forallb ibk_normal (irc_before_y version) = true /\
  ibk_normal (irc_y_stage version) = true /\
  ifr_keeps_temp IRC._i (ocn_prepend (irc_before_y version) Sskip) = true.
Proof.
  intro version.
  assert (Forall (irc_before_stage_ok version) (irc_before_y version)) as Hstages.
  { destruct version.
    all: apply Forall_cons; [irc_stage_receipt 9|].
    all: apply Forall_cons; [irc_stage_receipt 10|].
    all: apply Forall_cons; [irc_stage_receipt 11|].
    all: apply Forall_cons; [irc_stage_receipt 6|].
    all: apply Forall_nil. }
  split; [destruct version; reflexivity|].
  split; [destruct version; reflexivity|].
  split; [exact Hstages|]. destruct version; repeat split; reflexivity.
Qed.

Definition irc_state_zero := Ederef
  (Ebinop Oadd
    (Evar IRC._gMarioStates (tarray (Tstruct IRC._MarioState noattr) 0))
    (Etempvar IRC._i tint) (tptr (Tstruct IRC._MarioState noattr)))
  (Tstruct IRC._MarioState noattr).
Definition irc_state_position := Efield irc_state_zero IRC._pos (tarray tfloat 3).
Definition irc_source_y := Ederef (Ebinop Oadd irc_state_position
  (Econst_int (Int.repr 1) tint) (tptr tfloat)) tfloat.

Theorem irc_y_stage_is_generated : forall version,
  irc_y_stage version = irc_float_stage version IRC._t'27 IRC._t'28
    irc_source_y rank15_y_index.
Proof. intros []; reflexivity. Qed.
