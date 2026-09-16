(** The real two-word sqrtf routine, decoded from the authenticated JP
    instruction manifest. This is a deliberately small VR4300 instruction
    projection, NOT a replacement for the generated Clight program.
    SQRT.S uses Flocq's IEEE binary32 operation. We project RAM, registers
    and delayed control flow, not exception flags or a whole console.
    Normal return requires usable COP1, nearest-even mode, disabled inexact
    trapping, and a nonnegative normal-or-zero operand. Connecting an
    EF_external event in the selected Clight execution to this machine
    invocation is an explicit remaining refinement, never a new axiom. *)
From Coq Require Import Bool Lia List ZArith Reals Lra.
From Flocq Require Import BinarySingleNaN Binary Core.
From compcert Require Import AST Events Floats Integers Memory Values.
From LessThanOneAPress.Proofs Require Import
  InkTimer131RetailMipsCode Area2Rank9ACoinFlight.
Import ListNotations.
Local Open Scope Z_scope.

Inductive SqrtfInstruction :=
| SqrtfJumpRegister (source : Z)
| SqrtfSquareRootSingle (source destination : Z).

Definition sqrtf_decode word : option SqrtfInstruction :=
  if (jp_mips_opcode word =? 0) && (jp_mips_funct word =? 8) &&
     (Z.land word 2097088 =? 0)
  then Some (SqrtfJumpRegister (jp_mips_rs word))
  else if (jp_mips_opcode word =? 17) && (jp_mips_rs word =? 16) &&
    (jp_mips_rt word =? 0) && (jp_mips_funct word =? 4)
  then Some (SqrtfSquareRootSingle
    (Z.land (Z.shiftr word 11) 31) (Z.land (Z.shiftr word 6) 31))
  else None.

Theorem sqrtf_actual_words_decode :
  map sqrtf_decode jp_sqrtf_words =
    [Some (SqrtfJumpRegister 31); Some (SqrtfSquareRootSingle 12 0)].
Proof. vm_compute; reflexivity. Qed.

Definition sqrtf_operand_domain x : Prop :=
  rank9cf_finite x /\ (0 <= rank9cf_real x)%R /\
  ((rank9cf_real x = 0)%R \/
   (bpow radix2 (-126) <= rank9cf_real x)%R).

Record SqrtfMachineState := {
  sqrtf_pc : Z;
  sqrtf_next_pc : Z;
  sqrtf_gpr : Z -> Z;
  sqrtf_fpr : Z -> float32;
  sqrtf_memory : mem;
  sqrtf_rounding : mode;
  sqrtf_cop1_usable : bool;
  sqrtf_inexact_enabled : bool
}.

Definition sqrtf_jump (s : SqrtfMachineState) source :=
  {| sqrtf_pc := sqrtf_next_pc s; sqrtf_next_pc := sqrtf_gpr s source;
     sqrtf_gpr := sqrtf_gpr s; sqrtf_fpr := sqrtf_fpr s;
     sqrtf_memory := sqrtf_memory s; sqrtf_rounding := sqrtf_rounding s;
     sqrtf_cop1_usable := sqrtf_cop1_usable s;
     sqrtf_inexact_enabled := sqrtf_inexact_enabled s |}.
Definition sqrtf_write (s : SqrtfMachineState) source destination :=
  {| sqrtf_pc := sqrtf_next_pc s; sqrtf_next_pc := sqrtf_next_pc s + 4;
     sqrtf_gpr := sqrtf_gpr s;
     sqrtf_fpr := fun r => if r =? destination then
       Bsqrt 24 128 eq_refl eq_refl Float32.unop_nan
         (sqrtf_rounding s) (sqrtf_fpr s source) else sqrtf_fpr s r;
     sqrtf_memory := sqrtf_memory s; sqrtf_rounding := sqrtf_rounding s;
     sqrtf_cop1_usable := sqrtf_cop1_usable s;
     sqrtf_inexact_enabled := sqrtf_inexact_enabled s |}.

Inductive SqrtfInstructionStep : Z -> SqrtfMachineState -> SqrtfMachineState -> Prop :=
| sqrtf_step_jump : forall word s source,
    sqrtf_decode word = Some (SqrtfJumpRegister source) ->
    SqrtfInstructionStep word s (sqrtf_jump s source)
| sqrtf_step_square_root : forall word s source destination,
    sqrtf_decode word = Some (SqrtfSquareRootSingle source destination) ->
    Z.even source = true -> Z.even destination = true ->
    sqrtf_cop1_usable s = true -> sqrtf_inexact_enabled s = false ->
    sqrtf_operand_domain (sqrtf_fpr s source) ->
    SqrtfInstructionStep word s (sqrtf_write s source destination).

Inductive SqrtfWordExecution : list Z -> SqrtfMachineState -> SqrtfMachineState -> Prop :=
| sqrtf_words_nil : forall s, SqrtfWordExecution [] s s
| sqrtf_words_cons : forall word words before middle after,
    SqrtfInstructionStep word before middle ->
    SqrtfWordExecution words middle after ->
    SqrtfWordExecution (word :: words) before after.

(** All executions of the actual words in this instruction projection,
    including the delay slot. No numerical result or RAM frame is assumed. *)
Theorem sqrtf_actual_routine_result : forall before after,
  sqrtf_rounding before = mode_NE ->
  SqrtfWordExecution jp_sqrtf_words before after ->
  sqrtf_pc after = sqrtf_gpr before 31 /\
  sqrtf_fpr after 0 = Float32.sqrt (sqrtf_fpr before 12) /\
  sqrtf_memory after = sqrtf_memory before /\
  sqrtf_gpr after = sqrtf_gpr before /\
  (forall r, r <> 0 -> sqrtf_fpr after r = sqrtf_fpr before r).
Proof.
  intros before after Hround Hrun.
  inversion Hrun; subst.
  match goal with H : SqrtfInstructionStep _ _ _ |- _ =>
    inversion H; subst; clear H end.
  all: match goal with H : sqrtf_decode _ = _ |- _ => vm_compute in H; inversion H; subst; clear H end.
  match goal with H : SqrtfWordExecution (_ :: _) _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : SqrtfInstructionStep _ _ _ |- _ => inversion H; subst; clear H end.
  all: match goal with H : sqrtf_decode _ = _ |- _ => vm_compute in H; inversion H; subst; clear H end.
  match goal with H : SqrtfWordExecution [] _ _ |- _ => inversion H; subst; clear H end.
  cbn [sqrtf_jump sqrtf_write sqrtf_rounding sqrtf_fpr sqrtf_gpr sqrtf_pc sqrtf_memory].
  rewrite Hround. repeat split; try reflexivity.
  intros r Hr. assert (r =? 0 = false) as E by (apply Z.eqb_neq; exact Hr).
  rewrite E. reflexivity.
Qed.

Theorem sqrtf_actual_routine_exists : forall before,
  sqrtf_cop1_usable before = true -> sqrtf_inexact_enabled before = false ->
  sqrtf_operand_domain (sqrtf_fpr before 12) ->
  exists after, SqrtfWordExecution jp_sqrtf_words before after.
Proof.
  intros before Hcop Htrap Hinput.
  exists (sqrtf_write (sqrtf_jump before 31) 12 0).
  econstructor.
  - apply sqrtf_step_jump. reflexivity.
  - econstructor.
    + apply sqrtf_step_square_root; try reflexivity; assumption.
    + constructor.
Qed.

(** The CPU instruction model itself has a mathematical correctness theorem,
    not merely equality to a function named sqrt. *)
Theorem sqrtf_result_is_correctly_rounded : forall before after,
  sqrtf_rounding before = mode_NE ->
  SqrtfWordExecution jp_sqrtf_words before after ->
  rank9cf_real (sqrtf_fpr after 0) =
    rank9cf_round (sqrt (rank9cf_real (sqrtf_fpr before 12))).
Proof.
  intros before after Hround Hrun.
  destruct (sqrtf_actual_routine_result _ _ Hround Hrun) as (_ & Hr & _).
  rewrite Hr. exact (proj1 (Bsqrt_correct 24 128 eq_refl eq_refl
    Float32.unop_nan mode_NE (sqrtf_fpr before 12))).
Qed.

(** A concrete ABI realization of one call. This relation is not silently
    installed as Events.external_functions_sem. The old model still needs
    an explicit link from its reached external event to this realization. *)
Definition SqrtfMachineCall argument before trace result after : Prop :=
  exists entry finish,
    sqrtf_pc entry = jp_mips_range_start jp_sqrtf_range /\
    sqrtf_next_pc entry = jp_mips_range_start jp_sqrtf_range + 4 /\
    sqrtf_fpr entry 12 = argument /\ sqrtf_memory entry = before /\
    sqrtf_rounding entry = mode_NE /\
    SqrtfWordExecution jp_sqrtf_words entry finish /\
    result = Vsingle (sqrtf_fpr finish 0) /\
    after = sqrtf_memory finish /\ trace = E0.

(** Non-vacuity of the local implementation: every admitted operand has an
    actual two-instruction execution in this projection, for any RAM. This
    is not an existence claim for the enclosing game/Clight execution. *)
Theorem sqrtf_machine_call_exists : forall argument before,
  sqrtf_operand_domain argument ->
  exists result after, SqrtfMachineCall argument before E0 result after.
Proof.
  intros argument before Hdomain.
  set (entry := {| sqrtf_pc := jp_mips_range_start jp_sqrtf_range;
    sqrtf_next_pc := jp_mips_range_start jp_sqrtf_range + 4;
    sqrtf_gpr := fun _ => jp_mips_range_end jp_sqrtf_range;
    sqrtf_fpr := fun r => if r =? 12 then argument else Float32.zero;
    sqrtf_memory := before; sqrtf_rounding := mode_NE;
    sqrtf_cop1_usable := true; sqrtf_inexact_enabled := false |}).
  destruct (sqrtf_actual_routine_exists entry eq_refl eq_refl Hdomain)
    as [finish Hrun].
  exists (Vsingle (sqrtf_fpr finish 0)), (sqrtf_memory finish).
  exists entry, finish. repeat split; try reflexivity; exact Hrun.
Qed.

Theorem sqrtf_machine_call_value_and_memory : forall argument before trace result after,
  SqrtfMachineCall argument before trace result after ->
  result = Vsingle (Float32.sqrt argument) /\ after = before /\ trace = E0.
Proof.
  intros argument before trace result after
    (entry & finish & Hpc & Hnext & Harg & Hmem & Hmode & Hrun & -> & -> & ->).
  destruct (sqrtf_actual_routine_result _ _ Hmode Hrun) as (_ & Hr & Hm & _).
  rewrite Hr, Harg, Hm, Hmem. auto.
Qed.

Theorem sqrtf_machine_call_has_writable_frame : forall argument before trace result after
    chunk block offset,
  SqrtfMachineCall argument before trace result after ->
  Mem.load chunk after block offset = Mem.load chunk before block offset.
Proof.
  intros. destruct (sqrtf_machine_call_value_and_memory _ _ _ _ _ H) as (_ & -> & _).
  reflexivity.
Qed.
