(** The real signed hitbox store, finite positive size prefix, and producer spine.

    This is not a size-history coverage predicate. The completed helper/branch
    theorems expose real reached cuts; matching their live reads and deriving
    the legitimate entry/callback history remain explicit obligations. *)
From Coq Require Import List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Floats
  Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import GameTypes InkFlyGuyGrowthPrefix
  ObjectContactNecessity SelectedClightTarget.
Import ListNotations.
Local Open Scope Z_scope.

(** A finite arithmetic certificate now constrains the value written by the
    actual generated signed-scale multiplication, rather than an unconnected
    nominal actor template. Delayed scale Y is deliberately read separately. *)
Theorem ifgs_actual_prefix_height_store_is_bounded : forall version e le m
    ob oo scale_y t le' m' out,
  In scale_y (map ifgp_f32 ifgp_prefix_scale_bits) ->
  le ! FGH._obj = Some (Vptr ob oo) ->
  le ! FGH._t'7 = Some (Vsingle scale_y) ->
  le ! FGH._t'8 = Some (Vint (Int.repr 60)) ->
  ocn_exec (Clight.globalenv (selected_clight_target version)) e le m
    ifgp_height_store t le' m' out ->
  exists written,
    Mem.store Mfloat32 m ob (Ptrofs.unsigned (Ptrofs.add oo (Ptrofs.repr 508)))
      (Vsingle written) = Some m' /\
    Float32.cmp Cle written (ifgp_f32 1120744242) = true.
Proof.
  intros version e le m ob oo scale_y t le' m' out Hin Ho Hs Hh Hrun.
  exists (Float32.mul scale_y (Float32.of_int (Int.repr 60))).
  split.
  - exact (proj1 (ifgp_actual_hitbox_height_store version e le m ob oo scale_y
      t le' m' out Ho Hs Hh Hrun)).
  - pose proof ifgp_positive_prefix_height_ceiling_checked as Hbound.
    rewrite forallb_forall in Hbound. exact (Hbound scale_y Hin).
Qed.

(** These aliases retain the complete checked statements, including their
    actual execution and read premises. They are all discharged below. *)
Definition InkFlyGuyCompletedGrowthChoice : Prop.
Proof. let statement := type of ifgp_completed_helper_reaches_timer_choice in
  exact statement. Defined.
Definition InkFlyGuyReachedGrowthStores : Prop.
Proof. let statement := type of ifgp_executed_growth_reaches_both_stores in
  exact statement. Defined.
Definition InkFlyGuyActualScaleStore : Prop.
Proof. let statement := type of ifgp_actual_scale_store in exact statement. Defined.
Definition InkFlyGuyActualVelocityStore : Prop.
Proof. let statement := type of ifgp_actual_velocity_store in exact statement. Defined.
Definition InkFlyGuyCompletedHitboxStore : Prop.
Proof. let statement := type of ifgp_completed_hitbox_reaches_height_store in
  exact statement. Defined.
Definition InkFlyGuyBoundedPrefixHeightStore : Prop.
Proof. let statement := type of ifgs_actual_prefix_height_store_is_bounded in
  exact statement. Defined.

Definition InkFlyGuySizeStoreBoundary : Prop :=
  InkFlyGuyCompletedGrowthChoice /\ InkFlyGuyReachedGrowthStores /\
  InkFlyGuyActualScaleStore /\ InkFlyGuyActualVelocityStore /\
  InkFlyGuyCompletedHitboxStore /\ InkFlyGuyBoundedPrefixHeightStore /\
  map (fun pair =>
    (Int.unsigned (Float32.to_bits (fst (ifgp_prefix_step pair))),
     Int.unsigned (Float32.to_bits (snd (ifgp_prefix_step pair))))) ifgp_entry_pairs =
    combine (skipn 1 ifgp_prefix_scale_bits) (skipn 1 ifgp_prefix_velocity_bits).

Theorem ifgs_size_store_boundary_checked : InkFlyGuySizeStoreBoundary.
Proof.
  split; [exact ifgp_completed_helper_reaches_timer_choice|].
  split; [exact ifgp_executed_growth_reaches_both_stores|].
  split; [exact ifgp_actual_scale_store|].
  split; [exact ifgp_actual_velocity_store|].
  split; [exact ifgp_completed_hitbox_reaches_height_store|].
  split; [exact ifgs_actual_prefix_height_store_is_bounded|].
  exact ifgp_positive_prefix_bits_checked.
Qed.
