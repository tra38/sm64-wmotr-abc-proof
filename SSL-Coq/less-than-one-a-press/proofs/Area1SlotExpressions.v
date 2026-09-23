(** Exact relative addresses for bounded writes into one Object-pool slot.
    Only syntax whose values are established from caller temporaries is
    evaluated here; scalar memory reads remain unknown. *)
From Coq Require Import Bool Lia List ZArith.
From compcert Require Import AST Clight ClightBigstep Clightdefs Coqlib Cop Ctypes
 Errors Events Globalenvs Integers Maps Memory Values.
From LessThanOneAPress.Proofs Require Import InkPlatformWriteFrame.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Inductive ase_value := ASEint (i : int) | ASEptr (ofs : ptrofs).
Definition ase_denote b base v := match v with
| ASEint i => Vint i | ASEptr ofs => Vptr b (Ptrofs.add base ofs) end.
Definition ase_env := list (ident * ase_value).
Fixpoint ase_get id (ae : ase_env) := match ae with
| [] => None | (j,v)::rest => if Pos.eqb id j then Some v else ase_get id rest end.
Definition ase_remove id (ae : ase_env) :=
 filter (fun p => negb (Pos.eqb id (fst p))) ae.
Definition ase_put id value ae := match value with
| Some v => (id,v)::ase_remove id ae | None => ase_remove id ae end.
Definition ase_context b base ae (le : temp_env) :=
 forall id v, ase_get id ae = Some v -> le ! id = Some (ase_denote b base v).

Definition ase_field ce ty field := match ty with
| Tstruct tag _ => match ce ! tag with
  | Some co => field_offset ce field (co_members co) | None => Error (MSG "" :: nil) end
| Tunion tag _ => match ce ! tag with
  | Some co => union_field_offset ce field (co_members co) | None => Error (MSG "" :: nil) end
| _ => Error (MSG "" :: nil) end.

Definition ase_binary ce op ty1 ty2 v1 v2 := match op,v1,v2 with
| Oadd, ASEptr ofs, ASEint i =>
  match classify_add ty1 ty2 with
  | add_case_pi ty si => Some (ASEptr (Ptrofs.add ofs
       (Ptrofs.mul (Ptrofs.repr (sizeof ce ty)) (ptrofs_of_int si i))))
  | _ => None end
| Oadd, ASEint i, ASEint j =>
  if type_eq ty1 tint then if type_eq ty2 tint then Some (ASEint (Int.add i j)) else None else None
| Olt, ASEint i, ASEint j =>
  if type_eq ty1 tint then if type_eq ty2 tint then
    Some (ASEint (if Int.lt i j then Int.one else Int.zero)) else None else None
| _,_,_ => None end.

Fixpoint ase_eval ce ae a : option ase_value * option ptrofs :=
 match a with
 | Econst_int i _ => (Some (ASEint i),None)
 | Etempvar id _ => (ase_get id ae,None)
 | Ederef p ty =>
   let loc := match fst (ase_eval ce ae p) with Some (ASEptr ofs) => Some ofs | _ => None end in
   (if ipw_aggregate ty then option_map ASEptr loc else None,loc)
 | Efield p field ty =>
   let loc := match fst (ase_eval ce ae p), ase_field ce (typeof p) field with
     | Some (ASEptr ofs), OK (delta,Full) => Some (Ptrofs.add ofs (Ptrofs.repr delta))
     | _,_ => None end in
   (if ipw_aggregate ty then option_map ASEptr loc else None,loc)
 | Eaddrof p _ => (option_map ASEptr (snd (ase_eval ce ae p)),None)
 | Ecast p ty =>
   (match fst (ase_eval ce ae p), classify_cast (typeof p) ty with
    | Some (ASEptr ofs),cast_case_pointer => Some (ASEptr ofs) | _,_ => None end,None)
 | Ebinop op a1 a2 _ =>
   (match fst (ase_eval ce ae a1),fst (ase_eval ce ae a2) with
    | Some v1,Some v2 => ase_binary ce op (typeof a1) (typeof a2) v1 v2
    | _,_ => None end,None)
 | _ => (None,None) end.

Lemma ase_binary_sound : forall ce op ty1 ty2 x y z b base m answer,
 ase_binary ce op ty1 ty2 x y = Some z ->
 sem_binary_operation ce op (ase_denote b base x) ty1 (ase_denote b base y) ty2 m = Some answer ->
 answer = ase_denote b base z.
Proof.
 intros ce op ty1 ty2 x y z b base m answer Hcheck Hsem.
 destruct op; destruct x; destruct y; cbn [ase_binary] in Hcheck; try discriminate.
 all: repeat match type of Hcheck with context [if type_eq ?a ?b then _ else _] =>
   destruct (type_eq a b); try discriminate; subst end.
 - inversion Hcheck; subst.
   change (Some (Vint (Int.add i i0)) = Some answer) in Hsem.
   inversion Hsem; reflexivity.
 - destruct (classify_add ty1 ty2) eqn:Hclass; try discriminate.
   inversion Hcheck; subst. cbn [ase_denote] in *.
   unfold sem_binary_operation, sem_add in Hsem. rewrite Hclass in Hsem.
   cbn [sem_add_ptr_int] in Hsem. inversion Hsem; subst.
   rewrite Ptrofs.add_assoc. reflexivity.
 - inversion Hcheck; subst.
   change (Some (Val.of_bool (Int.lt i i0)) = Some answer) in Hsem.
   destruct (Int.lt i i0); inversion Hsem; reflexivity.
Qed.

Lemma ase_eval_lvalue_form : forall ge e le m a b ofs bf ae,
 eval_lvalue ge e le m a b ofs bf ->
 fst (ase_eval ge ae a) =
 if ipw_aggregate (typeof a) then option_map ASEptr (snd (ase_eval ge ae a)) else None.
Proof.
 intros; inversion H; subst; cbn [ase_eval typeof fst snd];
   try reflexivity; destruct (ipw_aggregate ty); reflexivity.
Qed.

Lemma ase_eval_sound : forall ge e le m b base ae,
 ase_context b base ae le ->
 (forall a v, eval_expr ge e le m a v -> forall x,
   fst (ase_eval ge ae a) = Some x -> v = ase_denote b base x) /\
 (forall a loc ofs bf, eval_lvalue ge e le m a loc ofs bf -> forall delta,
   snd (ase_eval ge ae a) = Some delta ->
   loc = b /\ ofs = Ptrofs.add base delta /\ bf = Full).
Proof.
 intros ge e le m b base ae Hctx.
 apply eval_expr_lvalue_ind; intros; cbn [ase_eval fst snd] in *; try discriminate.
 - inversion H; reflexivity.
 - eapply Hctx in H0. congruence.
 - destruct (snd (ase_eval ge ae a)) eqn:El; try discriminate.
   inversion H1; subst. destruct (H0 _ eq_refl) as (Hloc & Hofs & Hbf); subst. reflexivity.
 - destruct (fst (ase_eval ge ae a1)) eqn:E1; try discriminate.
   destruct (fst (ase_eval ge ae a2)) eqn:E2; try discriminate.
   rewrite (H0 _ eq_refl), (H2 _ eq_refl) in H3.
   eapply ase_binary_sound; eauto.
 - destruct (fst (ase_eval ge ae a)) as [[i|ofs]|] eqn:E; try discriminate.
   destruct (classify_cast (typeof a) ty) eqn:C; try discriminate.
   inversion H2; subst. rewrite (H0 _ eq_refl) in H1.
   unfold sem_cast in H1. rewrite C in H1. cbn [ase_denote] in H1.
   inversion H1; reflexivity.
 - assert (fst (ase_eval ge ae a) =
     if ipw_aggregate (typeof a) then option_map ASEptr (snd (ase_eval ge ae a)) else None) as Eform.
   { eapply ase_eval_lvalue_form; eauto. }
   rewrite Eform in H2.
   destruct (ipw_aggregate (typeof a)) eqn:Hagg; try discriminate.
   destruct (snd (ase_eval ge ae a)) eqn:E; try discriminate.
   inversion H2; subst. destruct (H0 _ eq_refl) as (Hloc & Hofs & Hbf); subst.
   inversion H1; subst; unfold ipw_aggregate in Hagg;
     try match goal with Hmode : access_mode _ = _ |- _ => rewrite Hmode in Hagg end;
     try discriminate; reflexivity.
 - destruct (fst (ase_eval ge ae a)) as [[number|relative]|] eqn:E; try discriminate.
   inversion H1; subst. specialize (H0 _ eq_refl). cbn [ase_denote] in H0.
   inversion H0; subst. auto.
 - unfold ase_field in H4; rewrite H1,H2,H3 in H4.
   destruct (fst (ase_eval ge ae a)) as [[number|relative]|] eqn:E; try discriminate.
   destruct bf; try discriminate. inversion H4; subst.
   specialize (H0 _ eq_refl). cbn [ase_denote] in H0. inversion H0; subst.
   repeat split; try reflexivity. rewrite Ptrofs.add_assoc. reflexivity.
 - unfold ase_field in H4; rewrite H1,H2,H3 in H4.
   destruct (fst (ase_eval ge ae a)) as [[number|relative]|] eqn:E; try discriminate.
   destruct bf; try discriminate. inversion H4; subst.
   specialize (H0 _ eq_refl). cbn [ase_denote] in H0. inversion H0; subst.
   repeat split; try reflexivity. rewrite Ptrofs.add_assoc. reflexivity.
Qed.
