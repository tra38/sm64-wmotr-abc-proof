(** The nine landing descriptors are PUBLIC writable globals.  Their ordinary
    generated uses only borrow their addresses for cancellation, whose body
    reads scalar fields. This does not make them private: the external-call
    boundary must protect them explicitly before a lifetime theorem follows. *)
From Coq Require Import Bool List ZArith.
From compcert Require Import AST Clight Clightdefs Ctypes Integers.
From LessThanOneAPress.Proofs Require Import ASTFacts ActionDepthAliasCensus
  InkLandingCallerSource InkLandingHistorySource InkMovingBackwardSource
  LinkedClightPrograms WritableActionTableAliasExternalClosure WritableActionTableWholeGameAliases.
Import ListNotations.
Import Clightdefs.ClightNotations.

Definition ildp_ids := map ilw_descriptor ilw_kinds.
Definition ildp_no_global id expr := Nat.eqb (wat_evar_count id expr) 0.
Definition ildp_no_globals id args := Nat.eqb (wat_expression_list_evar_count id args) 0.
Definition ildp_borrow_call id fn args := match fn, args with
| Evar called _, [mario; Eaddrof (Evar named _) _; callback] =>
    Pos.eqb called IMB._common_landing_cancels && Pos.eqb named id &&
    ildp_no_global id mario && ildp_no_global id callback
| _, _ => false end.
Fixpoint ildp_global_uses id s := match s with
| Sskip | Sbreak | Scontinue | Sreturn None | Sgoto _ => true
| Sassign lhs rhs => ildp_no_global id lhs && ildp_no_global id rhs
| Sset _ rhs => ildp_no_global id rhs
| Scall _ fn args => (ildp_no_global id fn && ildp_no_globals id args) ||
    ildp_borrow_call id fn args
| Sbuiltin _ _ _ args => ildp_no_globals id args
| Ssequence a b | Sloop a b => ildp_global_uses id a && ildp_global_uses id b
| Sifthenelse test a b => ildp_no_global id test && ildp_global_uses id a && ildp_global_uses id b
| Sreturn (Some expr) => ildp_no_global id expr
| Sswitch expr cases => ildp_no_global id expr && ildp_global_cases id cases
| Slabel _ body => ildp_global_uses id body end
with ildp_global_cases id cases := match cases with
| LSnil => true
| LScons _ body rest => ildp_global_uses id body && ildp_global_cases id rest end.

Definition ildp_program program :=
  watwg_program_has_no_initializer_alias ildp_ids program &&
  forallb (fun entry => match snd entry with
    | Gfun (Internal body) => forallb (fun id => ildp_global_uses id (fn_body body)) ildp_ids
    | _ => true end) (prog_defs program).

Theorem ildp_all_units_have_no_initial_alias_and_only_borrow_for_cancellation :
  watwg_nlist_all ildp_program us_units = true /\
  watwg_nlist_all ildp_program jp_units = true.
Proof. vm_compute; split; reflexivity. Qed.

Theorem ildp_all_nine_descriptors_are_exported :
  forallb (fun id => ident_mem id (prog_public us_mario_actions_moving.prog)) ildp_ids = true /\
  forallb (fun id => ident_mem id (prog_public jp_mario_actions_moving.prog)) ildp_ids = true.
Proof. vm_compute; split; reflexivity. Qed.

Definition ildp_no_borrow expr := negb (expression_mentions_ident IMB._landingAction expr).
Definition ildp_scalar_borrow_read expr := match expr with
| Efield (Ederef (Etempvar temp _) _) _ ty =>
    Pos.eqb temp IMB._landingAction &&
    match ty with Tint _ _ _ => true | _ => false end
| _ => false end.
Fixpoint ildp_borrower s := match s with
| Sskip | Sbreak | Scontinue | Sreturn None | Sgoto _ => true
| Sassign lhs rhs => ildp_no_borrow lhs && ildp_no_borrow rhs
| Sset id rhs => negb (Pos.eqb id IMB._landingAction) &&
    (ildp_no_borrow rhs || ildp_scalar_borrow_read rhs)
| Scall opt fn args =>
    (match opt with None => true | Some id => negb (Pos.eqb id IMB._landingAction) end) &&
    ildp_no_borrow fn && forallb ildp_no_borrow args
| Sbuiltin opt _ _ args =>
    (match opt with None => true | Some id => negb (Pos.eqb id IMB._landingAction) end) &&
    forallb ildp_no_borrow args
| Ssequence a b | Sloop a b => ildp_borrower a && ildp_borrower b
| Sifthenelse test a b => ildp_no_borrow test && ildp_borrower a && ildp_borrower b
| Sreturn (Some expr) => ildp_no_borrow expr
| Sswitch expr cases => ildp_no_borrow expr && ildp_borrower_cases cases
| Slabel _ body => ildp_borrower body end
with ildp_borrower_cases cases := match cases with
| LSnil => true
| LScons _ body rest => ildp_borrower body && ildp_borrower_cases rest end.

Theorem ildp_real_borrower_only_reads_scalars : forall version,
  ildp_borrower (fn_body (ilh_cancel_body version)) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Definition InkLandingDescriptorAccessSource : Prop :=
  (watwg_nlist_all ildp_program us_units = true /\
   watwg_nlist_all ildp_program jp_units = true) /\
  (forallb (fun id => ident_mem id (prog_public us_mario_actions_moving.prog)) ildp_ids = true /\
   forallb (fun id => ident_mem id (prog_public jp_mario_actions_moving.prog)) ildp_ids = true) /\
  (forall version, ildp_borrower (fn_body (ilh_cancel_body version)) = true).
Theorem ildp_descriptor_access_source_checked : InkLandingDescriptorAccessSource.
Proof.
  split; [exact ildp_all_units_have_no_initial_alias_and_only_borrow_for_cancellation|].
  split; [exact ildp_all_nine_descriptors_are_exported|exact ildp_real_borrower_only_reads_scalars].
Qed.
