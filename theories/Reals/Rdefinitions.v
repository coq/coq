(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Classical quotient of the constructive Cauchy real numbers. *)

Require Export ZArith_base.
Require Import QArith_base.
Require Import ConstructiveRIneq.

Parameter R : Set.

(* Declare primitive numeral notations for Scope R_scope *)
Declare Scope R_scope.
Declare ML Module "r_syntax_plugin".

(* Declare Scope R_scope with Key R *)
Delimit Scope R_scope with R.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Local Open Scope R_scope.

(* The limited principle of omniscience *)
Axiom sig_forall_dec
  : forall (P : nat -> Prop),
    (forall n, {P n} + {~P n})
    -> {n | ~P n} + {forall n, P n}.

Axiom sig_not_dec : forall P : Prop, { ~~P } + { ~P }.

Axiom Rabst : ConstructiveRIneq.R -> R.
Axiom Rrepr : R -> ConstructiveRIneq.R.
Axiom Rquot1 : forall x y:R, Req (Rrepr x) (Rrepr y) -> x = y.
Axiom Rquot2 : forall x:ConstructiveRIneq.R, Req (Rrepr (Rabst x)) x.

(* Those symbols must be kept opaque, for backward compatibility. *)
Module Type RbaseSymbolsSig.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rlt : R -> R -> Prop.

  Parameter R0_def : R0 = Rabst (CRzero CR).
  Parameter R1_def : R1 = Rabst (CRone CR).
  Parameter Rplus_def : forall x y : R,
      Rplus x y = Rabst (ConstructiveRIneq.Rplus (Rrepr x) (Rrepr y)).
  Parameter Rmult_def : forall x y : R,
      Rmult x y = Rabst (ConstructiveRIneq.Rmult (Rrepr x) (Rrepr y)).
  Parameter Ropp_def : forall x : R,
      Ropp x = Rabst (ConstructiveRIneq.Ropp (Rrepr x)).
  Parameter Rlt_def : forall x y : R,
      Rlt x y = ConstructiveRIneq.RltProp (Rrepr x) (Rrepr y).
End RbaseSymbolsSig.

Module RbaseSymbolsImpl : RbaseSymbolsSig.
  Definition R0 : R := Rabst (CRzero CR).
  Definition R1 : R := Rabst (CRone CR).
  Definition Rplus : R -> R -> R
    := fun x y : R => Rabst (ConstructiveRIneq.Rplus (Rrepr x) (Rrepr y)).
  Definition Rmult : R -> R -> R
    := fun x y : R => Rabst (ConstructiveRIneq.Rmult (Rrepr x) (Rrepr y)).
  Definition Ropp : R -> R
    := fun x : R => Rabst (ConstructiveRIneq.Ropp (Rrepr x)).
  Definition Rlt : R -> R -> Prop
    := fun x y : R => ConstructiveRIneq.RltProp (Rrepr x) (Rrepr y).

  Definition R0_def := eq_refl R0.
  Definition R1_def := eq_refl R1.
  Definition Rplus_def := fun x y => eq_refl (Rplus x y).
  Definition Rmult_def := fun x y => eq_refl (Rmult x y).
  Definition Ropp_def := fun x => eq_refl (Ropp x).
  Definition Rlt_def := fun x y => eq_refl (Rlt x y).
End RbaseSymbolsImpl.
Export RbaseSymbolsImpl.

(* Keep the same names as before *)
Notation R0 := RbaseSymbolsImpl.R0 (only parsing).
Notation R1 := RbaseSymbolsImpl.R1 (only parsing).
Notation Rplus := RbaseSymbolsImpl.Rplus (only parsing).
Notation Rmult := RbaseSymbolsImpl.Rmult (only parsing).
Notation Ropp := RbaseSymbolsImpl.Ropp (only parsing).
Notation Rlt := RbaseSymbolsImpl.Rlt (only parsing).

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.

Infix "<" := Rlt : R_scope.

(***********************************************************)

(**********)
Definition Rgt (r1 r2:R) : Prop := r2 < r1.

(**********)
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.

(**********)
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

(**********)
Definition Rminus (r1 r2:R) : R := r1 + - r2.


(**********)

Infix "-" := Rminus : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.

(**********************************************************)
(** *    Injection from [Z] to [R]                        *)
(**********************************************************)

(* compact representation for 2*p *)
Fixpoint IPR_2 (p:positive) : R :=
  match p with
  | xH => R1 + R1
  | xO p => (R1 + R1) * IPR_2 p
  | xI p => (R1 + R1) * (R1 + IPR_2 p)
  end.

Definition IPR (p:positive) : R :=
  match p with
  | xH => R1
  | xO p => IPR_2 p
  | xI p => R1 + IPR_2 p
  end.
Arguments IPR p%positive : simpl never.

(**********)
Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.
Arguments IZR z%Z : simpl never.

Lemma total_order_T : forall r1 r2:R, {Rlt r1 r2} + {r1 = r2} + {Rlt r2 r1}.
Proof.
  intros. destruct (Rlt_lpo_dec (Rrepr r1) (Rrepr r2) sig_forall_dec).
  - left. left. rewrite RbaseSymbolsImpl.Rlt_def.
    apply Rlt_forget. exact r.
  - destruct (Rlt_lpo_dec (Rrepr r2) (Rrepr r1) sig_forall_dec).
    + right. rewrite RbaseSymbolsImpl.Rlt_def. apply Rlt_forget. exact r.
    + left. right. apply Rquot1. split; assumption.
Qed.

Lemma Req_appart_dec : forall x y : R,
    { x = y } + { x < y \/ y < x }.
Proof.
  intros. destruct (total_order_T x y). destruct s.
  - right. left. exact r.
  - left. exact e.
  - right. right. exact r.
Qed.

Lemma Rrepr_appart_0 : forall x:R,
    (x < R0 \/ R0 < x) -> Rappart (Rrepr x) (CRzero CR).
Proof.
  intros. apply CRltDisjunctEpsilon. destruct H.
  left. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H.
  exact H.
  right. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H.
  exact H.
Qed.

Module Type RinvSig.
  Parameter Rinv : R -> R.
  Parameter Rinv_def : forall x : R,
      Rinv x = match Req_appart_dec x R0 with
               | left _ => R0 (* / 0 is undefined, we take 0 arbitrarily *)
               | right r => Rabst ((ConstructiveRIneq.Rinv (Rrepr x) (Rrepr_appart_0 x r)))
               end.
End RinvSig.

Module RinvImpl : RinvSig.
  Definition Rinv : R -> R
    := fun x => match Req_appart_dec x R0 with
             | left _ => R0 (* / 0 is undefined, we take 0 arbitrarily *)
             | right r => Rabst ((ConstructiveRIneq.Rinv (Rrepr x) (Rrepr_appart_0 x r)))
             end.
  Definition Rinv_def := fun x => eq_refl (Rinv x).
End RinvImpl.
Notation Rinv := RinvImpl.Rinv (only parsing).

Notation "/ x" := (Rinv x) : R_scope.

(**********)
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "/" := Rdiv   : R_scope.

(* First integer strictly above x *)
Definition up (x : R) : Z.
Proof.
  destruct (Rarchimedean (Rrepr x)) as [n nmaj], (total_order_T (IZR n - x) R1).
  destruct s.
  - exact n.
  - (* x = n-1 *) exact n.
  - exact (Z.pred n).
Defined.
