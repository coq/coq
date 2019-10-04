(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Abstraction of classical Dedekind reals behind an opaque module,
   for backward compatibility.

   This file also contains the proof that classical reals are a
   quotient of constructive Cauchy reals. *)

Require Export ZArith_base.
Require Import QArith_base.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ClassicalDedekindReals.


(* Declare primitive numeral notations for Scope R_scope *)
Declare Scope R_scope.
Declare ML Module "r_syntax_plugin".

(* Declare Scope R_scope with Key R *)
Delimit Scope R_scope with R.

Local Open Scope R_scope.


(* Those symbols must be kept opaque, for backward compatibility. *)
Module Type RbaseSymbolsSig.
  Parameter R : Set.
  Bind Scope R_scope with R.
  Axiom Rabst : CReal -> R.
  Axiom Rrepr : R -> CReal.
  Axiom Rquot1 : forall x y:R, CRealEq (Rrepr x) (Rrepr y) -> x = y.
  Axiom Rquot2 : forall x:CReal, CRealEq (Rrepr (Rabst x)) x.

  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rlt : R -> R -> Prop.

  Parameter R0_def : R0 = Rabst (inject_Q 0).
  Parameter R1_def : R1 = Rabst (inject_Q 1).
  Parameter Rplus_def : forall x y : R,
      Rplus x y = Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Parameter Rmult_def : forall x y : R,
      Rmult x y = Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Parameter Ropp_def : forall x : R,
      Ropp x = Rabst (CReal_opp (Rrepr x)).
  Parameter Rlt_def : forall x y : R,
      Rlt x y = CRealLtProp (Rrepr x) (Rrepr y).
End RbaseSymbolsSig.

Module RbaseSymbolsImpl : RbaseSymbolsSig.
  Definition R := DReal.
  Definition Rabst := DRealAbstr.
  Definition Rrepr := DRealRepr.
  Definition Rquot1 := DRealQuot1.
  Definition Rquot2 := DRealQuot2.
  Definition R0 : R := Rabst (inject_Q 0).
  Definition R1 : R := Rabst (inject_Q 1).
  Definition Rplus : R -> R -> R
    := fun x y : R => Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Definition Rmult : R -> R -> R
    := fun x y : R => Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Definition Ropp : R -> R
    := fun x : R => Rabst (CReal_opp (Rrepr x)).
  Definition Rlt : R -> R -> Prop
    := fun x y : R => CRealLtProp (Rrepr x) (Rrepr y).

  Definition R0_def := eq_refl R0.
  Definition R1_def := eq_refl R1.
  Definition Rplus_def := fun x y => eq_refl (Rplus x y).
  Definition Rmult_def := fun x y => eq_refl (Rmult x y).
  Definition Ropp_def := fun x => eq_refl (Ropp x).
  Definition Rlt_def := fun x y => eq_refl (Rlt x y).
End RbaseSymbolsImpl.
Export RbaseSymbolsImpl.

(* Keep the same names as before *)
Notation R := RbaseSymbolsImpl.R (only parsing).
Notation R0 := RbaseSymbolsImpl.R0 (only parsing).
Notation R1 := RbaseSymbolsImpl.R1 (only parsing).
Notation Rplus := RbaseSymbolsImpl.Rplus (only parsing).
Notation Rmult := RbaseSymbolsImpl.Rmult (only parsing).
Notation Ropp := RbaseSymbolsImpl.Ropp (only parsing).
Notation Rlt := RbaseSymbolsImpl.Rlt (only parsing).

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

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
  intros. destruct (CRealLt_lpo_dec (Rrepr r1) (Rrepr r2) sig_forall_dec).
  - left. left. rewrite RbaseSymbolsImpl.Rlt_def.
    apply CRealLtForget. exact c.
  - destruct (CRealLt_lpo_dec (Rrepr r2) (Rrepr r1) sig_forall_dec).
    + right. rewrite RbaseSymbolsImpl.Rlt_def. apply CRealLtForget. exact c.
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
    (x < R0 \/ R0 < x) -> CReal_appart (Rrepr x) (inject_Q 0).
Proof.
  intros. apply CRealLtDisjunctEpsilon. destruct H.
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
               | right r => Rabst ((CReal_inv (Rrepr x) (Rrepr_appart_0 x r)))
               end.
End RinvSig.

Module RinvImpl : RinvSig.
  Definition Rinv : R -> R
    := fun x => match Req_appart_dec x R0 with
             | left _ => R0 (* / 0 is undefined, we take 0 arbitrarily *)
             | right r => Rabst ((CReal_inv (Rrepr x) (Rrepr_appart_0 x r)))
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
  destruct (CRealArchimedean (Rrepr x)) as [n nmaj], (total_order_T (IZR n - x) R1).
  destruct s.
  - exact n.
  - (* x = n-1 *) exact n.
  - exact (Z.pred n).
Defined.
