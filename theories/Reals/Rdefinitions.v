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
Require Import ConstructiveCauchyReals.

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
  : forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Axiom Rabst : CReal -> R.
Axiom Rrepr : R -> CReal.
Axiom Rquot1 : forall x y:R, CRealEq (Rrepr x) (Rrepr y) -> x = y.
Axiom Rquot2 : forall x:CReal, CRealEq (Rrepr (Rabst x)) x.

(* Those symbols must be kept opaque, for backward compatibility. *)
Module Type RbaseSymbolsSig.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rlt : R -> R -> Prop.

  Parameter R0_def : R0 = Rabst 0%CReal.
  Parameter R1_def : R1 = Rabst 1%CReal.
  Parameter Rplus_def : forall x y : R,
      Rplus x y = Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Parameter Rmult_def : forall x y : R,
      Rmult x y = Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Parameter Ropp_def : forall x : R,
      Ropp x = Rabst (CReal_opp (Rrepr x)).
  Parameter Rlt_def : forall x y : R,
      Rlt x y = CRealLt (Rrepr x) (Rrepr y).
End RbaseSymbolsSig.

Module RbaseSymbolsImpl : RbaseSymbolsSig.
  Definition R0 : R := Rabst 0%CReal.
  Definition R1 : R := Rabst 1%CReal.
  Definition Rplus : R -> R -> R
    := fun x y : R => Rabst (CReal_plus (Rrepr x) (Rrepr y)).
  Definition Rmult : R -> R -> R
    := fun x y : R => Rabst (CReal_mult (Rrepr x) (Rrepr y)).
  Definition Ropp : R -> R
    := fun x : R => Rabst (CReal_opp (Rrepr x)).
  Definition Rlt : R -> R -> Prop
    := fun x y : R => CRealLt (Rrepr x) (Rrepr y).

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

Lemma CRealLt_dec : forall x y : CReal, { CRealLt x y } + { ~CRealLt x y }.
Proof.
  intros.
  destruct (sig_forall_dec
              (fun n:nat => Qle (proj1_sig y (S n) - proj1_sig x (S n)) (2 # Pos.of_nat (S n)))).
  - intro n. destruct (Qlt_le_dec (2 # Pos.of_nat (S n))
                                  (proj1_sig y (S n) - proj1_sig x (S n))).
    right. apply Qlt_not_le. exact q. left. exact q.
  - left. destruct s as [n nmaj]. exists (Pos.of_nat (S n)).
    rewrite Nat2Pos.id. apply Qnot_le_lt. exact nmaj. discriminate.
  - right. intro abs. destruct abs as [n majn].
    specialize (q (pred (Pos.to_nat n))).
    replace (S (pred (Pos.to_nat n))) with (Pos.to_nat n) in q.
    rewrite Pos2Nat.id in q.
    pose proof (Qle_not_lt _ _ q). contradiction.
    symmetry. apply Nat.succ_pred. intro abs.
    pose proof (Pos2Nat.is_pos n). rewrite abs in H. inversion H.
Qed.

Lemma total_order_T : forall r1 r2:R, {Rlt r1 r2} + {r1 = r2} + {Rlt r2 r1}.
Proof.
  intros. destruct (CRealLt_dec (Rrepr r1) (Rrepr r2)).
  - left. left. rewrite RbaseSymbolsImpl.Rlt_def. exact c.
  - destruct (CRealLt_dec (Rrepr r2) (Rrepr r1)).
    + right. rewrite RbaseSymbolsImpl.Rlt_def. exact c.
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
    (x < R0 \/ R0 < x) -> (Rrepr x # 0)%CReal.
Proof.
  intros. destruct H. left. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H. exact H.
  right. rewrite RbaseSymbolsImpl.Rlt_def, RbaseSymbolsImpl.R0_def, Rquot2 in H. exact H.
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
  destruct (Rarchimedean (Rrepr x)) as [n nmaj], (total_order_T (IZR n - x) R1).
  destruct s.
  - exact n.
  - (* x = n-1 *) exact n.
  - exact (Z.pred n).
Defined.
