(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* Ancien bug signale par Laurent Thery sur la condition de garde *)

Require Import Bool.
Require Import ZArith.

Definition rNat := positive.

Inductive rBoolOp : Set :=
  | rAnd : rBoolOp
  | rEq : rBoolOp.

Definition rlt (a b : rNat) : Prop :=
  (a ?= b)%positive Datatypes.Eq = Datatypes.Lt.

Definition rltDec : forall m n : rNat, {rlt m n} + {rlt n m \/ m = n}.
intros n m; generalize (nat_of_P_lt_Lt_compare_morphism n m);
 generalize (nat_of_P_gt_Gt_compare_morphism n m);
 generalize (Pcompare_Eq_eq n m); case ((n ?= m)%positive Datatypes.Eq).
intros H' H'0 H'1; right; right; auto.
intros H' H'0 H'1; left; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
intros H' H'0 H'1; right; left; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
apply H'0; auto.
Defined.


Definition rmax : rNat -> rNat -> rNat.
intros n m; case (rltDec n m); intros Rlt0.
exact m.
exact n.
Defined.

Inductive rExpr : Set :=
  | rV : rNat -> rExpr
  | rN : rExpr -> rExpr
  | rNode : rBoolOp -> rExpr -> rExpr -> rExpr.

Fixpoint maxVar (e : rExpr) : rNat :=
  match e with
  | rV n => n
  | rN p => maxVar p
  | rNode n p q => rmax (maxVar p) (maxVar q)
  end.

