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

Inductive rBoolOp: Set :=
     rAnd: rBoolOp
    | rEq: rBoolOp .

Definition rlt: rNat -> rNat ->Prop := [a, b:rNat](compare a b EGAL)=INFERIEUR.

Definition rltDec: (m, n:rNat){(rlt m n)}+{(rlt n m) \/ m=n}.
Intros n m; Generalize (compare_convert_INFERIEUR n m);
 Generalize (compare_convert_SUPERIEUR n m);
 Generalize (compare_convert_EGAL n m); Case (compare n m EGAL).
Intros H' H'0 H'1; Right; Right; Auto.
Intros H' H'0 H'1; Left; Unfold rlt.
Apply convert_compare_INFERIEUR; Auto.
Intros H' H'0 H'1; Right; Left; Unfold rlt.
Apply convert_compare_INFERIEUR; Auto.
Apply H'0; Auto.
Defined.


Definition rmax: rNat -> rNat ->rNat.
Intros n m; Case (rltDec n m); Intros Rlt0.
Exact m.
Exact n.
Defined.

Inductive rExpr: Set :=
     rV: rNat ->rExpr
    | rN: rExpr ->rExpr
    | rNode: rBoolOp -> rExpr -> rExpr ->rExpr .

Fixpoint maxVar[e:rExpr]: rNat :=
   Cases e of
       (rV n) => n
      | (rN p) => (maxVar p)
      | (rNode n p q) => (rmax (maxVar p) (maxVar q))
   end.

