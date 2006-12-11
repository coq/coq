(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)


(*********************************************************)
(**          Definitions for the axiomatization          *)
(*********************************************************)

Require Export ZArith_base.

Parameter R : Set.

(* Declare Scope positive_scope with Key R *)
Delimit Scope R_scope with R.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Parameter R0 : R.
Parameter R1 : R.
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R. 
Parameter Rlt : R -> R -> Prop.    
Parameter up : R -> Z.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Infix "<" := Rlt : R_scope.

(*i*******************************************************i*)

(**********)
Definition Rgt (r1 r2:R) : Prop := (r2 < r1)%R.

(**********)
Definition Rle (r1 r2:R) : Prop := (r1 < r2)%R \/ r1 = r2.

(**********)
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

(**********)
Definition Rminus (r1 r2:R) : R := (r1 + - r2)%R.

(**********)
Definition Rdiv (r1 r2:R) : R := (r1 * / r2)%R.

(**********)

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.

Notation "x <= y <= z" := ((x <= y)%R /\ (y <= z)%R) : R_scope.
Notation "x <= y < z" := ((x <= y)%R /\ (y < z)%R) : R_scope.
Notation "x < y < z" := ((x < y)%R /\ (y < z)%R) : R_scope.
Notation "x < y <= z" := ((x < y)%R /\ (y <= z)%R) : R_scope.
