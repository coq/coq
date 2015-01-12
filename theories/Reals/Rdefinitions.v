(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*********************************************************)
(**          Definitions for the axiomatization          *)
(*********************************************************)

Declare ML Module "r_syntax_plugin".
Require Export ZArith_base.

Parameter R : Set.

(* Declare Scope positive_scope with Key R *)
Delimit Scope R_scope with R.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Local Open Scope R_scope.

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
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

(**********)

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv   : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.
