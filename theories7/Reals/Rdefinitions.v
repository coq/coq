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
(*                                                       *)
(*********************************************************)

Require Export ZArith_base.

Parameter R:Set.

(* Declare Scope positive_scope with Key R *)
Delimits Scope R_scope with R.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Parameter R0:R.
Parameter R1:R.
Parameter Rplus:R->R->R.
Parameter Rmult:R->R->R.
Parameter Ropp:R->R.
Parameter Rinv:R->R. 
Parameter Rlt:R->R->Prop.    
Parameter up:R->Z.

V8Infix "+" Rplus : R_scope.
V8Infix "*" Rmult : R_scope.
V8Notation "- x" := (Ropp x) : R_scope.
V8Notation "/ x" := (Rinv x) : R_scope.

V8Infix "<"  Rlt : R_scope.

(*i*******************************************************i*)

(**********)
Definition Rgt:R->R->Prop:=[r1,r2:R](Rlt r2 r1).

(**********)
Definition Rle:R->R->Prop:=[r1,r2:R]((Rlt r1 r2)\/(r1==r2)).

(**********)
Definition Rge:R->R->Prop:=[r1,r2:R]((Rgt r1 r2)\/(r1==r2)).

(**********)
Definition Rminus:R->R->R:=[r1,r2:R](Rplus r1 (Ropp r2)).

(**********)
Definition Rdiv:R->R->R:=[r1,r2:R](Rmult r1 (Rinv r2)).

V8Infix "-" Rminus : R_scope.
V8Infix "/" Rdiv : R_scope.

V8Infix "<=" Rle : R_scope.
V8Infix ">=" Rge : R_scope.
V8Infix ">" Rgt : R_scope.

V8Notation "x <= y <= z" := (Rle x y)/\(Rle y z) : R_scope.
V8Notation "x <= y < z" := (Rle x y)/\(Rlt y z) : R_scope.
V8Notation "x < y < z" := (Rlt x y)/\(Rlt y z) : R_scope.
V8Notation "x < y <= z" := (Rlt x y)/\(Rle y z) : R_scope.
