(* $Id$ *)


(*********************************************************)
(*           Definitions for the axiomatization          *)
(*                                                       *)
(*********************************************************)

Require Export ZArith.
Require Export TypeSyntax.

Parameter R:Type.
Parameter R0:R.
Parameter R1:R.
Parameter Rplus:R->R->R.
Parameter Rmult:R->R->R.
Parameter Ropp:R->R.
Parameter Rinv:R->R. 
Parameter Rlt:R->R->Prop.    
Parameter up:R->Z.
(*********************************************************)

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
