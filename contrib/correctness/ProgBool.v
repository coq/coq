(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

Require Export Compare_dec.
Require Export Peano_dec.
Require ZArith.
Require Sumbool.

(* Programs use the booleans of type "bool", so we tranform any decidability
 * proof, in type sumbool, into a function returning a boolean with the
 * correct specification, through the following function:
 *)

Definition bool_of_sumbool : 
  (A,B:Prop) {A}+{B} -> { b:bool | if b then A else B }.
Proof.
Intros A B H.
Elim H; [ Intro; Exists true; Assumption
        | Intro; Exists false; Assumption ].
Save.

Definition annot_bool :
  (b:bool) { b':bool | if b' then b=true else b=false }.
Proof.
Intro b.
Exists b. Case b; Trivial.
Save.


(* Logical connectives *)

Definition spec_and := [A,B,C,D:Prop][b:bool]if b then A /\ C else B \/ D.

Definition prog_bool_and :
  (Q1,Q2:bool->Prop) (sig bool Q1) -> (sig bool Q2)
  -> { b:bool | if b then (Q1 true) /\ (Q2 true)
                     else (Q1 false) \/ (Q2 false) }.
Proof.
Intros Q1 Q2 H1 H2.
Elim H1. Intro b1. Elim H2. Intro b2. 
Case b1; Case b2; Intros.
Exists true; Auto.
Exists false; Auto. Exists false; Auto. Exists false; Auto.
Save.

Definition spec_or := [A,B,C,D:Prop][b:bool]if b then A \/ C else B /\ D.

Definition prog_bool_or :
  (Q1,Q2:bool->Prop) (sig bool Q1) -> (sig bool Q2)
  -> { b:bool | if b then (Q1 true) \/ (Q2 true)
                     else (Q1 false) /\ (Q2 false) }.
Proof.
Intros Q1 Q2 H1 H2.
Elim H1. Intro b1. Elim H2. Intro b2. 
Case b1; Case b2; Intros.
Exists true; Auto. Exists true; Auto. Exists true; Auto.
Exists false; Auto.
Save.

Definition spec_not:= [A,B:Prop][b:bool]if b then B else A.

Definition prog_bool_not :
  (Q:bool->Prop) (sig bool Q)
  -> { b:bool | if b then (Q false) else (Q true) }.
Proof.
Intros Q H.
Elim H. Intro b.
Case b; Intro.
Exists false; Auto. Exists true; Auto.
Save.


(* Application: the decidability of equality and order relations over
 * type Z give some boolean functions with the adequate specification.
 * For instance, Z_lt_ge_bool has type:
 * 
 *        (x,y:Z){b:bool | if b then `x < y` else `x >= y`}
 *)

Definition Z_lt_ge_bool := [x,y:Z](bool_of_sumbool ? ? (Z_lt_ge_dec x y)).
Definition Z_ge_lt_bool := [x,y:Z](bool_of_sumbool ? ? (Z_ge_lt_dec x y)).

Definition Z_le_gt_bool := [x,y:Z](bool_of_sumbool ? ? (Z_le_gt_dec x y)).
Definition Z_gt_le_bool := [x,y:Z](bool_of_sumbool ? ? (Z_gt_le_dec x y)).

Definition Z_eq_bool := [x,y:Z](bool_of_sumbool ? ? (Z_eq_dec x y)).
Definition Z_noteq_bool := [x,y:Z](bool_of_sumbool ? ? (Z_noteq_dec x y)).

Definition Zeven_odd_bool := [x:Z](bool_of_sumbool ? ? (Zeven_odd_dec x)).

(* ... and similarly for type nat *)

Definition notzerop := [n:nat] (sumbool_not ? ? (zerop n)).
Definition lt_ge_dec : (x,y:nat){(lt x y)}+{(ge x y)} := 
  [n,m:nat] (sumbool_not ? ? (le_lt_dec m n)).

Definition nat_lt_ge_bool := 
  [x,y:nat](bool_of_sumbool ? ? (lt_ge_dec x y)).
Definition nat_ge_lt_bool := 
  [x,y:nat](bool_of_sumbool ? ? (sumbool_not ? ? (lt_ge_dec x y))).

Definition nat_le_gt_bool := 
  [x,y:nat](bool_of_sumbool ? ? (le_gt_dec x y)).
Definition nat_gt_le_bool := 
  [x,y:nat](bool_of_sumbool ? ? (sumbool_not ? ? (le_gt_dec x y))).

Definition nat_eq_bool :=
  [x,y:nat](bool_of_sumbool ? ? (eq_nat_dec x y)).
Definition nat_noteq_bool := 
  [x,y:nat](bool_of_sumbool ? ? (sumbool_not ? ? (eq_nat_dec x y))).

Definition zerop_bool := [x:nat](bool_of_sumbool ? ? (zerop x)).
Definition notzerop_bool := [x:nat](bool_of_sumbool ? ? (notzerop x)).
