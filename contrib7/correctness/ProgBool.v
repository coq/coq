(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

Require ZArith.
Require Export Bool_nat.
Require Export Sumbool.

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

