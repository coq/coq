(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

Require Import ZArith.
Require Export Bool_nat.
Require Export Sumbool.

Definition annot_bool :
  forall b:bool, {b' : bool | if b' then b = true else b = false}.
Proof.
intro b.
exists b. case b; trivial.
Qed.


(* Logical connectives *)

Definition spec_and (A B C D:Prop) (b:bool) := if b then A /\ C else B \/ D.

Definition prog_bool_and :
  forall Q1 Q2:bool -> Prop,
    sig Q1 ->
    sig Q2 ->
    {b : bool | if b then Q1 true /\ Q2 true else Q1 false \/ Q2 false}.
Proof.
intros Q1 Q2 H1 H2.
elim H1. intro b1. elim H2. intro b2. 
case b1; case b2; intros.
exists true; auto.
exists false; auto. exists false; auto. exists false; auto.
Qed.

Definition spec_or (A B C D:Prop) (b:bool) := if b then A \/ C else B /\ D.

Definition prog_bool_or :
  forall Q1 Q2:bool -> Prop,
    sig Q1 ->
    sig Q2 ->
    {b : bool | if b then Q1 true \/ Q2 true else Q1 false /\ Q2 false}.
Proof.
intros Q1 Q2 H1 H2.
elim H1. intro b1. elim H2. intro b2. 
case b1; case b2; intros.
exists true; auto. exists true; auto. exists true; auto.
exists false; auto.
Qed.

Definition spec_not (A B:Prop) (b:bool) := if b then B else A.

Definition prog_bool_not :
  forall Q:bool -> Prop, sig Q -> {b : bool | if b then Q false else Q true}.
Proof.
intros Q H.
elim H. intro b.
case b; intro.
exists false; auto. exists true; auto.
Qed.
