(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Bool.

Inductive IfProp [A,B:Prop] : bool-> Prop 
  := Iftrue  : A -> (IfProp A B true)
  |  Iffalse : B -> (IfProp A B false).

Hints Resolve Iftrue Iffalse : bool v62.

Lemma Iftrue_inv : (A,B:Prop)(b:bool) (IfProp A B b) -> b=true -> A.
NewDestruct 1; Intros; Auto with bool.
Case diff_true_false; Auto with bool.
Qed.

Lemma Iffalse_inv : (A,B:Prop)(b:bool) (IfProp A B b) -> b=false -> B.
NewDestruct 1; Intros; Auto with bool.
Case diff_true_false; Trivial with bool.
Qed.

Lemma IfProp_true : (A,B:Prop)(IfProp A B true) -> A.
Intros.
Inversion H.
Assumption.
Qed.

Lemma IfProp_false : (A,B:Prop)(IfProp A B false) -> B.
Intros.
Inversion H.
Assumption.
Qed.

Lemma IfProp_or : (A,B:Prop)(b:bool)(IfProp A B b) -> A\/B.
NewDestruct 1; Auto with bool.
Qed.

Lemma IfProp_sum : (A,B:Prop)(b:bool)(IfProp A B b) -> {A}+{B}.
NewDestruct b; Intro H.
Left; Inversion H; Auto with bool.
Right; Inversion H; Auto with bool.
Qed.
