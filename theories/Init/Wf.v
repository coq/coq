(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This module proves the validity of
    - well-founded recursion (also called course of values)
    - well-founded induction
   from a well-founded ordering on a given set *)

Require Export Logic.
Require Export LogicSyntax.

(* Well-founded induction principle on Prop *)

Chapter Well_founded.

 Variable A : Set.
 Variable R : A -> A -> Prop.

 (* The accessibility predicate is defined to be non-informative *)

 Inductive  Acc : A -> Prop 
    := Acc_intro : (x:A)((y:A)(R y x)->(Acc y))->(Acc x).

 Lemma Acc_inv : (x:A)(Acc x) -> (y:A)(R y x) -> (Acc y).
  Destruct 1; Trivial.
 Defined.

  (* the informative elimination :
     [let Acc_rec F = let rec wf x = F x wf in wf] *)

 Section AccRec.
  Variable P : A -> Set.
  Variable F : (x:A)((y:A)(R y x)->(Acc y))->((y:A)(R y x)->(P y))->(P x).

  Fixpoint Acc_rec [x:A;a:(Acc x)] : (P x)
     := (F x (Acc_inv x a) ([y:A][h:(R y x)](Acc_rec y (Acc_inv x a y h)))).

 End AccRec.

 (* A relation is well-founded if every element is accessible *)

 Definition well_founded := (a:A)(Acc a).

 (* well-founded induction on Set and Prop *)

 Hypothesis Rwf : well_founded.

 Theorem well_founded_induction : 
        (P:A->Set)((x:A)((y:A)(R y x)->(P y))->(P x))->(a:A)(P a).
 Proof.
  Intros; Apply (Acc_rec P); Auto.
 Save.

  Theorem well_founded_ind : 
         (P:A->Prop)((x:A)((y:A)(R y x)->(P y))->(P x))->(a:A)(P a).
   Proof.
    Intros; Apply (Acc_ind P); Auto.
   Qed.

(* Building fixpoints  *) 

Section FixPoint.

Variable P : A -> Set.
Variable F : (x:A)((y:A)(R y x)->(P y))->(P x).

Fixpoint Fix_F [x:A;r:(Acc x)] : (P x) := 
         (F x [y:A][p:(R y x)](Fix_F y (Acc_inv x r y p))).

Definition fix := [x:A](Fix_F x (Rwf x)).

(* Proof that [well_founded_induction] satisfies the fixpoint equation. 
   It requires an extra property of the functional *)

Hypothesis F_ext : 
  (x:A)(f,g:(y:A)(R y x)->(P y))
  ((y:A)(p:(R y x))((f y p)=(g y p)))->(F x f)=(F x g).

Scheme Acc_inv_dep := Induction for Acc Sort Prop.

Lemma Fix_F_eq
  : (x:A)(r:(Acc x))
    (F x [y:A][p:(R y x)](Fix_F y (Acc_inv x r y p)))=(Fix_F x r).
Intros x r; Elim r using  Acc_inv_dep; Auto.
Save.

Lemma Fix_F_inv : (x:A)(r,s:(Acc x))(Fix_F x r)=(Fix_F x s).
Intro x; Elim (Rwf x); Intros.
Case (Fix_F_eq x0 r); Case (Fix_F_eq x0 s); Intros.
Apply F_ext; Auto.
Save.


Lemma fix_eq : (x:A)(fix x)=(F x [y:A][p:(R y x)](fix y)).
Intro; Unfold fix.
Case (Fix_F_eq x).
Apply F_ext; Intros.
Apply Fix_F_inv.
Save.

End FixPoint.

End Well_founded. 
