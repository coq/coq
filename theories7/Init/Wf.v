(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.
V7only [Unset Implicit Arguments.].

(*i $Id$ i*)

(** This module proves the validity of
    - well-founded recursion (also called course of values)
    - well-founded induction

   from a well-founded ordering on a given set *)

Require Notations.
Require Logic.
Require Datatypes.

(** Well-founded induction principle on Prop *)

Chapter Well_founded.

 Variable A : Set.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)

 Inductive  Acc : A -> Prop 
    := Acc_intro : (x:A)((y:A)(R y x)->(Acc y))->(Acc x).

 Lemma Acc_inv : (x:A)(Acc x) -> (y:A)(R y x) -> (Acc y).
  NewDestruct 1; Trivial.
 Defined.

  (** the informative elimination :
     [let Acc_rec F = let rec wf x = F x wf in wf] *)

 Section AccRecType.
  Variable P : A -> Type.
  Variable F : (x:A)((y:A)(R y x)->(Acc y))->((y:A)(R y x)->(P y))->(P x).

  Fixpoint Acc_rect [x:A;a:(Acc x)] : (P x)
     := (F x (Acc_inv x a) ([y:A][h:(R y x)](Acc_rect y (Acc_inv x a y h)))).

 End AccRecType.

 Definition Acc_rec [P:A->Set] := (Acc_rect P).

 (** A simplified version of Acc_rec(t) *)

 Section AccIter.
  Variable P : A -> Type. 
  Variable F : (x:A)((y:A)(R y x)-> (P y))->(P x).

  Fixpoint Acc_iter [x:A;a:(Acc x)] : (P x)
     := (F x ([y:A][h:(R y x)](Acc_iter y (Acc_inv x a y h)))).

 End AccIter.

 (** A relation is well-founded if every element is accessible *)

 Definition well_founded := (a:A)(Acc a).

 (** well-founded induction on Set and Prop *)

 Hypothesis Rwf : well_founded.

 Theorem well_founded_induction_type : 
        (P:A->Type)((x:A)((y:A)(R y x)->(P y))->(P x))->(a:A)(P a).
 Proof.
  Intros; Apply (Acc_iter P); Auto.
 Defined.

 Theorem well_founded_induction :
        (P:A->Set)((x:A)((y:A)(R y x)->(P y))->(P x))->(a:A)(P a).
 Proof.
  Exact [P:A->Set](well_founded_induction_type P).
 Defined.

 Theorem well_founded_ind : 
         (P:A->Prop)((x:A)((y:A)(R y x)->(P y))->(P x))->(a:A)(P a).
 Proof.
  Exact [P:A->Prop](well_founded_induction_type P).
 Defined.

(** Building fixpoints  *) 

Section FixPoint.

Variable P : A -> Set.
Variable F : (x:A)((y:A)(R y x)->(P y))->(P x).

Fixpoint Fix_F [x:A;r:(Acc x)] : (P x) := 
         (F x [y:A][p:(R y x)](Fix_F y (Acc_inv x r y p))).

Definition fix := [x:A](Fix_F x (Rwf x)).

(** Proof that [well_founded_induction] satisfies the fixpoint equation. 
    It requires an extra property of the functional *)

Hypothesis F_ext : 
  (x:A)(f,g:(y:A)(R y x)->(P y))
  ((y:A)(p:(R y x))((f y p)=(g y p)))->(F x f)=(F x g).

Scheme Acc_inv_dep := Induction for Acc Sort Prop.

Lemma Fix_F_eq
  : (x:A)(r:(Acc x))
    (F x [y:A][p:(R y x)](Fix_F y (Acc_inv x r y p)))=(Fix_F x r).
NewDestruct r using  Acc_inv_dep; Auto.
Qed.

Lemma Fix_F_inv : (x:A)(r,s:(Acc x))(Fix_F x r)=(Fix_F x s).
Intro x; NewInduction (Rwf x); Intros.
Rewrite <- (Fix_F_eq x r); Rewrite <- (Fix_F_eq x s); Intros.
Apply F_ext; Auto.
Qed.


Lemma Fix_eq : (x:A)(fix x)=(F x [y:A][p:(R y x)](fix y)).
Intro x; Unfold fix.
Rewrite <- (Fix_F_eq x).
Apply F_ext; Intros.
Apply Fix_F_inv.
Qed.

End FixPoint.

End Well_founded. 

(** A recursor over pairs *)

Chapter Well_founded_2.

  Variable A,B : Set.
  Variable R : A * B -> A * B -> Prop.

  Variable P : A -> B -> Type. 
  Variable F : (x:A)(x':B)((y:A)(y':B)(R (y,y') (x,x'))-> (P y y'))->(P x x').

  Fixpoint Acc_iter_2 [x:A;x':B;a:(Acc ? R (x,x'))] : (P x x')
     := (F x x' ([y:A][y':B][h:(R (y,y') (x,x'))](Acc_iter_2 y y' (Acc_inv ? ? (x,x') a (y,y') h)))).

  Hypothesis Rwf : (well_founded ? R).

  Theorem well_founded_induction_type_2 : 
     ((x:A)(x':B)((y:A)(y':B)(R (y,y') (x,x'))->(P y y'))->(P x x'))->(a:A)(b:B)(P a b).
  Proof.
   Intros; Apply Acc_iter_2; Auto.
  Defined.

End Well_founded_2.

