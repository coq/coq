(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)
(* Cuihtlauac Alvarado - octobre 2000 *)

(** Properties of a boolean equality   *)


Require Export Bool.

Section Bool_eq_dec.

  Variable A : Set.

  Variable beq : A -> A -> bool.

  Variable beq_refl : (x:A)true=(beq x x).

  Variable beq_eq : (x,y:A)true=(beq x y)->x=y.

  Definition beq_eq_true : (x,y:A)x=y->true=(beq x y).
  Proof.
    Intros x y H.
    Case H.
    Apply beq_refl.
  Defined.

  Definition beq_eq_not_false : (x,y:A)x=y->~false=(beq x y).
  Proof.
    Intros x y e.
    Rewrite <- beq_eq_true; Trivial; Discriminate.
  Defined.

  Definition beq_false_not_eq : (x,y:A)false=(beq x y)->~x=y.
  Proof.
    Exact [x,y:A; H:(false=(beq x y)); e:(x=y)](beq_eq_not_false x y e H).
  Defined.

  Definition exists_beq_eq : (x,y:A){b:bool | b=(beq x y)}.
  Proof.
    Intros.
    Exists (beq x y).
    Constructor.
  Defined.

  Definition not_eq_false_beq : (x,y:A)~x=y->false=(beq x y).
  Proof.
    Intros x y H.
    Symmetry.
    Apply not_true_is_false.
    Intro.
    Apply H.
    Apply beq_eq.
    Symmetry.
    Assumption.
  Defined.

  Definition eq_dec : (x,y:A){x=y}+{~x=y}.
  Proof.
    Intros x y; Case (exists_beq_eq x y).
    Intros b; Case b; Intro H.
      Left; Apply beq_eq; Assumption.
      Right; Apply beq_false_not_eq; Assumption.
  Defined.

End Bool_eq_dec.
