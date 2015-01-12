(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This defines the functor that build consequences of proof-irrelevance *)

Require Export EqdepFacts.

Module Type ProofIrrelevance.

  Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

End ProofIrrelevance.

Module ProofIrrelevanceTheory (M:ProofIrrelevance).

  (** Proof-irrelevance implies uniqueness of reflexivity proofs *)

  Module Eq_rect_eq.
    Lemma eq_rect_eq :
      forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
        x = eq_rect p Q x p h.
    Proof.
      intros; rewrite M.proof_irrelevance with (p1:=h) (p2:=eq_refl p).
      reflexivity.
    Qed.
  End Eq_rect_eq.

  (** Export the theory of injective dependent elimination *)

  Module EqdepTheory := EqdepTheory(Eq_rect_eq).
  Export EqdepTheory.

  Scheme eq_indd := Induction for eq Sort Prop.

  (** We derive the irrelevance of the membership property for subsets *)

  Lemma subset_eq_compat :
    forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
      x = y -> exist P x p = exist P y q.
  Proof.
    intros.
    rewrite M.proof_irrelevance with (p1:=q) (p2:=eq_rect x P p y H).
    elim H using eq_indd.
    reflexivity.
  Qed.

  Lemma subsetT_eq_compat :
    forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
      x = y -> existT P x p = existT P y q.
  Proof.
    intros.
    rewrite M.proof_irrelevance with (p1:=q) (p2:=eq_rect x P p y H).
    elim H using eq_indd.
    reflexivity.
  Qed.

End ProofIrrelevanceTheory.
