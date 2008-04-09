(* -*- coq-prog-args: ("-emacs-U" "-top" "Coq.Classes.Morphisms") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Morphism instances for relations.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.

(** Morphisms for relations *)

Instance relation_conjunction_morphism : Morphism (relation_equivalence (A:=A) ==>
  relation_equivalence ==> relation_equivalence) relation_conjunction.
  Proof. firstorder. Qed.

Instance relation_disjunction_morphism : Morphism (relation_equivalence (A:=A) ==>
  relation_equivalence ==> relation_equivalence) relation_disjunction.
  Proof. firstorder. Qed.

(* Predicate equivalence is exactly the same as the pointwise lifting of [iff]. *)

Require Import List.

Lemma predicate_equivalence_pointwise (l : list Type) :
  Morphism (@predicate_equivalence l ==> pointwise_lifting iff l) id.
Proof. do 2 red. unfold predicate_equivalence. auto. Qed.

Lemma predicate_implication_pointwise (l : list Type) :
  Morphism (@predicate_implication l ==> pointwise_lifting impl l) id.
Proof. do 2 red. unfold predicate_implication. auto. Qed.

(** The instanciation at relation allows to rewrite applications of relations [R x y] to [R' x y] *)
(*    when [R] and [R'] are in [relation_equivalence]. *)

Instance relation_equivalence_pointwise :
  Morphism (relation_equivalence ==> pointwise_relation (A:=A) (pointwise_relation (A:=A) iff)) id.
Proof. intro. apply (predicate_equivalence_pointwise (cons A (cons A nil))). Qed.

Instance subrelation_pointwise :
  Morphism (subrelation ==> pointwise_relation (A:=A) (pointwise_relation (A:=A) impl)) id.
Proof. intro. apply (predicate_implication_pointwise (cons A (cons A nil))). Qed.
