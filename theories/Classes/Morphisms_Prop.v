(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Program.Basics.

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

#[global]
Instance not_impl_morphism :
  Proper (impl --> impl) not | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance not_iff_morphism :
  Proper (iff ++> iff) not.
Proof. firstorder idtac. Qed.

(** Logical conjunction. *)

#[global]
Instance and_impl_morphism :
  Proper (impl ==> impl ==> impl) and | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance and_iff_morphism :
  Proper (iff ==> iff ==> iff) and.
Proof. firstorder idtac. Qed.

(** Logical disjunction. *)

#[global]
Instance or_impl_morphism :
  Proper (impl ==> impl ==> impl) or | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance or_iff_morphism :
  Proper (iff ==> iff ==> iff) or.
Proof. firstorder idtac. Qed.

(** Logical implication [impl] is a morphism for logical equivalence. *)

#[global]
Instance iff_iff_iff_impl_morphism : Proper (iff ==> iff ==> iff) impl.
Proof. firstorder idtac. Qed.

(** Morphisms for quantifiers *)

#[global]
Instance ex_iff_morphism {A : Type} : Proper (pointwise_relation A iff ==> iff) (@ex A).
Proof. firstorder idtac. Qed.

#[global]
Instance ex_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@ex A) | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance ex_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@ex A) | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance all_iff_morphism {A : Type} :
  Proper (pointwise_relation A iff ==> iff) (@all A).
Proof. firstorder idtac. Qed.

#[global]
Instance all_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@all A) | 1.
Proof. firstorder idtac. Qed.

#[global]
Instance all_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@all A) | 1.
Proof. firstorder idtac. Qed.

(** Equivalent points are simultaneously accessible or not *)

#[global]
Instance Acc_pt_morphism {A:Type}(E R : A->A->Prop)
 `(Equivalence _ E) `(Proper _ (E==>E==>iff) R) :
 Proper (E==>iff) (Acc R).
Proof.
  apply proper_sym_impl_iff.
  - auto with relations.
  - intros x y EQ WF. apply Acc_intro; intros z Hz.
    rewrite <- EQ in Hz. now apply Acc_inv with x.
Qed.

(** Equivalent relations have the same accessible points *)

#[global]
Instance Acc_rel_morphism {A:Type} :
 Proper (relation_equivalence ==> Logic.eq ==> iff) (@Acc A).
Proof.
  apply proper_sym_impl_iff_2.
  - red; now symmetry.
  - red; now symmetry.
  - intros R R' EQ a a' Ha WF. subst a'.
    induction WF as [x _ WF']. constructor.
    intros y Ryx. now apply WF', EQ.
Qed.

(** Equivalent relations are simultaneously well-founded or not *)

#[global]
Instance well_founded_morphism {A : Type} :
 Proper (relation_equivalence ==> iff) (@well_founded A).
Proof.
 unfold well_founded. solve_proper.
Qed.
