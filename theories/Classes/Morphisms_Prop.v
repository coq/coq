(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

Program Instance not_impl_morphism :
  Proper (impl --> impl) not | 1.

Program Instance not_iff_morphism :
  Proper (iff ++> iff) not.

(** Logical conjunction. *)

Program Instance and_impl_morphism :
  Proper (impl ==> impl ==> impl) and | 1.

Program Instance and_iff_morphism :
  Proper (iff ==> iff ==> iff) and.

(** Logical disjunction. *)

Program Instance or_impl_morphism :
  Proper (impl ==> impl ==> impl) or | 1.

Program Instance or_iff_morphism :
  Proper (iff ==> iff ==> iff) or.

(** Logical implication [impl] is a morphism for logical equivalence. *)

Program Instance iff_iff_iff_impl_morphism : Proper (iff ==> iff ==> iff) impl.

(** Morphisms for quantifiers *)

Program Instance ex_iff_morphism {A : Type} : Proper (pointwise_relation A iff ==> iff) (@ex A).

Program Instance ex_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@ex A) | 1.

Program Instance ex_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@ex A) | 1.

Program Instance all_iff_morphism {A : Type} :
  Proper (pointwise_relation A iff ==> iff) (@all A).

Program Instance all_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@all A) | 1.

Program Instance all_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation A (flip impl) ==> flip impl) (@all A) | 1.

(** Equivalent points are simultaneously accessible or not *)

Instance Acc_pt_morphism {A:Type}(E R : A->A->Prop)
 `(Equivalence _ E) `(Proper _ (E==>E==>iff) R) :
 Proper (E==>iff) (Acc R).
Proof.
 apply proper_sym_impl_iff; auto with *.
 intros x y EQ WF. apply Acc_intro; intros z Hz.
rewrite <- EQ in Hz. now apply Acc_inv with x.
Qed.

(** Equivalent relations have the same accessible points *)

Instance Acc_rel_morphism {A:Type} :
 Proper (relation_equivalence ==> Logic.eq ==> iff) (@Acc A).
Proof.
 apply proper_sym_impl_iff_2. red; now symmetry. red; now symmetry.
 intros R R' EQ a a' Ha WF. subst a'.
 induction WF as [x _ WF']. constructor.
 intros y Ryx. now apply WF', EQ.
Qed.

(** Equivalent relations are simultaneously well-founded or not *)

Instance well_founded_morphism {A : Type} :
 Proper (relation_equivalence ==> iff) (@well_founded A).
Proof.
 unfold well_founded. solve_proper.
Qed.
