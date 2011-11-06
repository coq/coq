(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * [Proper] instances for propositional connectives.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Local Obligation Tactic := simpl_relation.

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

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.
    split ; intros.
    destruct H0 as [x1 H1].
    exists x1. rewrite H in H1. assumption.

    destruct H0 as [x1 H1].
    exists x1. rewrite H. assumption.
  Qed.

Program Instance ex_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@ex A) | 1.

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.
    exists H0. apply H. assumption.
  Qed.

Program Instance ex_inverse_impl_morphism {A : Type} :
  Proper (pointwise_relation A (inverse impl) ==> inverse impl) (@ex A) | 1.

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.
    exists H0. apply H. assumption.
  Qed.

Program Instance all_iff_morphism {A : Type} :
  Proper (pointwise_relation A iff ==> iff) (@all A).

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance all_impl_morphism {A : Type} :
  Proper (pointwise_relation A impl ==> impl) (@all A) | 1.

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance all_inverse_impl_morphism {A : Type} :
  Proper (pointwise_relation A (inverse impl) ==> inverse impl) (@all A) | 1.

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.
