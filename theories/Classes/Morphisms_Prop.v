(* -*- coq-prog-args: ("-emacs-U" "-top" "Coq.Classes.Morphisms") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Morphism instances for propositional connectives.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.

(** Standard instances for [not], [iff] and [impl]. *)

(** Logical negation. *)

Program Instance not_impl_morphism :
  Morphism (impl --> impl) not.

Program Instance not_iff_morphism : 
  Morphism (iff ++> iff) not.

(** Logical conjunction. *)

Program Instance and_impl_iff_morphism :
  Morphism (impl ==> impl ==> impl) and.

(* Program Instance and_impl_iff_morphism :  *)
(*   Morphism (impl ==> iff ==> impl) and. *)

(* Program Instance and_iff_impl_morphism :  *)
(*   Morphism (iff ==> impl ==> impl) and. *)

(* Program Instance and_inverse_impl_iff_morphism :  *)
(*   Morphism (inverse impl ==> iff ==> inverse impl) and. *)

(* Program Instance and_iff_inverse_impl_morphism :  *)
(*   Morphism (iff ==> inverse impl ==> inverse impl) and. *)

Program Instance and_iff_morphism : 
  Morphism (iff ==> iff ==> iff) and.

(** Logical disjunction. *)

Program Instance or_impl_iff_morphism : 
  Morphism (impl ==> impl ==> impl) or.

(* Program Instance or_impl_iff_morphism :  *)
(*   Morphism (impl ==> iff ==> impl) or. *)

(* Program Instance or_iff_impl_morphism :  *)
(*   Morphism (iff ==> impl ==> impl) or. *)

(* Program Instance or_inverse_impl_iff_morphism : *)
(*   Morphism (inverse impl ==> iff ==> inverse impl) or. *)

(* Program Instance or_iff_inverse_impl_morphism :  *)
(*   Morphism (iff ==> inverse impl ==> inverse impl) or. *)

Program Instance or_iff_morphism : 
  Morphism (iff ==> iff ==> iff) or.

(** Logical implication [impl] is a morphism for logical equivalence. *)

Program Instance iff_iff_iff_impl_morphism : Morphism (iff ==> iff ==> iff) impl.

(** Morphisms for quantifiers *)

Program Instance {A : Type} => ex_iff_morphism : Morphism (pointwise_relation iff ==> iff) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.     
    split ; intros.
    destruct H0 as [x₁ H₁].
    exists x₁. rewrite H in H₁. assumption.
    
    destruct H0 as [x₁ H₁].
    exists x₁. rewrite H. assumption.
  Qed.

Program Instance {A : Type} => ex_impl_morphism :
  Morphism (pointwise_relation impl ==> impl) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.  
    exists H0. apply H. assumption.
  Qed.

Program Instance {A : Type} => ex_inverse_impl_morphism : 
  Morphism (pointwise_relation (inverse impl) ==> inverse impl) (@ex A).

  Next Obligation.
  Proof.
    unfold pointwise_relation in H.  
    exists H0. apply H. assumption.
  Qed.

Program Instance {A : Type} => all_iff_morphism : 
  Morphism (pointwise_relation iff ==> iff) (@all A).

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance {A : Type} => all_impl_morphism : 
  Morphism (pointwise_relation impl ==> impl) (@all A).
  
  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.

Program Instance {A : Type} => all_inverse_impl_morphism : 
  Morphism (pointwise_relation (inverse impl) ==> inverse impl) (@all A).
  
  Next Obligation.
  Proof.
    unfold pointwise_relation, all in *.
    intuition ; specialize (H x0) ; intuition.
  Qed.
