(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Permut.v 9245 2006-10-17 12:53:34Z notin $ i*)

(** Tactics related to (dependent) equality and proof irrelevance. *)

Require Export ProofIrrelevance.
Require Export JMeq.

(** Notation for heterogenous equality. *)

Notation " [ x : X ] = [ y : Y ] " := (@JMeq X x Y y) (at level 0, X at next level, Y at next level).

(** Do something on an heterogeneous equality appearing in the context. *)

Ltac on_JMeq tac := 
  match goal with
    | [ H : @JMeq ?x ?X ?y ?Y |- _ ] => tac H
  end.

(** Try to apply [JMeq_eq] to get back a regular equality when the two types are equal. *)

Ltac simpl_one_JMeq :=
  on_JMeq 
  ltac:(fun H => let H' := fresh "H" in 
    assert (H' := JMeq_eq H) ; clear H ; rename H' into H).

(** Repeat it for every possible hypothesis. *)

Ltac simpl_JMeq := repeat simpl_one_JMeq.

(** Just simplify an h.eq. without clearing it. *)

Ltac simpl_one_dep_JMeq :=
  on_JMeq
  ltac:(fun H => let H' := fresh "H" in 
    assert (H' := JMeq_eq H)).

Require Import Eqdep.

(** Tries to eliminate a call to [eq_rect] (the substitution principle) by any means available. *)

Ltac elim_eq_rect :=
  match goal with
    | [ |- ?t ] => 
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] => 
          let P := fresh "P" in 
            set (P := p); simpl in P ; 
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.

