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

(** Rewrite using uniqueness of indentity proofs [H = refl_equal X]. *)

Ltac simpl_uip :=
  match goal with
    [ H : ?X = ?X |- _ ] => rewrite (UIP_refl _ _ H) in *; clear H
  end.

(** Simplify equalities appearing in the context and goal. *)

Ltac simpl_eq := simpl ; repeat (elim_eq_rect ; simpl) ; repeat (simpl_uip ; simpl).

(** Try to abstract a proof of equality, if no proof of the same equality is present in the context. *)

Ltac abstract_eq_hyp H' p := 
  let ty := type of p in
  let tyred := eval simpl in ty in
    match tyred with  
      ?X = ?Y => 
      match goal with 
        | [ H : X = Y |- _ ] => fail 1
        | _ => set (H':=p) ; try (change p with H') ; clearbody H' ; simpl in H'
      end
    end.

(** Apply the tactic tac to proofs of equality appearing as coercion arguments. 
   Just redefine this tactic (using [Ltac on_coerce_proof tac ::=]) to handle custom coercion operators.
   *)

Ltac on_coerce_proof tac T :=
  match T with
    | context [ eq_rect _ _ _ _ ?p ] => tac p
  end.
  
Ltac on_coerce_proof_gl tac :=
  match goal with
    [ |- ?T ] => on_coerce_proof tac T
  end.

(** Abstract proofs of equalities of coercions. *)

Ltac abstract_eq_proof := on_coerce_proof_gl ltac:(fun p => let H := fresh "eqH" in abstract_eq_hyp H p).

Ltac abstract_eq_proofs := repeat abstract_eq_proof.
  
(** Factorize proofs, by using proof irrelevance so that two proofs of the same equality 
   in the goal become convertible. *)

Ltac pi_eq_proof_hyp p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
  match tyred with
    ?X = ?Y => 
    match goal with 
      | [ H : X = Y |- _ ] => 
        match p with
          | H => fail 2
          | _ => rewrite (proof_irrelevance (X = Y) p H)
        end
      | _ => fail " No hypothesis with same type "
    end
  end.

(** Factorize proofs of equality appearing as coercion arguments. *)

Ltac pi_eq_proof := on_coerce_proof_gl pi_eq_proof_hyp.

Ltac pi_eq_proofs := repeat pi_eq_proof.

(** The two preceding tactics in sequence. *)

Ltac clear_eq_proofs :=
  abstract_eq_proofs ; pi_eq_proofs.

Hint Rewrite <- eq_rect_eq : refl_id.

(** The refl_id database should be populated with lemmas of the form
   [coerce_* t (refl_equal _) = t]. *)

Ltac rewrite_refl_id := autorewrite with refl_id.

(** Clear the context and goal of equality proofs. *)

Ltac clear_eq_ctx :=
  rewrite_refl_id ; clear_eq_proofs.

(** Reapeated elimination of [eq_rect] applications. 
   Abstracting equalities makes it run much faster than an naive implementation. *)

Ltac simpl_eqs := 
  repeat (elim_eq_rect ; simpl ; clear_eq_ctx).

(** Clear unused reflexivity proofs. *)

Ltac clear_refl_eq := 
  match goal with [ H : ?X = ?X |- _ ] => clear H end.
Ltac clear_refl_eqs := repeat clear_refl_eq.

(** Clear unused equality proofs. *)

Ltac clear_eq := 
  match goal with [ H : _ = _ |- _ ] => clear H end.
Ltac clear_eqs := repeat clear_eq.

(** Combine all the tactics to simplify goals containing coercions. *)

Ltac simplify_eqs := 
  simpl ; simpl_eqs ; clear_eq_ctx ; clear_refl_eqs ;  
    try subst ; simpl ; repeat simpl_uip ; rewrite_refl_id.

(** A tactic to remove trivial equality guards in hypotheses. *)

Ltac simpl_IH_eq H :=
  let tac H' := clear H ; rename H' into H in
  let H' := fresh "H" in
    match type of H with
      | JMeq _ _ -> _ =>
        assert (H' := H (JMeq_refl _)) ; tac H'
      | _ = _ -> _ =>
        assert (H' := H (refl_equal _)) ; tac H'
    end.

Ltac simpl_IH_eqs H := repeat simpl_IH_eq H.

Ltac simpl_IHs_eqs := 
  match goal with
    | [ H : JMeq _ _ -> _ |- _ ] => simpl_IH_eqs H
    | [ H : _ = _ -> _ |- _ ] => simpl_IH_eqs H
  end.

Require Import Coq.Program.Tactics.

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to 
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

Tactic Notation "dependent" "induction" ident(H) := 
  generalize_eqs H ; clear H ; (intros until 1 || intros until H) ; 
    induction H ; intros ; subst* ; try discriminates ; try simpl_IHs_eqs.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  generalize_eqs H ; clear H ; (intros until 1 || intros until H) ; 
    generalize l ; clear l ; induction H ; intros ; subst* ; try discriminates ; try simpl_IHs_eqs.
