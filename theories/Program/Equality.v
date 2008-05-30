(* -*- coq-prog-args: ("-emacs-U") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Tactics related to (dependent) equality and proof irrelevance. *)

Require Export ProofIrrelevance.
Require Export JMeq.

Require Import Coq.Program.Tactics.

(** Notation for heterogenous equality. *)

Notation " [ x : X ] = [ y : Y ] " := (@JMeq X x Y y) (at level 0, X at next level, Y at next level).

(** Do something on an heterogeneous equality appearing in the context. *)

Ltac on_JMeq tac := 
  match goal with
    | [ H : @JMeq ?x ?X ?y ?Y |- _ ] => tac H
  end.

(** Try to apply [JMeq_eq] to get back a regular equality when the two types are equal. *)

Ltac simpl_one_JMeq :=
  on_JMeq ltac:(fun H => replace_hyp H (JMeq_eq H)).

(** Repeat it for every possible hypothesis. *)

Ltac simpl_JMeq := repeat simpl_one_JMeq.

(** Just simplify an h.eq. without clearing it. *)

Ltac simpl_one_dep_JMeq :=
  on_JMeq
  ltac:(fun H => let H' := fresh "H" in 
    assert (H' := JMeq_eq H)).

Require Import Eqdep.

(** Simplify dependent equality using sigmas to equality of the second projections if possible. 
   Uses UIP. *)

Ltac simpl_existT :=
  match goal with
    [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => 
    let Hi := fresh H in assert(Hi:=inj_pairT2 _ _ _ _ _ H) ; clear H
  end.

Ltac simpl_existTs := repeat simpl_existT.

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

(** A tactic that tries to remove trivial equality guards in induction hypotheses coming
   from [dependent induction]/[generalize_eqs] invocations. *)


Ltac simpl_IH_eq H :=
  match type of H with
    | @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H (JMeq_refl x))
    | _ -> @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H _ (JMeq_refl x))
    | _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H _ _ (JMeq_refl x))
    | _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H _ _ _ (JMeq_refl x))
    | _ -> _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H _ _ _ _ (JMeq_refl x))
    | _ -> _ -> _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      refine_hyp (H _ _ _ _ _ (JMeq_refl x))
    | ?x = _ -> _ =>
      refine_hyp (H (refl_equal x))
    | _ -> ?x = _ -> _ =>
      refine_hyp (H _ (refl_equal x))
    | _ -> _ -> ?x = _ -> _ =>
      refine_hyp (H _ _ (refl_equal x))
    | _ -> _ -> _ -> ?x = _ -> _ =>
      refine_hyp (H _ _ _ (refl_equal x))
    | _ -> _ -> _ -> _ -> ?x = _ -> _ =>
      refine_hyp (H _ _ _ _ (refl_equal x))
    | _ -> _ -> _ -> _ -> _ -> ?x = _ -> _ =>
      refine_hyp (H _ _ _ _ _ (refl_equal x))
  end.

Ltac simpl_IH_eqs H := repeat simpl_IH_eq H.

Ltac do_simpl_IHs_eqs := 
  match goal with
    | [ H : context [ @JMeq _ _ _ _ -> _ ] |- _ ] => progress (simpl_IH_eqs H)
    | [ H : context [ _ = _ -> _ ] |- _ ] => progress (simpl_IH_eqs H)
  end.

Ltac simpl_IHs_eqs := repeat do_simpl_IHs_eqs.

Ltac simpl_depind := subst* ; autoinjections ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simpl_IHs_eqs.

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to 
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

(** The [do_depind] higher-order tactic takes an induction tactic as argument and an hypothesis 
   and starts a dependent induction using this tactic. *)

Ltac do_depind tac H :=
  generalize_eqs H ; tac H ; repeat progress simpl_depind.

(** Calls [destruct] on the generalized hypothesis, results should be similar to inversion. *)

Tactic Notation "dependent" "destruction" ident(H) := 
  do_depind ltac:(fun H => destruct H ; intros) H ; subst*.

Tactic Notation "dependent" "destruction" ident(H) "using" constr(c) := 
  do_depind ltac:(fun H => destruct H using c ; intros) H.

(** Then we have wrappers for usual calls to induction. One can customize the induction tactic by 
   writting another wrapper calling do_depind. *)

Tactic Notation "dependent" "induction" ident(H) := 
  do_depind ltac:(fun H => induction H ; intros) H.

Tactic Notation "dependent" "induction" ident(H) "using" constr(c) := 
  do_depind ltac:(fun H => induction H using c ; intros) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depind ltac:(fun H => generalize l ; clear l ; induction H ; intros) H.

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depind ltac:(fun H => generalize l ; clear l ; induction H using c ; intros) H.

