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
  on_JMeq ltac:(fun H => apply JMeq_eq in H).

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

Ltac simpl_eq := simpl ; unfold eq_rec_r, eq_rec ; repeat (elim_eq_rect ; simpl) ; repeat (simpl_uip ; simpl).

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
      specialize (H (JMeq_refl x))
    | _ -> @JMeq _ ?x _ _ -> _ =>
      specialize (H _ (JMeq_refl x))
    | _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      specialize (H _ _ (JMeq_refl x))
    | _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      specialize (H _ _ _ (JMeq_refl x))
    | _ -> _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      specialize (H _ _ _ _ (JMeq_refl x))
    | _ -> _ -> _ -> _ -> _ -> @JMeq _ ?x _ _ -> _ =>
      specialize (H _ _ _ _ _ (JMeq_refl x))
    | ?x = _ -> _ =>
      specialize (H (refl_equal x))
    | _ -> ?x = _ -> _ =>
      specialize (H _ (refl_equal x))
    | _ -> _ -> ?x = _ -> _ =>
      specialize (H _ _ (refl_equal x))
    | _ -> _ -> _ -> ?x = _ -> _ =>
      specialize (H _ _ _ (refl_equal x))
    | _ -> _ -> _ -> _ -> ?x = _ -> _ =>
      specialize (H _ _ _ _ (refl_equal x))
    | _ -> _ -> _ -> _ -> _ -> ?x = _ -> _ =>
      specialize (H _ _ _ _ _ (refl_equal x))
  end.

Ltac simpl_IH_eqs H := repeat simpl_IH_eq H.

Ltac do_simpl_IHs_eqs := 
  match goal with
    | [ H : context [ @JMeq _ _ _ _ -> _ ] |- _ ] => progress (simpl_IH_eqs H)
    | [ H : context [ _ = _ -> _ ] |- _ ] => progress (simpl_IH_eqs H)
  end.

Ltac simpl_IHs_eqs := repeat do_simpl_IHs_eqs.

(** We split substitution tactics in the two directions depending on which 
   names we want to keep corresponding to the generalization performed by the
   [generalize_eqs] tactic. *)

Ltac subst_left_no_fail :=
  repeat (match goal with 
            [ H : ?X = ?Y |- _ ] => subst X
          end).

Ltac subst_right_no_fail :=
  repeat (match goal with 
            [ H : ?X = ?Y |- _ ] => subst Y
          end).

Ltac inject_left H :=
  progress (inversion H ; subst_left_no_fail ; clear_dups) ; clear H.

Ltac inject_right H :=
  progress (inversion H ; subst_right_no_fail ; clear_dups) ; clear H.

Ltac autoinjections_left := repeat autoinjection ltac:inject_left.
Ltac autoinjections_right := repeat autoinjection ltac:inject_right.

Ltac simpl_depind := subst_no_fail ; autoinjections ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simpl_IHs_eqs.

Ltac simpl_depind_l := subst_left_no_fail ; autoinjections_left ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simpl_IHs_eqs.

Ltac simpl_depind_r := subst_right_no_fail ; autoinjections_right ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simpl_IHs_eqs.

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to 
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

(** The [do_depind] higher-order tactic takes an induction tactic as argument and an hypothesis 
   and starts a dependent induction using this tactic. *)

Ltac do_depind tac H :=
  generalize_eqs_vars H ; tac H ; repeat progress simpl_depind_r ; subst_left_no_fail.

(** A variant where generalized variables should be given by the user. *)

Ltac do_depind' tac H :=
  generalize_eqs H ; tac H ; repeat progress simpl_depind_l ; subst_right_no_fail.

(** Calls [destruct] on the generalized hypothesis, results should be similar to inversion.
   By default, we don't try to generalize the hyp by its variable indices.  *)

Tactic Notation "dependent" "destruction" ident(H) := 
  do_depind' ltac:(fun hyp => destruct hyp ; intros) H.

Tactic Notation "dependent" "destruction" ident(H) "using" constr(c) := 
  do_depind' ltac:(fun hyp => destruct hyp using c ; intros) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depind' ltac:(fun hyp => revert l ; destruct hyp ; intros) H.

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depind' ltac:(fun hyp => revert l ; destruct hyp using c ; intros) H.

(** Then we have wrappers for usual calls to induction. One can customize the induction tactic by 
   writting another wrapper calling do_depind. We suppose the hyp has to be generalized before
   calling [induction]. *)

Tactic Notation "dependent" "induction" ident(H) := 
  do_depind ltac:(fun hyp => induction hyp ; intros) H.

Tactic Notation "dependent" "induction" ident(H) "using" constr(c) := 
  do_depind ltac:(fun hyp => induction hyp using c ; intros) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depind' ltac:(fun hyp => generalize l ; clear l ; induction hyp ; intros) H.

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depind' ltac:(fun hyp => generalize l ; clear l ; induction hyp using c ; intros) H.

(** Support for the [Equations] command.
   These tactics implement the necessary machinery to solve goals produced by the 
   [Equations] command relative to dependent pattern-matching. 
   It is completely inspired from the "Eliminating Dependent Pattern-Matching" paper by
   Goguen, McBride and McKinna.
   
*)

(** Lemmas used by the simplifier, mainly rephrasings of [eq_rect], [eq_ind]. *)

Lemma solution_left : Π A (B : A -> Type) (t : A), B t -> (Π x, x = t -> B x).
Proof. intros; subst; assumption. Defined.

Lemma solution_right : Π A (B : A -> Type) (t : A), B t -> (Π x, t = x -> B x).
Proof. intros; subst; assumption. Defined.

Lemma deletion : Π A B (t : A), B -> (t = t -> B).
Proof. intros; assumption. Defined.

Lemma simplification_heq : Π A B (x y : A), (x = y -> B) -> (JMeq x y -> B).
Proof. intros; apply X; apply (JMeq_eq H). Defined.

Lemma simplification_existT : Π A (P : A -> Type) B  (p : A) (x y : P p),
  (x = y -> B) -> (existT P p x = existT P p y -> B).
Proof. intros. apply X. apply inj_pair2. exact H. Defined.

(** This hint database and the following tactic can be used with [autosimpl] to 
   unfold everything to [eq_rect]s. *)

Hint Unfold solution_left solution_right deletion simplification_heq simplification_existT : equations.
Hint Unfold eq_rect_r eq_rec eq_ind : equations.

(** Simply unfold as much as possible. *)

Ltac unfold_equations := repeat progress autosimpl with equations.

(** The tactic [simplify_equations] is to be used when a program generated using [Equations] 
   is in the goal. It simplifies it as much as possible, possibly using [K] if needed. *) 

Ltac simplify_equations := repeat (unfold_equations ; simplify_eqs). 

(** Using these we can make a simplifier that will perform the unification 
   steps needed to put the goal in normalised form (provided there are only
   constructor forms). Compare with the lemma 16 of the paper.
   We don't have a [noCycle] procedure yet. *) 

Ltac simplify_one_dep_elim_term c :=
  match c with
    | @JMeq ?A ?a ?A ?b -> _ => refine (simplification_heq _ _ _ _ _)
    | ?t = ?t -> _ => intros _
    | eq (existT ?P ?p _) (existT ?P ?p _) -> _ => refine (simplification_existT _ _ _ _ _ _ _)
    | ?f ?x = ?f ?y -> _ => let H := fresh in intros H ; injection H ; clear H
    | ?x = ?y -> _ =>
      (let hyp := fresh in intros hyp ; 
        move dependent hyp before x ; 
          generalize dependent x ; refine (solution_left _ _ _ _) ; intros until 0) ||
      (let hyp := fresh in intros hyp ; 
        move dependent hyp before y ; 
          generalize dependent y ; refine (solution_right _ _ _ _) ; intros until 0)
    | ?t = ?u -> _ => let hyp := fresh in
      intros hyp ; elimtype False ; discriminate
    | _ => intro
  end.

Ltac simplify_one_dep_elim :=
  match goal with
    | [ |- ?gl ] => simplify_one_dep_elim_term gl
  end.

(** Repeat until no progress is possible. By construction, it should leave the goal with
   no remaining equalities generated by the [generalize_eqs] tactic. *)

Ltac simplify_dep_elim := repeat simplify_one_dep_elim.

(** To dependent elimination on some hyp. *)

Ltac depelim id :=
  generalize_eqs id ; destruct id ; simplify_dep_elim.

(** Do dependent elimination of the last hypothesis, but not simplifying yet
   (used internally). *)

Ltac destruct_last :=
  on_last_hyp ltac:(fun id => simpl in id ; generalize_eqs id ; destruct id).

(** The rest is support tactics for the [Equations] command. *)

(** Do as much as possible to apply a method, trying to get the arguments right. *)

Ltac try_intros m :=
  (eapply m ; eauto) || (intro ; try_intros m).

(** To solve a goal by inversion on a particular target. *)

Ltac solve_empty target :=
  do_nat target intro ; elimtype False ; destruct_last ; simplify_dep_elim.

Ltac simplify_method H := clear H ; simplify_dep_elim ; reverse.

(** Solving a method call: we must refine the goal until the body 
   can be applied or just solve it by splitting on an empty family member. *)
    
Ltac solve_method rec :=
  match goal with
    | [ H := ?body : nat |- _ ] => simplify_method H ; solve_empty body
    | [ H := ?body |- _ ] => simplify_method H ; rec ; try_intros body
  end.

(** Impossible cases, by splitting on a given target. *)

Ltac solve_split :=
  match goal with 
    | [ |- let split := ?x : nat in _ ] => intros _ ; solve_empty x
  end.

(** If defining recursive functions, the prototypes come first. *)

Ltac intro_prototypes :=
  match goal with 
    | [ |- Π x : _, _ ] => intro ; intro_prototypes
    | _ => idtac
  end.

Ltac nonrec_equations := 
  solve [solve_equations (solve_method idtac)] || solve [ solve_split ]
    || fail "Unnexpected equations goal".

Ltac recursive_equations :=
  solve [solve_equations (solve_method ltac:intro)] || solve [ solve_split ] 
    || fail "Unnexpected recursive equations goal".

(** The [equations] tactic is the toplevel tactic for solving goals generated
   by [Equations]. *)

Ltac equations :=
  match goal with 
    | [ |- Π x : _, _ ] => intro ; recursive_equations
    | _ => nonrec_equations
  end.
