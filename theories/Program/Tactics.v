(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This module implements various tactics used to simplify the goals produced by Program. *)

(** Destructs one pair, without care regarding naming. *)

Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

(** Repeateadly destruct pairs. *)

Ltac destruct_pairs := repeat (destruct_one_pair).

(** Destruct one existential package, keeping the name of the hypothesis for the first component. *)

Ltac destruct_one_ex :=
  let tac H := let ph := fresh "H" in destruct H as [H ph] in
    match goal with
      | [H : (ex _) |- _] => tac H
      | [H : (sig ?P) |- _ ] => tac H
      | [H : (ex2 _) |- _] => tac H
    end.

(** Repeateadly destruct existentials. *)

Ltac destruct_exists := repeat (destruct_one_ex).

(** Repeateadly destruct conjunctions and existentials. *)

Ltac destruct_conjs := repeat (destruct_one_pair || destruct_one_ex).

(** Destruct an existential hypothesis [t] keeping its name for the first component 
   and using [Ht] for the second *)

Tactic Notation "destruct" "exist" ident(t) ident(Ht) := destruct t as [t Ht].

(** Destruct a disjunction keeping its name in both subgoals. *)

Tactic Notation "destruct" "or" ident(H) := destruct H as [H|H].

(** Discriminate that also work on a [x <> x] hypothesis. *)

Ltac discriminates :=
  match goal with
    | [ H : ?x <> ?x |- _ ] => elim H ; reflexivity
    | _ => discriminate
  end.

(** Revert the last hypothesis. *)

Ltac revert_last := 
  match goal with
    [ H : _ |- _ ] => revert H
  end.

(** Reapeateadly reverse the last hypothesis, putting everything in the goal. *)

Ltac reverse := repeat revert_last.

(** A non-failing subst that substitutes as much as possible. *)

Tactic Notation "subst" "*" :=
  repeat (match goal with 
            [ H : ?X = ?Y |- _ ] => subst X || subst Y                  
          end).

(** Tactical [on_call f tac] applies [tac] on any application of [f] in the hypothesis or goal. *)
Ltac on_call f tac :=
  match goal with
    | H : ?T |- _  =>
      match T with
        | context [f ?x ?y ?z ?w ?v ?u ?a ?b ?c] => tac (f x y z w v u a b c)
        | context [f ?x ?y ?z ?w ?v ?u ?a ?b] => tac (f x y z w v u a b)
        | context [f ?x ?y ?z ?w ?v ?u ?a] => tac (f x y z w v u a)
        | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
        | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
        | context [f ?x ?y ?z ?w] => tac (f x y z w)
        | context [f ?x ?y ?z] => tac (f x y z)
        | context [f ?x ?y] => tac (f x y) 
        | context [f ?x] => tac (f x)
      end
    | |- ?T  =>
      match T with
        | context [f ?x ?y ?z ?w ?v ?u ?a ?b ?c] => tac (f x y z w v u a b c)
        | context [f ?x ?y ?z ?w ?v ?u ?a ?b] => tac (f x y z w v u a b)
        | context [f ?x ?y ?z ?w ?v ?u ?a] => tac (f x y z w v u a)
        | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
        | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
        | context [f ?x ?y ?z ?w] => tac (f x y z w)
        | context [f ?x ?y ?z] => tac (f x y z)
        | context [f ?x ?y] => tac (f x y)
        | context [f ?x] => tac (f x)
      end
  end.

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object. *)

Ltac destruct_call f :=
  let tac t := destruct t in on_call f tac.

Ltac destruct_call_as f l :=
  let tac t := destruct t as l in on_call f tac.

Tactic Notation "destruct_call" constr(f) := destruct_call f.

(** Permit to name the results of destructing the call to [f]. *)

Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) := destruct_call_as f l.

(** Try to inject any potential constructor equality hypothesis. *)

Ltac autoinjection :=
  let tac H := inversion H ; subst ; clear H in
    match goal with
      | [ H : ?f ?a = ?f' ?a' |- _ ] => tac H
      | [ H : ?f ?a ?b = ?f' ?a' ?b'  |- _ ] => tac H
      | [ H : ?f ?a ?b ?c = ?f' ?a' ?b' ?c' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g= ?f' ?a' ?b' ?c' ?d' ?e' ?g'  |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h= ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h ?i = ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' ?i' |- _ ] => tac H
      | [ H : ?f ?a ?b ?c ?d ?e ?g ?h ?i ?j = ?f' ?a' ?b' ?c' ?d' ?e'?g' ?h' ?i' ?j' |- _ ] => tac H
    end.

Ltac autoinjections := repeat autoinjection.

(** Destruct an hypothesis by first copying it to avoid dependencies. *)

Ltac destruct_nondep H := let H0 := fresh "H" in assert(H0 := H); destruct H0.

(** If bang appears in the goal, it means that we have a proof of False and the goal is solved. *)

Ltac bang :=
  match goal with
    | |- ?x => 
      match x with
        | context [False_rect _ ?p] => elim p
      end
  end.
 
(** A tactic to show contradiction by first asserting an automatically provable hypothesis. *)
Tactic Notation "contradiction" "by" constr(t) := 
  let H := fresh in assert t as H by auto with * ; contradiction.

(** The default simplification tactic used by Program is defined by [program_simpl], sometimes [auto with *]
   is overkill and slows things down, better rebind using [Obligations Tactic := tac] in this case, 
   possibly using [program_simplify] to use standard goal-cleaning tactics. *)

Ltac program_simplify :=
  simpl ; intros ; destruct_conjs ; simpl proj1_sig in * ; subst* ; try autoinjection ; try discriminates ;
    try (solve [ red ; intros ; destruct_conjs ; try autoinjection ; discriminates ]).

Ltac program_simpl := program_simplify ; auto with *.
