(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements various tactics used to simplify the goals produced by Program,
   which are also generally useful. *)

(** Debugging tactics to show the goal during evaluation. *)

Ltac show_goal := match goal with [ |- ?T ] => idtac T end.

Ltac show_hyp id :=
  match goal with
    | [ H := ?b : ?T |- _ ] =>
      match H with
        | id => idtac id ":=" b ":" T
      end
    | [ H : ?T |- _ ] =>
      match H with
        | id => idtac id  ":"  T
      end
  end.

Ltac show_hyps :=
  try match reverse goal with
        | [ H : ?T |- _ ] => show_hyp H ; fail
      end.

(** The [do] tactic but using a Coq-side nat. *)

Ltac do_nat n tac :=
  match n with
    | 0 => idtac
    | S ?n' => tac ; do_nat n' tac
  end.

(** Do something on the last hypothesis, or fail *)

Ltac on_last_hyp tac :=
  lazymatch goal with [ H : _ |- _ ] => tac H end.

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
  let tac H := let ph := fresh "H" in (destruct H as [H ph]) in
  let tac2 H := let ph := fresh "H" in let ph' := fresh "H" in 
    (destruct H as [H ph ph']) 
  in
  let tacT H := let ph := fresh "X" in (destruct H as [H ph]) in
  let tacT2 H := let ph := fresh "X" in let ph' := fresh "X" in 
    (destruct H as [H ph ph']) 
  in
    match goal with
      | [H : (ex _) |- _] => tac H
      | [H : (sig ?P) |- _ ] => tac H
      | [H : (sigT ?P) |- _ ] => tacT H
      | [H : (ex2 _ _) |- _] => tac2 H
      | [H : (sig2 ?P _) |- _ ] => tac2 H
      | [H : (sigT2 ?P _) |- _ ] => tacT2 H
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

(** Repeatedly reverse the last hypothesis, putting everything in the goal. *)

Ltac reverse := repeat revert_last.

(** Reverse everything up to hypothesis id (not included). *)

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

(** Clear duplicated hypotheses *)

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

(** Try to clear everything except some hyp *)

Ltac clear_except hyp := 
  repeat match goal with [ H : _ |- _ ] =>
           match H with
             | hyp => fail 1
             | _ => clear H
           end
         end.

(** A non-failing subst that substitutes as much as possible. *)

Ltac subst_no_fail :=
  repeat (match goal with
            [ H : ?X = ?Y |- _ ] => subst X || subst Y
          end).

Tactic Notation "subst" "*" := subst_no_fail.

Ltac on_application f tac T :=
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
  end.

(** A variant of [apply] using [refine], doing as much conversion as necessary. *)

Ltac rapply p :=
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _) ||
  refine (p _ _ _ _ _) ||
  refine (p _ _ _ _) ||
  refine (p _ _ _) ||
  refine (p _ _) ||
  refine (p _) ||
  refine p.

(** Tactical [on_call f tac] applies [tac] on any application of [f] in the hypothesis or goal. *)

Ltac on_call f tac :=
  match goal with
    | |- ?T  => on_application f tac T
    | H : ?T |- _  => on_application f tac T
  end.

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object. *)

Ltac destruct_call f :=
  let tac t := (destruct t) in on_call f tac.

Ltac destruct_calls f := repeat destruct_call f.

Ltac destruct_call_in f H :=
  let tac t := (destruct t) in
  let T := type of H in
    on_application f tac T.

Ltac destruct_call_as f l :=
  let tac t := (destruct t as l) in on_call f tac.

Ltac destruct_call_as_in f l H :=
  let tac t := (destruct t as l) in
  let T := type of H in
    on_application f tac T.

Tactic Notation "destruct_call" constr(f) := destruct_call f.

(** Permit to name the results of destructing the call to [f]. *)

Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) :=
  destruct_call_as f l.

(** Specify the hypothesis in which the call occurs as well. *)

Tactic Notation "destruct_call" constr(f) "in" hyp(id) :=
  destruct_call_in f id.

Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) "in" hyp(id) :=
  destruct_call_as_in f l id.

(** A marker for prototypes to destruct. *)

Definition fix_proto {A : Type} (a : A) := a.

Ltac destruct_rec_calls :=
  match goal with
    | [ H : fix_proto _ |- _ ] => destruct_calls H ; clear H
  end.

Ltac destruct_all_rec_calls :=
  repeat destruct_rec_calls ; unfold fix_proto in *.

(** Try to inject any potential constructor equality hypothesis. *)

Ltac autoinjection tac :=
  match goal with
    | [ H : ?f ?a = ?f' ?a' |- _ ] => tac H
  end.

Ltac inject H := progress (inversion H ; subst*; clear_dups) ; clear H.

Ltac autoinjections := repeat (clear_dups ; autoinjection ltac:(inject)).

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

(** A tactic that adds [H:=p:typeof(p)] to the context if no hypothesis of the same type appears in the goal.
   Useful to do saturation using tactics. *)

Ltac add_hypothesis H' p :=
  match type of p with
    ?X =>
    match goal with
      | [ H : X |- _ ] => fail 1
      | _ => set (H':=p) ; try (change p with H') ; clearbody H'
    end
  end.

(** A tactic to replace an hypothesis by another term. *)

Ltac replace_hyp H c :=
  let H' := fresh "H" in
    assert(H' := c) ; clear H ; rename H' into H.

(** A tactic to refine an hypothesis by supplying some of its arguments. *)

Ltac refine_hyp c :=
  let tac H := replace_hyp H c in
    match c with
      | ?H _ => tac H
      | ?H _ _ => tac H
      | ?H _ _ _ => tac H
      | ?H _ _ _ _ => tac H
      | ?H _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ _ _ => tac H
    end.

(** The default simplification tactic used by Program is defined by [program_simpl], sometimes [auto]
   is not enough, better rebind using [Obligation Tactic := tac] in this case,
   possibly using [program_simplify] to use standard goal-cleaning tactics. *)

Ltac program_simplify :=
simpl; intros ; destruct_all_rec_calls ; repeat (destruct_conjs; simpl proj1_sig in * );
  subst*; autoinjections ; try discriminates ;
    try (solve [ red ; intros ; destruct_conjs ; autoinjections ; discriminates ]).

(** Restrict automation to propositional obligations. *)

Ltac program_solve_wf :=
  match goal with
    | |- well_founded _ => auto with *
    | |- ?T => match type of T with Prop => auto end
  end.

Create HintDb program discriminated.

Ltac program_simpl := program_simplify ; try typeclasses eauto 10 with program ; try program_solve_wf.

Obligation Tactic := program_simpl.

Definition obligation (A : Type) {a : A} := a.
