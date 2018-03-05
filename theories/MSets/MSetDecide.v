(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**************************************************************)
(* MSetDecide.v                                               *)
(*                                                            *)
(* Author: Aaron Bohannon                                     *)
(**************************************************************)

(** This file implements a decision procedure for a certain
    class of propositions involving finite sets.  *)

Require Import Decidable Setoid DecidableTypeEx MSetFacts.

(** First, a version for Weak Sets in functorial presentation *)

Module WDecideOn (E : DecidableType)(Import M : WSetsOn E).
 Module F := MSetFacts.WFactsOn E M.

(** * Overview
    This functor defines the tactic [fsetdec], which will
    solve any valid goal of the form
<<
    forall s1 ... sn,
    forall x1 ... xm,
    P1 -> ... -> Pk -> P
>>
    where [P]'s are defined by the grammar:
<<

P ::=
| Q
| Empty F
| Subset F F'
| Equal F F'

Q ::=
| E.eq X X'
| In X F
| Q /\ Q'
| Q \/ Q'
| Q -> Q'
| Q <-> Q'
| ~ Q
| True
| False

F ::=
| S
| empty
| singleton X
| add X F
| remove X F
| union F F'
| inter F F'
| diff F F'

X ::= x1 | ... | xm
S ::= s1 | ... | sn

>>

The tactic will also work on some goals that vary slightly from
the above form:
- The variables and hypotheses may be mixed in any order and may
  have already been introduced into the context.  Moreover,
  there may be additional, unrelated hypotheses mixed in (these
  will be ignored).
- A conjunction of hypotheses will be handled as easily as
  separate hypotheses, i.e., [P1 /\ P2 -> P] can be solved iff
  [P1 -> P2 -> P] can be solved.
- [fsetdec] should solve any goal if the MSet-related hypotheses
  are contradictory.
- [fsetdec] will first perform any necessary zeta and beta
  reductions and will invoke [subst] to eliminate any Coq
  equalities between finite sets or their elements.
- If [E.eq] is convertible with Coq's equality, it will not
  matter which one is used in the hypotheses or conclusion.
- The tactic can solve goals where the finite sets or set
  elements are expressed by Coq terms that are more complicated
  than variables.  However, non-local definitions are not
  expanded, and Coq equalities between non-variable terms are
  not used.  For example, this goal will be solved:
<<
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g (g x2)) ->
    In x1 s1 ->
    In (g (g x2)) (f s2)
>>
  This one will not be solved:
<<
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g x2) ->
    In x1 s1 ->
    g x2 = g (g x2) ->
    In (g (g x2)) (f s2)
>>
*)

  (** * Facts and Tactics for Propositional Logic
      These lemmas and tactics are in a module so that they do
      not affect the namespace if you import the enclosing
      module [Decide]. *)
  Module MSetLogicalFacts.
    Export Decidable.
    Export Setoid.

    (** ** Lemmas and Tactics About Decidable Propositions *)

    (** ** Propositional Equivalences Involving Negation
        These are all written with the unfolded form of
        negation, since I am not sure if setoid rewriting will
        always perform conversion. *)

    (** ** Tactics for Negations *)

    Tactic Notation "fold" "any" "not" :=
      repeat (
        match goal with
        | H: context [?P -> False] |- _ =>
          fold (~ P) in H
        | |- context [?P -> False] =>
          fold (~ P)
        end).

    (** [push not using db] will pushes all negations to the
        leaves of propositions in the goal, using the lemmas in
        [db] to assist in checking the decidability of the
        propositions involved.  If [using db] is omitted, then
        [core] will be used.  Additional versions are provided
        to manipulate the hypotheses or the hypotheses and goal
        together.

        XXX: This tactic and the similar subsequent ones should
        have been defined using [autorewrite]. However, dealing
        with multiples rewrite sites and side-conditions is
        done more cleverly with the following explicit
        analysis of goals. *)

    Ltac or_not_l_iff P Q tac :=
      (rewrite (or_not_l_iff_1 P Q) by tac) ||
      (rewrite (or_not_l_iff_2 P Q) by tac).

    Ltac or_not_r_iff P Q tac :=
      (rewrite (or_not_r_iff_1 P Q) by tac) ||
      (rewrite (or_not_r_iff_2 P Q) by tac).

    Ltac or_not_l_iff_in P Q H tac :=
      (rewrite (or_not_l_iff_1 P Q) in H by tac) ||
      (rewrite (or_not_l_iff_2 P Q) in H by tac).

    Ltac or_not_r_iff_in P Q H tac :=
      (rewrite (or_not_r_iff_1 P Q) in H by tac) ||
      (rewrite (or_not_r_iff_2 P Q) in H by tac).

    Tactic Notation "push" "not" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff;
      repeat (
        match goal with
        | |- context [True -> False] => rewrite not_true_iff
        | |- context [False -> False] => rewrite not_false_iff
        | |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
        | |- context [(?P -> False) -> (?Q -> False)] =>
            rewrite (contrapositive P Q) by dec
        | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
        | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
        | |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
        | |- context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q)
        | |- context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q)
        | |- context [(?P -> ?Q) -> False] => rewrite (not_imp_iff P Q) by dec
        end);
      fold any not.

    Tactic Notation "push" "not" :=
      push not using core.

    Tactic Notation
      "push" "not" "in" "*" "|-" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff in * |-;
      repeat (
        match goal with
        | H: context [True -> False] |- _ => rewrite not_true_iff in H
        | H: context [False -> False] |- _ => rewrite not_false_iff in H
        | H: context [(?P -> False) -> False] |- _ =>
          rewrite (not_not_iff P) in H by dec
        | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
          rewrite (contrapositive P Q) in H by dec
        | H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
        | H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
        | H: context [(?P -> False) -> ?Q] |- _ =>
          rewrite (imp_not_l P Q) in H by dec
        | H: context [?P \/ ?Q -> False] |- _ => rewrite (not_or_iff P Q) in H
        | H: context [?P /\ ?Q -> False] |- _ => rewrite (not_and_iff P Q) in H
        | H: context [(?P -> ?Q) -> False] |- _ =>
          rewrite (not_imp_iff P Q) in H by dec
        end);
      fold any not.

    Tactic Notation "push" "not" "in" "*" "|-"  :=
      push not in * |- using core.

    Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
      push not using db; push not in * |- using db.
    Tactic Notation "push" "not" "in" "*" :=
      push not in * using core.

    (** A simple test case to see how this works.  *)
    Lemma test_push : forall P Q R : Prop,
      decidable P ->
      decidable Q ->
      (~ True) ->
      (~ False) ->
      (~ ~ P) ->
      (~ (P /\ Q) -> ~ R) ->
      ((P /\ Q) \/ ~ R) ->
      (~ (P /\ Q) \/ R) ->
      (R \/ ~ (P /\ Q)) ->
      (~ R \/ (P /\ Q)) ->
      (~ P -> R) ->
      (~ ((R -> P) \/ (Q -> R))) ->
      (~ (P /\ R)) ->
      (~ (P -> R)) ->
      True.
    Proof.
      intros. push not in *.
       (* note that ~(R->P) remains (since R isnt decidable) *)
      tauto.
    Qed.

    (** [pull not using db] will pull as many negations as
        possible toward the top of the propositions in the goal,
        using the lemmas in [db] to assist in checking the
        decidability of the propositions involved.  If [using
        db] is omitted, then [core] will be used.  Additional
        versions are provided to manipulate the hypotheses or
        the hypotheses and goal together. *)

    Tactic Notation "pull" "not" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff;
      repeat (
        match goal with
        | |- context [True -> False] => rewrite not_true_iff
        | |- context [False -> False] => rewrite not_false_iff
        | |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
        | |- context [(?P -> False) -> (?Q -> False)] =>
          rewrite (contrapositive P Q) by dec
        | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
        | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
        | |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
        | |- context [(?P -> False) /\ (?Q -> False)] =>
          rewrite <- (not_or_iff P Q)
        | |- context [?P -> ?Q -> False] => rewrite <- (not_and_iff P Q)
        | |- context [?P /\ (?Q -> False)] => rewrite <- (not_imp_iff P Q) by dec
        | |- context [(?Q -> False) /\ ?P] =>
          rewrite <- (not_imp_rev_iff P Q) by dec
        end);
      fold any not.

    Tactic Notation "pull" "not" :=
      pull not using core.

    Tactic Notation
      "pull" "not" "in" "*" "|-" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff in * |-;
      repeat (
        match goal with
        | H: context [True -> False] |- _ => rewrite not_true_iff in H
        | H: context [False -> False] |- _ => rewrite not_false_iff in H
        | H: context [(?P -> False) -> False] |- _ =>
          rewrite (not_not_iff P) in H by dec
        | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
          rewrite (contrapositive P Q) in H by dec
        | H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
        | H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
        | H: context [(?P -> False) -> ?Q] |- _ =>
          rewrite (imp_not_l P Q) in H by dec
        | H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
          rewrite <- (not_or_iff P Q) in H
        | H: context [?P -> ?Q -> False] |- _ =>
          rewrite <- (not_and_iff P Q) in H
        | H: context [?P /\ (?Q -> False)] |- _ =>
          rewrite <- (not_imp_iff P Q) in H by dec
        | H: context [(?Q -> False) /\ ?P] |- _ =>
          rewrite <- (not_imp_rev_iff P Q) in H by dec
        end);
      fold any not.

    Tactic Notation "pull" "not" "in" "*" "|-"  :=
      pull not in * |- using core.

    Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
      pull not using db; pull not in * |- using db.
    Tactic Notation "pull" "not" "in" "*" :=
      pull not in * using core.

    (** A simple test case to see how this works.  *)
    Lemma test_pull : forall P Q R : Prop,
      decidable P ->
      decidable Q ->
      (~ True) ->
      (~ False) ->
      (~ ~ P) ->
      (~ (P /\ Q) -> ~ R) ->
      ((P /\ Q) \/ ~ R) ->
      (~ (P /\ Q) \/ R) ->
      (R \/ ~ (P /\ Q)) ->
      (~ R \/ (P /\ Q)) ->
      (~ P -> R) ->
      (~ (R -> P) /\ ~ (Q -> R)) ->
      (~ P \/ ~ R) ->
      (P /\ ~ R) ->
      (~ R /\ P) ->
      True.
    Proof.
      intros. pull not in *. tauto.
    Qed.

  End MSetLogicalFacts.
  Import MSetLogicalFacts.

  (** * Auxiliary Tactics
      Again, these lemmas and tactics are in a module so that
      they do not affect the namespace if you import the
      enclosing module [Decide].  *)
  Module MSetDecideAuxiliary.

    (** ** Generic Tactics
        We begin by defining a few generic, useful tactics. *)

    (** remove logical hypothesis inter-dependencies (fix #2136). *)

    Ltac no_logical_interdep :=
      match goal with
        | H : ?P |- _ =>
          match type of P with
            | Prop =>
              match goal with H' : context [ H ] |- _ => clear dependent H' end
            | _ => fail
          end; no_logical_interdep
        | _ => idtac
      end.

    Ltac abstract_term t :=
      tryif (is_var t) then fail "no need to abstract a variable"
      else (let x := fresh "x" in set (x := t) in *; try clearbody x).

    Ltac abstract_elements :=
      repeat
        (match goal with
           | |- context [ singleton ?t ] => abstract_term t
           | _ : context [ singleton ?t ] |- _ => abstract_term t
           | |- context [ add ?t _ ] => abstract_term t
           | _ : context [ add ?t _ ] |- _ => abstract_term t
           | |- context [ remove ?t _ ] => abstract_term t
           | _ : context [ remove ?t _ ] |- _ => abstract_term t
           | |- context [ In ?t _ ] => abstract_term t
           | _ : context [ In ?t _ ] |- _ => abstract_term t
         end).

    (** [prop P holds by t] succeeds (but does not modify the
        goal or context) if the proposition [P] can be proved by
        [t] in the current context.  Otherwise, the tactic
        fails. *)
    Tactic Notation "prop" constr(P) "holds" "by" tactic(t) :=
      let H := fresh in
      assert P as H by t;
      clear H.

    (** This tactic acts just like [assert ... by ...] but will
        fail if the context already contains the proposition. *)
    Tactic Notation "assert" "new" constr(e) "by" tactic(t) :=
      match goal with
      | H: e |- _ => fail 1
      | _ => assert e by t
      end.

    (** [subst++] is similar to [subst] except that
        - it never fails (as [subst] does on recursive
          equations),
        - it substitutes locally defined variable for their
          definitions,
        - it performs beta reductions everywhere, which may
          arise after substituting a locally defined function
          for its definition.
        *)
    Tactic Notation "subst" "++" :=
      repeat (
        match goal with
        | x : _ |- _ => subst x
        end);
      cbv zeta beta in *.

    (** [decompose records] calls [decompose record H] on every
        relevant hypothesis [H]. *)
    Tactic Notation "decompose" "records" :=
      repeat (
        match goal with
        | H: _ |- _ => progress (decompose record H); clear H
        end).

    (** ** Discarding Irrelevant Hypotheses
        We will want to clear the context of any
        non-MSet-related hypotheses in order to increase the
        speed of the tactic.  To do this, we will need to be
        able to decide which are relevant.  We do this by making
        a simple inductive definition classifying the
        propositions of interest. *)

    Inductive MSet_elt_Prop : Prop -> Prop :=
    | eq_Prop : forall (S : Type) (x y : S),
        MSet_elt_Prop (x = y)
    | eq_elt_prop : forall x y,
        MSet_elt_Prop (E.eq x y)
    | In_elt_prop : forall x s,
        MSet_elt_Prop (In x s)
    | True_elt_prop :
        MSet_elt_Prop True
    | False_elt_prop :
        MSet_elt_Prop False
    | conj_elt_prop : forall P Q,
        MSet_elt_Prop P ->
        MSet_elt_Prop Q ->
        MSet_elt_Prop (P /\ Q)
    | disj_elt_prop : forall P Q,
        MSet_elt_Prop P ->
        MSet_elt_Prop Q ->
        MSet_elt_Prop (P \/ Q)
    | impl_elt_prop : forall P Q,
        MSet_elt_Prop P ->
        MSet_elt_Prop Q ->
        MSet_elt_Prop (P -> Q)
    | not_elt_prop : forall P,
        MSet_elt_Prop P ->
        MSet_elt_Prop (~ P).

    Inductive MSet_Prop : Prop -> Prop :=
    | elt_MSet_Prop : forall P,
        MSet_elt_Prop P ->
        MSet_Prop P
    | Empty_MSet_Prop : forall s,
        MSet_Prop (Empty s)
    | Subset_MSet_Prop : forall s1 s2,
        MSet_Prop (Subset s1 s2)
    | Equal_MSet_Prop : forall s1 s2,
        MSet_Prop (Equal s1 s2).

    (** Here is the tactic that will throw away hypotheses that
        are not useful (for the intended scope of the [fsetdec]
        tactic). *)
    Hint Constructors MSet_elt_Prop MSet_Prop : MSet_Prop.
    Ltac discard_nonMSet :=
      repeat (
        match goal with
        | H : context [ @Logic.eq ?T ?x ?y ] |- _ =>
          tryif (change T with E.t in H) then fail
          else tryif (change T with t in H) then fail
          else clear H
        | H : ?P |- _ =>
          tryif prop (MSet_Prop P) holds by
            (auto 100 with MSet_Prop)
          then fail
          else clear H
        end).

    (** ** Turning Set Operators into Propositional Connectives
        The lemmas from [MSetFacts] will be used to break down
        set operations into propositional formulas built over
        the predicates [In] and [E.eq] applied only to
        variables.  We are going to use them with [autorewrite].
        *)

    Hint Rewrite
      F.empty_iff F.singleton_iff F.add_iff F.remove_iff
      F.union_iff F.inter_iff F.diff_iff
    : set_simpl.

    Lemma eq_refl_iff (x : E.t) : E.eq x x <-> True.
    Proof.
     now split.
    Qed.

    Hint Rewrite eq_refl_iff : set_eq_simpl.

    (** ** Decidability of MSet Propositions *)

    (** [In] is decidable. *)
    Lemma dec_In : forall x s,
      decidable (In x s).
    Proof.
      red; intros; generalize (F.mem_iff s x); case (mem x s); intuition.
    Qed.

    (** [E.eq] is decidable. *)
    Lemma dec_eq : forall (x y : E.t),
      decidable (E.eq x y).
    Proof.
      red; intros x y; destruct (E.eq_dec x y); auto.
    Qed.

    (** The hint database [MSet_decidability] will be given to
        the [push_neg] tactic from the module [Negation]. *)
    Hint Resolve dec_In dec_eq : MSet_decidability.

    (** ** Normalizing Propositions About Equality
        We have to deal with the fact that [E.eq] may be
        convertible with Coq's equality.  Thus, we will find the
        following tactics useful to replace one form with the
        other everywhere. *)

    (** The next tactic, [Logic_eq_to_E_eq], mentions the term
        [E.t]; thus, we must ensure that [E.t] is used in favor
        of any other convertible but syntactically distinct
        term. *)
    Ltac change_to_E_t :=
      repeat (
        match goal with
        | H : ?T |- _ =>
          progress (change T with E.t in H);
          repeat (
            match goal with
            | J : _ |- _ => progress (change T with E.t in J)
            | |- _ => progress (change T with E.t)
            end )
        | H : forall x : ?T, _ |- _ =>
          progress (change T with E.t in H);
          repeat (
            match goal with
            | J : _ |- _ => progress (change T with E.t in J)
            | |- _ => progress (change T with E.t)
            end )
       end).

    (** These two tactics take us from Coq's built-in equality
        to [E.eq] (and vice versa) when possible. *)

    Ltac Logic_eq_to_E_eq :=
      repeat (
        match goal with
        | H: _ |- _ =>
          progress (change (@Logic.eq E.t) with E.eq in H)
        | |- _ =>
          progress (change (@Logic.eq E.t) with E.eq)
        end).

    Ltac E_eq_to_Logic_eq :=
      repeat (
        match goal with
        | H: _ |- _ =>
          progress (change E.eq with (@Logic.eq E.t) in H)
        | |- _ =>
          progress (change E.eq with (@Logic.eq E.t))
        end).

    (** This tactic works like the built-in tactic [subst], but
        at the level of set element equality (which may not be
        the convertible with Coq's equality). *)
    Ltac substMSet :=
      repeat (
        match goal with
        | H: E.eq ?x ?x |- _ => clear H
        | H: E.eq ?x ?y |- _ => rewrite H in *; clear H
        end);
      autorewrite with set_eq_simpl in *.

    (** ** Considering Decidability of Base Propositions
        This tactic adds assertions about the decidability of
        [E.eq] and [In] to the context.  This is necessary for
        the completeness of the [fsetdec] tactic.  However, in
        order to minimize the cost of proof search, we should be
        careful to not add more than we need.  Once negations
        have been pushed to the leaves of the propositions, we
        only need to worry about decidability for those base
        propositions that appear in a negated form. *)
    Ltac assert_decidability :=
      (** We actually don't want these rules to fire if the
          syntactic context in the patterns below is trivially
          empty, but we'll just do some clean-up at the
          afterward.  *)
      repeat (
        match goal with
        | H: context [~ E.eq ?x ?y] |- _ =>
          assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
        | H: context [~ In ?x ?s] |- _ =>
          assert new (In x s \/ ~ In x s) by (apply dec_In)
        | |- context [~ E.eq ?x ?y] =>
          assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
        | |- context [~ In ?x ?s] =>
          assert new (In x s \/ ~ In x s) by (apply dec_In)
        end);
      (** Now we eliminate the useless facts we added (because
          they would likely be very harmful to performance). *)
      repeat (
        match goal with
        | _: ~ ?P, H : ?P \/ ~ ?P |- _ => clear H
        end).

    (** ** Handling [Empty], [Subset], and [Equal]
        This tactic instantiates universally quantified
        hypotheses (which arise from the unfolding of [Empty],
        [Subset], and [Equal]) for each of the set element
        expressions that is involved in some membership or
        equality fact.  Then it throws away those hypotheses,
        which should no longer be needed. *)
    Ltac inst_MSet_hypotheses :=
      repeat (
        match goal with
        | H : forall a : E.t, _,
          _ : context [ In ?x _ ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | H : forall a : E.t, _
          |- context [ In ?x _ ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | H : forall a : E.t, _,
          _ : context [ E.eq ?x _ ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | H : forall a : E.t, _
          |- context [ E.eq ?x _ ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | H : forall a : E.t, _,
          _ : context [ E.eq _ ?x ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | H : forall a : E.t, _
          |- context [ E.eq _ ?x ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        end);
      repeat (
        match goal with
        | H : forall a : E.t, _ |- _ =>
          clear H
        end).

    (** ** The Core [fsetdec] Auxiliary Tactics *)

    (** Here is the crux of the proof search.  Recursion through
        [intuition]!  (This will terminate if I correctly
        understand the behavior of [intuition].) *)
    Ltac fsetdec_rec := progress substMSet; intuition fsetdec_rec.

    (** If we add [unfold Empty, Subset, Equal in *; intros;] to
        the beginning of this tactic, it will satisfy the same
        specification as the [fsetdec] tactic; however, it will
        be much slower than necessary without the pre-processing
        done by the wrapper tactic [fsetdec]. *)
    Ltac fsetdec_body :=
      autorewrite with set_eq_simpl in *;
      inst_MSet_hypotheses;
      autorewrite with set_simpl set_eq_simpl in *;
      push not in * using MSet_decidability;
      substMSet;
      assert_decidability;
      auto;
      (intuition fsetdec_rec) ||
      fail 1
        "because the goal is beyond the scope of this tactic".

  End MSetDecideAuxiliary.
  Import MSetDecideAuxiliary.

  (** * The [fsetdec] Tactic
      Here is the top-level tactic (the only one intended for
      clients of this library).  It's specification is given at
      the top of the file. *)
  Ltac fsetdec :=
    (** We first unfold any occurrences of [iff]. *)
    unfold iff in *;
    (** We fold occurrences of [not] because it is better for
        [intros] to leave us with a goal of [~ P] than a goal of
        [False]. *)
    fold any not; intros;
    (** We don't care about the value of elements : complex ones are
        abstracted as new variables (avoiding potential dependencies,
        see bug #2464) *)
    abstract_elements;
    (** We remove dependencies to logical hypothesis. This way,
        later "clear" will work nicely (see bug #2136) *)
    no_logical_interdep;
    (** Now we decompose conjunctions, which will allow the
        [discard_nonMSet] and [assert_decidability] tactics to
        do a much better job. *)
    decompose records;
    discard_nonMSet;
    (** We unfold these defined propositions on finite sets.  If
        our goal was one of them, then have one more item to
        introduce now. *)
    unfold Empty, Subset, Equal in *; intros;
    (** We now want to get rid of all uses of [=] in favor of
        [E.eq].  However, the best way to eliminate a [=] is in
        the context is with [subst], so we will try that first.
        In fact, we may as well convert uses of [E.eq] into [=]
        when possible before we do [subst] so that we can even
        more mileage out of it.  Then we will convert all
        remaining uses of [=] back to [E.eq] when possible.  We
        use [change_to_E_t] to ensure that we have a canonical
        name for set elements, so that [Logic_eq_to_E_eq] will
        work properly.  *)
    change_to_E_t; E_eq_to_Logic_eq; subst++; Logic_eq_to_E_eq;
    (** The next optimization is to swap a negated goal with a
        negated hypothesis when possible.  Any swap will improve
        performance by eliminating the total number of
        negations, but we will get the maximum benefit if we
        swap the goal with a hypotheses mentioning the same set
        element, so we try that first.  If we reach the fourth
        branch below, we attempt any swap.  However, to maintain
        completeness of this tactic, we can only perform such a
        swap with a decidable proposition; hence, we first test
        whether the hypothesis is an [MSet_elt_Prop], noting
        that any [MSet_elt_Prop] is decidable. *)
    pull not using MSet_decidability;
    unfold not in *;
    match goal with
    | H: (In ?x ?r) -> False |- (In ?x ?s) -> False =>
      contradict H; fsetdec_body
    | H: (In ?x ?r) -> False |- (E.eq ?x ?y) -> False =>
      contradict H; fsetdec_body
    | H: (In ?x ?r) -> False |- (E.eq ?y ?x) -> False =>
      contradict H; fsetdec_body
    | H: ?P -> False |- ?Q -> False =>
      tryif prop (MSet_elt_Prop P) holds by
        (auto 100 with MSet_Prop)
      then (contradict H; fsetdec_body)
      else fsetdec_body
    | |- _ =>
      fsetdec_body
    end.

  (** * Examples *)

  Module MSetDecideTestCases.

    Lemma test_eq_trans_1 : forall x y z s,
      E.eq x y ->
      ~ ~ E.eq z y ->
      In x s ->
      In z s.
    Proof. fsetdec. Qed.

    Lemma test_eq_trans_2 : forall x y z r s,
      In x (singleton y) ->
      ~ In z r ->
      ~ ~ In z (add y r) ->
      In x s ->
      In z s.
    Proof. fsetdec. Qed.

    Lemma test_eq_neq_trans_1 : forall w x y z s,
      E.eq x w ->
      ~ ~ E.eq x y ->
      ~ E.eq y z ->
      In w s ->
      In w (remove z s).
    Proof. fsetdec. Qed.

    Lemma test_eq_neq_trans_2 : forall w x y z r1 r2 s,
      In x (singleton w) ->
      ~ In x r1 ->
      In x (add y r1) ->
      In y r2 ->
      In y (remove z r2) ->
      In w s ->
      In w (remove z s).
    Proof. fsetdec. Qed.

    Lemma test_In_singleton : forall x,
      In x (singleton x).
    Proof. fsetdec. Qed.

    Lemma test_add_In : forall x y s,
      In x (add y s) ->
      ~ E.eq x y ->
      In x s.
    Proof. fsetdec. Qed.

    Lemma test_Subset_add_remove : forall x s,
      s [<=] (add x (remove x s)).
    Proof. fsetdec. Qed.

    Lemma test_eq_disjunction : forall w x y z,
      In w (add x (add y (singleton z))) ->
      E.eq w x \/ E.eq w y \/ E.eq w z.
    Proof. fsetdec. Qed.

    Lemma test_not_In_disj : forall x y s1 s2 s3 s4,
      ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
      ~ (In x s1 \/ In x s4 \/ E.eq y x).
    Proof. fsetdec. Qed.

    Lemma test_not_In_conj : forall x y s1 s2 s3 s4,
      ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
      ~ In x s1 /\ ~ In x s4 /\ ~ E.eq y x.
    Proof. fsetdec. Qed.

    Lemma test_iff_conj : forall a x s s',
    (In a s' <-> E.eq x a \/ In a s) ->
    (In a s' <-> In a (add x s)).
    Proof. fsetdec. Qed.

    Lemma test_set_ops_1 : forall x q r s,
      (singleton x) [<=] s ->
      Empty (union q r) ->
      Empty (inter (diff s q) (diff s r)) ->
      ~ In x s.
    Proof. fsetdec. Qed.

    Lemma eq_chain_test : forall x1 x2 x3 x4 s1 s2 s3 s4,
      Empty s1 ->
      In x2 (add x1 s1) ->
      In x3 s2 ->
      ~ In x3 (remove x2 s2) ->
      ~ In x4 s3 ->
      In x4 (add x3 s3) ->
      In x1 s4 ->
      Subset (add x4 s4) s4.
    Proof. fsetdec. Qed.

    Lemma test_too_complex : forall x y z r s,
      E.eq x y ->
      (In x (singleton y) -> r [<=] s) ->
      In z r ->
      In z s.
    Proof.
      (** [fsetdec] is not intended to solve this directly. *)
      intros until s; intros Heq H Hr; lapply H; fsetdec.
    Qed.

    Lemma function_test_1 :
      forall (f : t -> t),
      forall (g : elt -> elt),
      forall (s1 s2 : t),
      forall (x1 x2 : elt),
      Equal s1 (f s2) ->
      E.eq x1 (g (g x2)) ->
      In x1 s1 ->
      In (g (g x2)) (f s2).
    Proof. fsetdec. Qed.

    Lemma function_test_2 :
      forall (f : t -> t),
      forall (g : elt -> elt),
      forall (s1 s2 : t),
      forall (x1 x2 : elt),
      Equal s1 (f s2) ->
      E.eq x1 (g x2) ->
      In x1 s1 ->
      g x2 = g (g x2) ->
      In (g (g x2)) (f s2).
    Proof.
      (** [fsetdec] is not intended to solve this directly. *)
      intros until 3. intros g_eq. rewrite <- g_eq. fsetdec.
    Qed.

    Lemma test_baydemir :
      forall (f : t -> t),
      forall (s : t),
      forall (x y : elt),
      In x (add y (f s)) ->
      ~ E.eq x y ->
      In x (f s).
    Proof.
      fsetdec.
    Qed.

  End MSetDecideTestCases.

End WDecideOn.

Require Import MSetInterface.

(** Now comes variants for self-contained weak sets and for full sets.
    For these variants, only one argument is necessary. Thanks to
    the subtyping [WS<=S], the [Decide] functor which is meant to be
    used on modules [(M:S)] can simply be an alias of [WDecide]. *)

Module WDecide (M:WSets) := !WDecideOn M.E M.
Module Decide := WDecide.
