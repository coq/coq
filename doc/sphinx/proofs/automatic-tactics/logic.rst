.. _decisionprocedures:

==============================
Solvers for logic and equality
==============================

.. tacn:: tauto

   This tactic implements a decision procedure for intuitionistic propositional
   calculus based on the contraction-free sequent calculi LJT* of Roy Dyckhoff
   :cite:`Dyc92`. Note that :tacn:`tauto` succeeds on any instance of an
   intuitionistic tautological proposition. :tacn:`tauto` unfolds negations and
   logical equivalence but does not unfold any other definition.

   .. example::

      The following goal can be proved by :tacn:`tauto` whereas :tacn:`auto` would
      fail:

      .. rocqtop:: reset all

         Goal forall (x:nat) (P:nat -> Prop), x = 0 \/ P x -> x <> 0 -> P x.
         intros.
         tauto.

   Moreover, if it has nothing else to do, :tacn:`tauto` performs introductions.
   Therefore, the use of :tacn:`intros` in the previous proof is unnecessary.
   :tacn:`tauto` can for instance for:

   .. example::

      .. rocqtop:: reset all

         Goal forall (A:Prop) (P:nat -> Prop), A \/ (forall x:nat, ~ A -> P x) -> forall x:nat, ~ A -> P x.
         tauto.

   .. note::
     In contrast, :tacn:`tauto` cannot solve the following goal
     :g:`Goal forall (A:Prop) (P:nat -> Prop), A \/ (forall x:nat, ~ A -> P x) ->`
     :g:`forall x:nat, ~ ~ (A \/ P x).`
     because :g:`(forall x:nat, ~ A -> P x)` cannot be treated as atomic and
     an instantiation of `x` is necessary.

   .. tacn:: dtauto

      While :tacn:`tauto` recognizes inductively defined connectives isomorphic to
      the standard connectives ``and``, ``prod``, ``or``, ``sum``, ``False``,
      ``Empty_set``, ``unit`` and ``True``, :tacn:`dtauto` also recognizes all inductive
      types with one constructor and no indices, i.e. record-style connectives.

.. todo would be nice to explain/discuss the various types of flags
   that define the differences between these tactics.  See Tauto.v/tauto.ml.

.. tacn:: intuition {? @ltac_expr }

   Uses the search tree built by the decision procedure for :tacn:`tauto`
   to generate a set of subgoals equivalent to the original one (but
   simpler than it) and applies :n:`@ltac_expr` to them :cite:`Mun94`. If
   :n:`@ltac_expr` is not specified, it defaults to ``Tauto.intuition_solver``.

   The initial value of ``intuition_solver`` is equivalent to :n:`auto
   with *` but prints warning ``intuition-auto-with-star`` when it
   solves a goal that :tacn:`auto` cannot solve. In a future version
   it will be changed to just :tacn:`auto`. Use ``intuition tac``
   locally or ``Ltac Tauto.intuition_solver ::= tac`` globally to
   silence the warning in a forward compatible way with your choice of
   tactic ``tac`` (``auto``, ``auto with *``, ``auto with`` your
   prefered databases, or any other tactic).

   If :n:`@ltac_expr` fails on some goals then :tacn:`intuition` fails. In fact,
   :tacn:`tauto` is simply :g:`intuition fail`.

   :tacn:`intuition` recognizes inductively defined connectives
   isomorphic to the standard connectives ``and``, ``prod``, ``or``, ``sum``, ``False``,
   ``Empty_set``, ``unit`` and ``True``.

   .. example::

      For instance, the tactic :g:`intuition auto` applied to the goal::

         (forall (x:nat), P x) /\ B -> (forall (y:nat), P y) /\ P O \/ B /\ P O

      internally replaces it by the equivalent one::

        (forall (x:nat), P x), B |- P O

      and then uses :tacn:`auto` which completes the proof.

   .. tacn:: dintuition {? @ltac_expr }

      In addition to the inductively defined connectives recognized by :tacn:`intuition`,
      :tacn:`dintuition` also recognizes all inductive
      types with one constructor and no indices, i.e. record-style connectives.

   .. flag:: Intuition Negation Unfolding

      This :term:`flag` controls whether :tacn:`intuition` unfolds inner negations which do not need
      to be unfolded. It is on by default.

.. tacn:: rtauto

   Solves propositional tautologies similarly to
   :tacn:`tauto`, but the proof term is built using a
   reflection scheme applied to a sequent calculus proof of the goal.  The search
   procedure is also implemented using a different technique.

   Users should be aware that this difference may result in faster proof search
   but slower proof checking, and :tacn:`rtauto` might not solve goals that
   :tacn:`tauto` would be able to solve (e.g. goals involving universal
   quantifiers).

   Note that this tactic is only available after a ``Require Import Rtauto``.

.. tacn:: firstorder {? @ltac_expr } {? using {+, @qualid } } {? with {+ @ident } }

   An experimental extension of :tacn:`tauto` to
   first-order reasoning. It is not restricted to
   usual logical connectives but instead can reason about any first-order class
   inductive definition.

   :token:`ltac_expr`
     Tries to solve the goal with :token:`ltac_expr` when no logical rule applies.
     If unspecified, the tactic uses the default from the :opt:`Firstorder Solver`
     option.

   :n:`using {+, @qualid }`
     Adds the lemmas :n:`{+, @qualid }` to the proof search environment. If :n:`@qualid`
     refers to an inductive type, its constructors are
     added to the proof search environment.

   :n:`with {+ @ident }`
     Adds lemmas from :tacn:`auto` hint bases :n:`{+ @ident }` to the proof search
     environment.

   .. opt:: Firstorder Solver @ltac_expr

      The default tactic used by :tacn:`firstorder` when no rule
      applies in :g:`auto with core`. This command supports the same
      locality attributes as :cmd:`Obligation Tactic`.

   .. cmd:: Print Firstorder Solver

      Prints the default tactic used by :tacn:`firstorder` when no rule applies.

   .. opt:: Firstorder Depth @natural

      This :term:`option` controls the proof search depth bound.

.. tacn:: congruence {? @natural } {? with {+ @one_term } }

   :token:`natural`
     Specifies the maximum number of hypotheses stating quantified equalities that may be added
     to the problem in order to solve it. The default is 1000.

   :n:`{? with {+ @one_term } }`
     Adds :n:`{+ @one_term }` to the pool of terms used by :tacn:`congruence`. This helps
     in case you have partially applied constructors in your goal.

   Implements the standard
   Nelson and Oppen congruence closure algorithm, which is a decision procedure
   for ground equalities with uninterpreted symbols. It also includes
   constructor theory (see :tacn:`injection` and :tacn:`discriminate`). If the goal
   is a non-quantified equality, congruence tries to prove it with non-quantified
   equalities in the context. Otherwise it tries to infer a discriminable equality
   from those in the context. Alternatively, congruence tries to prove that a
   hypothesis is equal to the goal or to the negation of another hypothesis.

   :tacn:`congruence` is also able to take advantage of hypotheses stating
   quantified equalities, but you have to provide a bound for the number of extra
   equalities generated that way. Please note that one of the sides of the
   equality must contain all the quantified variables in order for congruence to
   match against it.

   Increasing the maximum number of hypotheses may solve
   problems that would have failed with a smaller value.  It will make failures slower but it
   won't make successes found with the smaller value any slower.
   You may want to use :tacn:`assert` to add some lemmas as
   hypotheses so that :tacn:`congruence` can use them.

   .. tacn:: simple congruence {? @natural } {? with {+ @one_term } }

      Behaves like :tacn:`congruence`, but does not unfold definitions.

   .. example::

      .. rocqtop:: reset all

         Theorem T (A:Type) (f:A -> A) (g: A -> A -> A) a b: a=(f a) -> (g b (f a))=(f (f a)) -> (g a b)=(f (g b a)) -> (g a b)=a.
         intros.
         congruence.
         Qed.

         Theorem inj (A:Type) (f:A -> A * A) (a c d: A) : f = pair a -> Some (f c) = Some (f d) -> c=d.
         intros.
         congruence.
         Qed.

   .. exn:: I don’t know how to handle dependent equality.

      The decision procedure managed to find a proof of the goal or of a
      discriminable equality but this proof could not be built in Rocq because of
      dependently-typed functions.

   .. exn:: Goal is solvable by congruence but some arguments are missing. Try congruence with {+ @term}, replacing metavariables by arbitrary terms.

      The decision procedure could solve the goal with the provision that additional
      arguments are supplied for some partially applied constructors. Any term of an
      appropriate type will allow the tactic to successfully solve the goal. Those
      additional arguments can be given to congruence by filling in the holes in the
      terms given in the error message, using the `with` clause.

   Setting :opt:`Debug` ``"congruence"`` makes :tacn:`congruence` print debug information.

.. tacn:: btauto

   The tactic :tacn:`btauto` implements a reflexive solver for boolean
   tautologies. It solves goals of the form :g:`t = u` where `t` and `u` are
   constructed over the following grammar:

   .. prodn::
      btauto_term ::= @ident
      | true
      | false
      | orb @btauto_term @btauto_term
      | andb @btauto_term @btauto_term
      | xorb @btauto_term @btauto_term
      | negb @btauto_term
      | if @btauto_term then @btauto_term else @btauto_term

   Whenever the formula supplied is not a tautology, it also provides a
   counter-example.

   Internally, it uses a system very similar to the one of the ring
   tactic.

   Note that this tactic is only available after a ``Require Import Btauto``.

   .. exn:: Cannot recognize a boolean equality.

      The goal is not of the form :g:`t = u`. Especially note that :tacn:`btauto`
      doesn't introduce variables into the context on its own.
