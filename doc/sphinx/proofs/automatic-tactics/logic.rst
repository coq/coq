.. _decisionprocedures:

==============================
Solvers for logic and equality
==============================

.. tacn:: tauto
   :name: tauto

   This tactic implements a decision procedure for intuitionistic propositional
   calculus based on the contraction-free sequent calculi LJT* of Roy Dyckhoff
   :cite:`Dyc92`. Note that :tacn:`tauto` succeeds on any instance of an
   intuitionistic tautological proposition. :tacn:`tauto` unfolds negations and
   logical equivalence but does not unfold any other definition.

.. example::

   The following goal can be proved by :tacn:`tauto` whereas :tacn:`auto` would
   fail:

   .. coqtop:: reset all

      Goal forall (x:nat) (P:nat -> Prop), x = 0 \/ P x -> x <> 0 -> P x.
      intros.
      tauto.

Moreover, if it has nothing else to do, :tacn:`tauto` performs introductions.
Therefore, the use of :tacn:`intros` in the previous proof is unnecessary.
:tacn:`tauto` can for instance for:

.. example::

   .. coqtop:: reset all

      Goal forall (A:Prop) (P:nat -> Prop), A \/ (forall x:nat, ~ A -> P x) -> forall x:nat, ~ A -> P x.
      tauto.

.. note::
  In contrast, :tacn:`tauto` cannot solve the following goal
  :g:`Goal forall (A:Prop) (P:nat -> Prop), A \/ (forall x:nat, ~ A -> P x) ->`
  :g:`forall x:nat, ~ ~ (A \/ P x).`
  because :g:`(forall x:nat, ~ A -> P x)` cannot be treated as atomic and
  an instantiation of `x` is necessary.

.. tacv:: dtauto
   :name: dtauto

   While :tacn:`tauto` recognizes inductively defined connectives isomorphic to
   the standard connectives ``and``, ``prod``, ``or``, ``sum``, ``False``,
   ``Empty_set``, ``unit``, ``True``, :tacn:`dtauto` also recognizes all inductive
   types with one constructor and no indices, i.e. record-style connectives.

.. tacn:: intuition @tactic
   :name: intuition

   The tactic :tacn:`intuition` takes advantage of the search-tree built by the
   decision procedure involved in the tactic :tacn:`tauto`. It uses this
   information to generate a set of subgoals equivalent to the original one (but
   simpler than it) and applies the tactic :n:`@tactic` to them :cite:`Mun94`. If
   this tactic fails on some goals then :tacn:`intuition` fails. In fact,
   :tacn:`tauto` is simply :g:`intuition fail`.

   .. example::

      For instance, the tactic :g:`intuition auto` applied to the goal::

         (forall (x:nat), P x) /\ B -> (forall (y:nat), P y) /\ P O \/ B /\ P O

      internally replaces it by the equivalent one::

        (forall (x:nat), P x), B |- P O

      and then uses :tacn:`auto` which completes the proof.

Originally due to César Muñoz, these tactics (:tacn:`tauto` and
:tacn:`intuition`) have been completely re-engineered by David Delahaye using
mainly the tactic language (see :ref:`ltac`). The code is
now much shorter and a significant increase in performance has been noticed.
The general behavior with respect to dependent types, unfolding and
introductions has slightly changed to get clearer semantics. This may lead to
some incompatibilities.

.. tacv:: intuition

   Is equivalent to :g:`intuition auto with *`.

.. tacv:: dintuition
   :name: dintuition

   While :tacn:`intuition` recognizes inductively defined connectives
   isomorphic to the standard connectives ``and``, ``prod``, ``or``, ``sum``, ``False``,
   ``Empty_set``, ``unit``, ``True``, :tacn:`dintuition` also recognizes all inductive
   types with one constructor and no indices, i.e. record-style connectives.

.. flag:: Intuition Negation Unfolding

   Controls whether :tacn:`intuition` unfolds inner negations which do not need
   to be unfolded. This flag is on by default.

.. tacn:: rtauto
   :name: rtauto

   The :tacn:`rtauto` tactic solves propositional tautologies similarly to what
   :tacn:`tauto` does. The main difference is that the proof term is built using a
   reflection scheme applied to a sequent calculus proof of the goal.  The search
   procedure is also implemented using a different technique.

   Users should be aware that this difference may result in faster proof-search
   but slower proof-checking, and :tacn:`rtauto` might not solve goals that
   :tacn:`tauto` would be able to solve (e.g. goals involving universal
   quantifiers).

   Note that this tactic is only available after a ``Require Import Rtauto``.

.. tacn:: firstorder
   :name: firstorder

   The tactic :tacn:`firstorder` is an experimental extension of :tacn:`tauto` to
   first- order reasoning, written by Pierre Corbineau. It is not restricted to
   usual logical connectives but instead may reason about any first-order class
   inductive definition.

.. opt:: Firstorder Solver @tactic
   :name: Firstorder Solver

   The default tactic used by :tacn:`firstorder` when no rule applies is
   :g:`auto with core`, it can be reset locally or globally using this option.

   .. cmd:: Print Firstorder Solver

      Prints the default tactic used by :tacn:`firstorder` when no rule applies.

.. tacv:: firstorder @tactic

   Tries to solve the goal with :n:`@tactic` when no logical rule may apply.

.. tacv:: firstorder using {+ @qualid}

   .. deprecated:: 8.3

      Use the syntax below instead (with commas).

.. tacv:: firstorder using {+, @qualid}

  Adds lemmas :n:`{+, @qualid}` to the proof-search environment. If :n:`@qualid`
  refers to an inductive type, it is the collection of its constructors which are
  added to the proof-search environment.

.. tacv:: firstorder with {+ @ident}

  Adds lemmas from :tacn:`auto` hint bases :n:`{+ @ident}` to the proof-search
  environment.

.. tacv:: firstorder @tactic using {+, @qualid} with {+ @ident}

  This combines the effects of the different variants of :tacn:`firstorder`.

.. opt:: Firstorder Depth @natural
   :name: Firstorder Depth

   This option controls the proof-search depth bound.

.. tacn:: congruence
   :name: congruence

   The tactic :tacn:`congruence`, by Pierre Corbineau, implements the standard
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

.. example::

   .. coqtop:: reset all

      Theorem T (A:Type) (f:A -> A) (g: A -> A -> A) a b: a=(f a) -> (g b (f a))=(f (f a)) -> (g a b)=(f (g b a)) -> (g a b)=a.
      intros.
      congruence.
      Qed.

      Theorem inj (A:Type) (f:A -> A * A) (a c d: A) : f = pair a -> Some (f c) = Some (f d) -> c=d.
      intros.
      congruence.
      Qed.

.. tacv:: congruence @natural

  Tries to add at most :token:`natural` instances of hypotheses stating quantified equalities
  to the problem in order to solve it. A bigger value of :token:`natural` does not make
  success slower, only failure. You might consider adding some lemmas as
  hypotheses using assert in order for :tacn:`congruence` to use them.

.. tacv:: congruence with {+ @term}
   :name: congruence with

   Adds :n:`{+ @term}` to the pool of terms used by :tacn:`congruence`. This helps
   in case you have partially applied constructors in your goal.

.. exn:: I don’t know how to handle dependent equality.

  The decision procedure managed to find a proof of the goal or of a
  discriminable equality but this proof could not be built in |Coq| because of
  dependently-typed functions.

.. exn:: Goal is solvable by congruence but some arguments are missing. Try congruence with {+ @term}, replacing metavariables by arbitrary terms.

  The decision procedure could solve the goal with the provision that additional
  arguments are supplied for some partially applied constructors. Any term of an
  appropriate type will allow the tactic to successfully solve the goal. Those
  additional arguments can be given to congruence by filling in the holes in the
  terms given in the error message, using the :tacn:`congruence with` variant described above.

.. flag:: Congruence Verbose

  This flag makes :tacn:`congruence` print debug information.

.. tacn:: btauto
   :name: btauto

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

.. tacv:: field
          field_simplify {* @term}
          field_simplify_eq

   The field tactic is built on the same ideas as ring: this is a
   reflexive tactic that solves or simplifies equations in a field
   structure. The main idea is to reduce a field expression (which is an
   extension of ring expressions with the inverse and division
   operations) to a fraction made of two polynomial expressions.

   Tactic :n:`field` is used to solve subgoals, whereas :n:`field_simplify {+ @term}`
   replaces the provided terms by their reduced fraction.
   :n:`field_simplify_eq` applies when the conclusion is an equation: it
   simplifies both hand sides and multiplies so as to cancel
   denominators. So it produces an equation without division nor inverse.

   All of these 3 tactics may generate a subgoal in order to prove that
   denominators are different from zero.

   See :ref:`Theringandfieldtacticfamilies` for more information on the tactic and how to
   declare new field structures. All declared field structures can be
   printed with the Print Fields command.

.. example::

   .. coqtop:: reset all

      Require Import Reals.
      Goal forall x y:R,
      (x * y > 0)%R ->
      (x * (1 / x + x / (x + y)))%R =
      ((- 1 / y) * y * (- x * (x / (x + y)) - 1))%R.

      intros; field.

.. seealso::

   File plugins/ring/RealField.v for an example of instantiation,
   theory theories/Reals for many examples of use of field.
