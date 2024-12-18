=========================
Reasoning with equalities
=========================

There are multiple notions of :gdef:`equality` in Rocq:

- :gdef:`Leibniz equality` is the standard
  way to define equality in Rocq and the Calculus of Inductive Constructions,
  which is in terms of a binary relation, i.e. a binary function that returns
  a `Prop`.  The standard library
  defines `eq` similar to this:

   .. rocqdoc::

      Inductive eq {A : Type} (x : A) : A -> Prop := eq_refl : eq x x.

  The notation `x = y` represents the term `eq x y`.  The notation `x = y :> A`
  gives the type of x and y explicitly.

- :gdef:`Setoid equality <setoid equality>` defines equality in terms of an equivalence
  relation.  A :gdef:`setoid` is a set that is equipped with an equivalence relation
  (see https://en.wikipedia.org/wiki/Setoid).  These are needed to form a :gdef:`quotient set`
  or :gdef:`quotient`
  (see https://en.wikipedia.org/wiki/Equivalence_class).  In Rocq, users generally work
  with setoids rather than constructing quotients, for which there is no specific support.

- :gdef:`Definitional equality <definitional equality>` is equality based on the
  :ref:`conversion rules <Conversion-rules>`, which Rocq can determine automatically.
  Two terms are definitionally equal when they reduce to syntactically identical terms
  using the conversion rules.  When two terms are definitionally equal, Rocq knows it can
  replace one with the other, such as with :tacn:`change` `X with Y`, among many
  other advantages.  ":term:`Convertible <convertible>`" is another way of saying that
  two terms are definitionally equal.

  Among other reductions, the conversion rules can do computation to simplify
  expressions.  The behavior depends on the function associated with an
  operator, such as `+` (through the :ref:`Notation <syntax-extensions-and-notation-scopes>`
  mechanism).  `+` refers to different functions depending on the data type of its
  operands.
  Using the standard library definitions of `+` for `nat` and `Z`, `1 + 2` will be reduced to `3`.
  But the conversion rules don't do all the reductions that a person might.  For example,
  for the mentioned definitions, `n + 0` is not reducible due to how the add function is defined
  (see the aside :ref:`here <reversed_add_example>`).  `n + 1 + 2` isn't reducible because it's
  represented as `(n + 1) + 2` and convertibility doesn't consider associativity.

  In contrast, for type `R`, `1 + 2` is not reduced at all.

Tactics for dealing with equality of inductive types such as :tacn:`injection`
and :tacn:`inversion` are described :ref:`here <equality-inductive_types>`.

Tactics for simple equalities
-----------------------------

.. tacn:: reflexivity

   After doing an :tacn:`intros`,
   if the resulting goal is in the form `t = u` in which `t` and `u` are
   :term:`definitionally equal <definitional equality>`, the tactic
   proves the goal (by applying `eq_refl`).  If not, it fails.

   The tactic also works if the resulting goal (after the :tacn:`intros`) has the
   form `R t u` where `R` is a reflexive relation registered with the `Equivalence`
   or `Reflexive` typeclasses.  See :cmd:`Class` and :cmd:`Instance`.

   .. exn:: The relation @ident is not a declared reflexive relation. Maybe you need to require the Stdlib.Classes.RelationClasses library
      :undocumented:

.. tacn:: symmetry {? @simple_occurrences }

   Changes a goal that has the form :n:`{? forall @open_binders , } t = u` into
   :n:`u = t`.  :n:`@simple_occurrences`
   may be used to apply the change in the selected hypotheses and/or the conclusion.

   The tactic may also be applied to goals with the form
   :n:`{? forall @open_binders , } R @term__1 @term__2` where
   `R` is a symmetric relation registered with the `Equivalence` or `Symmetric`
   typeclasses.  See :cmd:`Class` and :cmd:`Instance`.

   .. exn:: The relation @ident is not a declared symmetric relation. Maybe you need to require the Stdlib.Classes.RelationClasses library
      :undocumented:

.. tacn:: transitivity @one_term

   Changes a goal that has the form :n:`{? forall @open_binders , } t = u`
   into the two subgoals :n:`t = @one_term`
   and :n:`@one_term = u`.

   The tactic may also be applied to goals with the form
   :n:`{? forall @open_binders , } R @term__1 @term__2` where
   `R` is a transitive relation registered with the `Equivalence` or `Transitivity`
   typeclasses.  See :cmd:`Class` and :cmd:`Instance`.

   .. tacn:: etransitivity

      This tactic behaves like :tacn:`transitivity`, using a fresh evar instead of
      a concrete :token:`one_term`.

   .. exn:: The relation @ident is not a declared transitive relation. Maybe you need to require the Stdlib.Classes.RelationClasses library
      :undocumented:

.. tacn:: f_equal

   For a goal with the form :n:`f a__1 ... a__n = g b__1 ... b__n`, creates
   subgoals :n:`f = g` and :n:`a__i = b__i` for the `n` arguments. Subgoals
   that can be proven by :tacn:`reflexivity` or :tacn:`congruence` are solved
   automatically.

.. _rewritingexpressions:

Rewriting with Leibniz and setoid equality
------------------------------------------

.. tacn:: rewrite {+, @oriented_rewriter } {? @occurrences } {? by @ltac_expr3 }

   .. insertprodn oriented_rewriter oriented_rewriter

   .. prodn::
      oriented_rewriter ::= {? {| -> | <- } } {? @natural } {? {| ? | ! } } @one_term_with_bindings

   Replaces subterms with other subterms that have been proven to be equal.
   The type of :n:`@one_term` must have the form:

      :n:`{? forall @open_binders , } EQ @term__1 @term__2`

   where :g:`EQ` is the :term:`Leibniz equality` `eq` or a registered :term:`setoid equality`.
   Note that :n:`eq @term__1 @term__2` is typically written with the infix notation
   :n:`@term__1 = @term__2`.  You must `Require Setoid` to use the tactic
   with a setoid equality or with :ref:`setoid rewriting <generalizedrewriting>`.

   :n:`rewrite @one_term` finds subterms matching :n:`@term__1` in the goal,
   and replaces them with :n:`@term__2` (or the reverse if `<-` is given).
   Some of the variables :g:`x`\ :sub:`i` are solved by unification,
   and some of the types :n:`A__1, …, A__n` may become new
   subgoals.  :tacn:`rewrite` won't find occurrences inside `forall` that refer
   to variables bound by the `forall`; use the more advanced :tacn:`setoid_rewrite`
   if you want to find such occurrences.

   :n:`{+, @oriented_rewriter }`
     The :n:`@oriented_rewriter`\s are applied sequentially
     to the first goal generated by the previous :n:`@oriented_rewriter`.  If any of them fail,
     the tactic fails.

   :n:`{? {| -> | <- } }`
     For `->` (the default), :n:`@term__1` is rewritten
     into :n:`@term__2`.  For `<-`, :n:`@term__2` is rewritten into :n:`@term__1`.

   :n:`{? @natural } {? {| ? | ! } }`
     :n:`@natural` is the number of rewrites to perform.  If `?` is given, :n:`@natural`
     is the maximum number of rewrites to perform; otherwise :n:`@natural` is the exact number
     of rewrites to perform.

     `?` (without :n:`@natural`) performs the rewrite as many times as possible
     (possibly zero times).
     This form never fails.  `!` (without :n:`@natural`) performs the rewrite as many
     times as possible
     and at least once.  The tactic fails if the requested number of rewrites can't
     be performed.  :n:`@natural !` is equivalent to :n:`@natural`.

   :n:`@occurrences`
     If :n:`@occurrences` specifies multiple occurrences, the tactic succeeds if
     any of them can be rewritten.  If not specified, only the first occurrence
     in the conclusion is replaced.

     .. note::

        If :n:`at @occs_nums` is specified, rewriting is always done
        with :ref:`setoid rewriting <generalizedrewriting>`, even for
        Leibniz equality, which means that you must `Require
        Setoid` to use that form.  However, note that :tacn:`rewrite`
        (even when using setoid rewriting) and :tacn:`setoid_rewrite`
        don't behave identically (as is noted above and below).

   :n:`by @ltac_expr3`
     If specified, is used to resolve all side conditions generated by the tactic.

   .. note::

      For each selected hypothesis and/or the conclusion,
      :tacn:`rewrite` finds the first matching subterm in
      depth-first search order. Only subterms identical to
      that first matched subterm are rewritten.  If the `at` clause is specified,
      only these subterms are considered when counting occurrences.
      To select a different set of matching subterms, you can
      specify how some or all of the free variables are bound by
      using a `with` clause (see :n:`@one_term_with_bindings`).

      For instance, if we want to rewrite the right-hand side in the
      following goal, this will not work:

      .. rocqtop:: none

         From Corelib Require Import Setoid.

         Axiom add_comm : forall n m, n + m = m + n.

      .. rocqtop:: out

         Lemma example x y : x + y = y + x.

      .. rocqtop:: all fail

         rewrite add_comm at 2.

      One can explicitly specify how some variables are bound to match
      a different subterm:

      .. rocqtop:: all abort

         rewrite add_comm with (m := x).

      Note that the more advanced :tacn:`setoid_rewrite` tactic
      behaves differently, and thus the number of occurrences
      available to rewrite may differ between the two tactics.

   .. exn:: Tactic failure: Setoid library not loaded.
      :undocumented:

      .. todo You can use Typeclasses Debug to tell whether rewrite used
         setoid rewriting.  Example here: https://github.com/coq/coq/pull/13470#discussion_r539230973

   .. exn:: Cannot find a relation to rewrite.
      :undocumented:

   .. exn:: Tactic generated a subgoal identical to the original goal.
      :undocumented:

   .. exn:: Found no subterm matching @term in @ident.
            Found no subterm matching @term in the current goal.

      This happens if :n:`@term` does not occur in, respectively, the named hypothesis or the goal.

   .. tacn:: erewrite {+, @oriented_rewriter } {? @occurrences } {? by @ltac_expr3 }

      Works like :tacn:`rewrite`, but turns
      unresolved bindings, if any, into existential variables instead of
      failing. It has the same parameters as :tacn:`rewrite`.

   .. flag:: Keyed Unification

      This :term:`flag` makes higher-order unification used by :tacn:`rewrite` rely on a set of keys to drive
      unification.  The subterms, considered as rewriting candidates, must start with
      the same key as the left- or right-hand side of the lemma given to rewrite, and the arguments
      are then unified up to full reduction.

   .. cmd:: Declare Equivalent Keys @one_term @one_term
      :undocumented:

   .. cmd:: Print Equivalent Keys
      :undocumented:

.. tacn:: rewrite * {? {| -> | <- } } @one_term {? in @ident } {? at @rewrite_occs } {? by @ltac_expr3 }
          rewrite * {? {| -> | <- } } @one_term at @rewrite_occs in @ident {? by @ltac_expr3 }
   :name: rewrite *; _
   :undocumented:

.. tacn:: replace {? {| -> | <- } } @one_term__from with @one_term__to {? @occurrences } {? by @ltac_expr3 }
          replace {? {| -> | <- } } @one_term__from {? @occurrences }
   :name: replace; _

   The first form, when used with `<-` or no arrow, replaces all free
   occurrences of :n:`@one_term__from` in the current goal with :n:`@one_term__to`
   and generates an equality :n:`@one_term__to = @one_term__from` as a subgoal.
   Note that this equality is reversed with respect to the order of the two terms.
   When used with `->`, it generates instead an equality :n:`@one_term__from = @one_term__to`.
   When :n:`by @ltac_expr3` is not present, this equality is automatically solved
   if it occurs among the hypotheses, or if its symmetric form occurs.

   The second form, with `->` or no arrow, replaces :n:`@one_term__from`
   with :n:`@term__to` using
   the first hypothesis whose type has the form :n:`@one_term__from = @term__to`.
   If `<-` is given, the tactic uses the first hypothesis with the reverse form,
   i.e. :n:`@term__to = @one_term__from`.

   :n:`@occurrences`
     The `type of` and `value of` forms are not supported.
     Note you must `Require Setoid` to use the `at` clause in :n:`@occurrences`.

   :n:`by @ltac_expr3`
     Applies the :n:`@ltac_expr3` to solve the generated equality.

   .. exn:: Terms do not have convertible types.
      :undocumented:

.. tacn:: substitute {? {| -> | <- } } @one_term_with_bindings
   :undocumented:

.. tacn:: subst {* @ident }

   For each :n:`@ident`, in order, for which there is a hypothesis in the form
   :n:`@ident = @term` or :n:`@term = @ident`, replaces :n:`@ident` with :n:`@term`
   everywhere in the hypotheses and the conclusion and clears :n:`@ident` and the hypothesis
   from the context.  If there are multiple hypotheses that match the :n:`@ident`,
   the first one is used.  If no :n:`@ident` is given, replacement is done for all
   hypotheses in the appropriate form in top to bottom order.

   If :n:`@ident` is a :term:`local definition <context-local definition>` of the form
   :n:`@ident := @term`, it is also unfolded and cleared.

   If :n:`@ident` is a section variable it must have no
   indirect occurrences in the goal, i.e. no global declarations
   implicitly depending on the section variable may be present in the
   goal.

   .. note::
      If the hypothesis is itself dependent in the goal, it is replaced by the proof of
      reflexivity of equality.

   .. flag:: Regular Subst Tactic

      This :term:`flag` controls the behavior of :tacn:`subst`. When it is
      activated (it is by default), :tacn:`subst` also deals with the following corner cases:

      + A context with ordered hypotheses :n:`@ident__1 = @ident__2`
        and :n:`@ident__1 = t`, or :n:`t′ = @ident__1` with `t′` not
        a variable, and no other hypotheses of the form :n:`@ident__2 = u`
        or :n:`u = @ident__2`; without the flag, a second call to
        subst would be necessary to replace :n:`@ident__2` by `t` or
        `t′` respectively.
      + The presence of a recursive equation which without the flag would
        be a cause of failure of :tacn:`subst`.
      + A context with cyclic dependencies as with hypotheses :n:`@ident__1 = f @ident__2`
        and :n:`@ident__2 = g @ident__1` which without the
        flag would be a cause of failure of :tacn:`subst`.

      Additionally, it prevents a :term:`local definition <context-local definition>`
      such as :n:`@ident := t` from being
      unfolded which otherwise would exceptionally unfold in configurations
      containing hypotheses of the form :n:`@ident = u`, or :n:`u′ = @ident`
      with `u′` not a variable. Finally, it preserves the initial order of
      hypotheses, which without the flag it may break.

   .. exn:: Cannot find any non-recursive equality over @ident.
      :undocumented:

   .. exn:: Section variable @ident occurs implicitly in global declaration @qualid present in hypothesis @ident.
            Section variable @ident occurs implicitly in global declaration @qualid present in the conclusion.

      Raised when the variable is a section variable with indirect
      dependencies in the goal.
      If :n:`@ident` is a section variable, it must not have any
      indirect occurrences in the goal, i.e. no global declarations
      implicitly depending on the section variable may be present in the
      goal.

.. tacn:: simple subst
   :undocumented:

.. tacn:: stepl @one_term {? by @ltac_expr }

   For chaining rewriting steps. It assumes a goal in the
   form :n:`R @term__1 @term__2` where ``R`` is a binary relation and relies on a
   database of lemmas of the form :g:`forall x y z, R x y -> eq x z -> R z y`
   where `eq` is typically a setoid equality. The application of :n:`stepl @one_term`
   then replaces the goal by :n:`R @one_term @term__2` and adds a new goal stating
   :n:`eq @one_term @term__1`.

   If :n:`@ltac_expr` is specified, it is applied to the side condition.

   .. cmd:: Declare Left Step @one_term

      Adds :n:`@one_term` to the database used by :tacn:`stepl`.

   This tactic is especially useful for parametric setoids which are not accepted
   as regular setoids for :tacn:`rewrite` and :tacn:`setoid_replace` (see
   :ref:`Generalizedrewriting`).

   .. tacn:: stepr @one_term {? by @ltac_expr }

      This behaves like :tacn:`stepl` but on the right hand side of the binary
      relation. Lemmas are expected to be in the form
      :g:`forall x y z, R x y -> eq y z -> R x z`.

   .. cmd:: Declare Right Step @one_term

       Adds :n:`@term` to the database used by :tacn:`stepr`.

Rewriting with definitional equality
------------------------------------

.. tacn:: change {? @one_term__from {? at @occs_nums } with } @one_term__to {? @occurrences }

   Replaces terms with other :term:`convertible` terms.
   If :n:`@one_term__from` is not specified, then :n:`@one_term__to` replaces the conclusion and/or
   the specified hypotheses.  If :n:`@one_term__from` is specified, the tactic replaces occurrences
   of :n:`@one_term__to` within the conclusion and/or the specified hypotheses.

   :n:`{? @one_term__from {? at @occs_nums } with }`
     Replaces the occurrences of :n:`@one_term__from` specified by :n:`@occs_nums`
     with :n:`@one_term__to`, provided that the two :n:`@one_term`\s are
     convertible.  :n:`@one_term__from` may contain pattern variables such as `?x`,
     whose value which will substituted for `x` in :n:`@one_term__to`, such as in
     `change (f ?x ?y) with (g (x, y))` or `change (fun x => ?f x) with f`.

     The `at … with …` form is deprecated in 8.14; use `with … at …` instead.
     For `at … with … in H |-`, use `with … in H at … |-`.

   :n:`@occurrences`
     If `with` is not specified, :n:`@occurrences` must only specify
     entire hypotheses and/or the goal; it must not include any
     :n:`at @occs_nums` clauses.

   .. exn:: Not convertible.
      :undocumented:

   .. exn:: Found an "at" clause without "with" clause
      :undocumented:

   .. tacn:: now_show @one_type

      A synonym for :n:`change @one_type`. It can be used to
      make some proof steps explicit when refactoring a proof script
      to make it readable.

   .. seealso:: :ref:`applyingconversionrules`

.. tacn:: change_no_check {? @one_term__from {? at @occs_nums } with } @one_term__to {? @occurrences }

   For advanced usage. Similar to :tacn:`change`, but as an optimization,
   it skips checking that :n:`@one_term__to` is convertible with the goal or
   :n:`@one_term__from`.

   Recall that the Rocq kernel typechecks proofs again when they are concluded to
   ensure correctness. Hence, using :tacn:`change` checks convertibility twice
   overall, while :tacn:`change_no_check` can produce ill-typed terms,
   but checks convertibility only once.
   Hence, :tacn:`change_no_check` can be useful to speed up certain proof
   scripts, especially if one knows by construction that the argument is
   indeed convertible to the goal.

   In the following example, :tacn:`change_no_check` replaces :g:`False` with
   :g:`True`, but :cmd:`Qed` then rejects the proof, ensuring consistency.

   .. example::

      .. rocqtop:: all abort fail

         Goal False.
           change_no_check True.
           exact I.
         Qed.

   .. example::

      .. rocqtop:: all abort fail

         Goal True -> False.
           intro H.
           change_no_check False in H.
           exact H.
         Qed.

.. _applyingconversionrules:

Applying conversion rules
-------------------------

These tactics apply reductions and expansions, replacing :term:`convertible` subterms
with others that are equal by definition in |CiC|.
They implement different specialized uses of the
:tacn:`change` tactic.  Other ways to apply these reductions are through
the :cmd:`Eval` command, the `Eval` clause in the :cmd:`Definition`/:cmd:`Example`
command and the :tacn:`eval` tactic.

Tactics described in this section include:

- :tacn:`lazy` and :tacn:`cbv`, which allow precise selection of which reduction
  rules to apply
- :tacn:`simpl` and :tacn:`cbn`, which are "clever" tactics meant to give the most
  readable result
- :tacn:`hnf` and :tacn:`red`, which apply reduction rules only to the head of the
  term
- :tacn:`vm_compute` and :tacn:`native_compute`, which are performance-oriented.

Except for :tacn:`red`, conversion tactics succeed even if the context is left
unchanged.

Conversion tactics, with two exceptions, only change the types and contexts
of existential variables
and leave the proof term unchanged.  (The :tacn:`vm_compute` and :tacn:`native_compute`
tactics change existential variables in a way similar to other conversions while
also adding a single explicit cast to the proof term to tell the kernel
which reduction engine to use.  See :ref:`type-cast`.)  For example:

   .. rocqtop:: all

      Goal 3 + 4 = 7.
      Show Proof.
      Show Existentials.
      cbv.
      Show Proof.
      Show Existentials.

   .. rocqtop:: none

      Abort.

.. tacn:: lazy {? @reductions } @simple_occurrences
          cbv {? @reductions } @simple_occurrences

   .. insertprodn reductions delta_reductions

   .. prodn::
      reductions ::= {+ @reduction }
      | {? head } @delta_reductions
      reduction ::= head
      | beta
      | delta {? @delta_reductions }
      | match
      | fix
      | cofix
      | iota
      | zeta
      delta_reductions ::= {? - } [ {+ @reference } ]

   Normalize the goal as specified by :n:`@reductions`.  If no reductions are
   specified by name, all reductions are applied.  If any reductions are specified by name,
   then only the named reductions are applied.  The reductions include:

   `head`
     Do only head reduction, without going under binders.
     Supported by :tacn:`simpl`, :tacn:`cbv`, :tacn:`cbn` and :tacn:`lazy`.
     If this is the only specified reduction, all other reductions are applied.

   `beta`
     :term:`beta-reduction` of functional application

   :n:`delta {? @delta_reductions }`
     :term:`delta-reduction`: unfolding of transparent constants, see :ref:`controlling-the-reduction-strategies`.
     The form in :n:`@reductions` without the keyword `delta` includes `beta`,
     `iota` and `zeta` reductions in addition to `delta` using the given :n:`@delta_reductions`.

     :n:`{? - } [ {+ @reference } ]`
       without the `-`, limits delta unfolding to the listed constants.  If the
       `-` is present,
       unfolding is applied to all constants that are not listed.
       Notice that the ``delta`` doesn't apply to variables bound by a let-in
       construction inside the term itself (use ``zeta`` to inline these).
       Opaque constants are never unfolded except by :tacn:`vm_compute` and
       :tacn:`native_compute`
       (see `#4476 <https://github.com/coq/coq/issues/4476>`_ and
       :ref:`controlling-the-reduction-strategies`).

   `iota`
     :term:`iota-reduction` of pattern matching (`match`) over a constructed term and reduction
     of :g:`fix` and :g:`cofix` expressions.  Shorthand for `match fix cofix`.

   `zeta`
      :term:`zeta-reduction`: reduction of :ref:`let-in definitions <let-in>`

   Normalization is done by first evaluating the
   head of the expression into :gdef:`weak-head normal form`, i.e. until the
   evaluation is blocked by a variable, an opaque constant, an
   axiom, such as in :n:`x u__1 … u__n`, :g:`match x with … end`,
   :g:`(fix f x {struct x} := …) x`, a constructed form (a
   :math:`\lambda`-expression, constructor, cofixpoint, inductive type,
   product type or sort) or a redex for which flags prevent reduction of the redex. Once a
   weak-head normal form is obtained, subterms are recursively reduced using the
   same strategy.

   There are two strategies for reduction to weak-head normal form:
   *lazy* (the :tacn:`lazy` tactic), or *call-by-value* (the :tacn:`cbv` tactic).
   The lazy strategy is a
   `call by need <https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_need>`_
   strategy, with sharing of reductions: the
   arguments of a function call are weakly evaluated only when necessary,
   and if an argument is used several times then it is weakly computed
   only once. This reduction is efficient for reducing expressions with
   dead code. For instance, the proofs of a proposition :g:`exists x. P(x)`
   reduce to a pair of a witness :g:`t` and a proof that :g:`t` satisfies the
   predicate :g:`P`. Most of the time, :g:`t` may be computed without computing
   the proof of :g:`P(t)`, thanks to the lazy strategy.

   .. flag:: Kernel Term Sharing

      Turning this flag off disables the sharing of computations in
      :tacn:`lazy`, making it a call-by-name reduction. This also
      affects the reduction procedure used by the kernel when
      typechecking. By default sharing is activated.

   The call-by-value strategy is the one used in ML languages: the
   arguments of a function call are systematically weakly evaluated
   first. The lazy strategy is similar to how Haskell reduces terms.
   Although the lazy strategy always does fewer reductions than
   the call-by-value strategy, the latter is generally more efficient for
   evaluating purely computational expressions (i.e. with little dead code).

   .. tacn:: compute {? @delta_reductions } @simple_occurrences

      A variant form of :tacn:`cbv`.

   Setting :opt:`Debug` ``"Cbv"`` makes :tacn:`cbv` (and its derivative :tacn:`compute`) print
   information about the constants it encounters and the unfolding decisions it
   makes.

.. tacn:: simpl {? head } {? @delta_reductions } {? {| @reference_occs | @pattern_occs } } @simple_occurrences

   .. insertprodn reference_occs pattern_occs

   .. prodn::
      reference_occs ::= @reference {? at @occs_nums }
      pattern_occs ::= @one_term {? at @occs_nums }

   Reduces a term to
   something still readable instead of fully normalizing it. It performs
   a sort of strong normalization with two key differences:

   + It unfolds constants only if they lead to an ι-reduction,
     i.e. reducing a match or unfolding a fixpoint.
   + When reducing a constant unfolding to (co)fixpoints, the tactic
     uses the name of the constant the (co)fixpoint comes from instead of
     the (co)fixpoint definition in recursive calls.

   :n:`@occs_nums`
     Selects which occurrences of :n:`@one_term` to process (counting from
     left to right on the expression printed using the :flag:`Printing All` flag)

   :n:`@simple_occurrences`
     Permits selecting whether to reduce the conclusion and/or one or more
     hypotheses.  While the `at` option of :n:`@occurrences` is not allowed here,
     :n:`@reference_occs` and :n:`@pattern_occs` have a somewhat less
     flexible `at` option for selecting specific occurrences.

   :tacn:`simpl` can unfold transparent constants whose name can be reused in
   recursive calls as well as those designated by :cmd:`Arguments` :n:`@reference … /`
   commands. For instance, a constant :g:`plus' := plus` may be unfolded and
   reused in recursive calls, but a constant such as :g:`succ := plus (S O)` is
   not unfolded unless it was specifically designated in an :cmd:`Arguments`
   command such as :n:`Arguments succ /.`.

   :n:`{| @reference_occs | @pattern_occs }` can limit the application of :tacn:`simpl`
   to:

   - applicative subterms whose :term:`head` is the
     constant :n:`@qualid` or is the constant used
     in the notation :n:`@string` (see :n:`@reference`)
   - subterms matching a pattern :n:`@one_term`

.. tacn:: cbn {? @reductions } @simple_occurrences

   :tacn:`cbn` was intended to be a more principled, faster and more
   predictable replacement for :tacn:`simpl`.
   The main difference is that :tacn:`cbn` may unfold constants even when they
   cannot be reused in recursive calls: in the previous example, :g:`succ t` is
   reduced to :g:`S t`. Modifiers such as `simpl never` are also not treated the same,
   see :ref:`Args_effect_on_unfolding`.

   Setting :opt:`Debug` ``"RAKAM"`` makes :tacn:`cbn` print various debugging information.
   ``RAKAM`` is the Refolding Algebraic Krivine Abstract Machine.

   .. example::

      Here are typical examples comparing :tacn:`cbn` and :tacn:`simpl`:

      .. rocqtop:: all

         Definition add1 (n:nat) := n + 1.
         Eval simpl in add1 0.
         Eval cbn in add1 0.

         Definition pred_add n m := pred (n + m).
         Eval simpl in pred_add 0 0.
         Eval cbn in pred_add 0 0.

         Parameter n : nat.
         Eval simpl in pred_add 0 n.
         Eval cbn in pred_add 0 n.

.. tacn:: hnf @simple_occurrences

   Replaces the current goal with its
   weak-head normal form according to the βδιζ-reduction rules, i.e. it
   reduces the :term:`head` of the goal until it becomes a product or an
   irreducible term. All inner βι-redexes are also reduced.  While :tacn:`hnf`
   behaves similarly to :tacn:`simpl` and :tacn:`cbn`, unlike them, it does not
   recurse into subterms.
   The behavior of :tacn:`hnf` can be tuned using the :cmd:`Arguments` command.

   Example: The term :g:`fun n : nat => S n + S n` is not reduced by :n:`hnf`.

   .. note::
      The δ rule only applies to transparent constants
      (see :ref:`controlling-the-reduction-strategies` on transparency and opacity).

.. tacn:: red @simple_occurrences

   βιζ-reduces the :term:`head constant` of `T`, if possible, in the selected
   hypotheses and/or the goal which have the form:

     :n:`{? forall @open_binders , } T`

   (where `T` does not begin with a `forall`) to :n:`c t__1 … t__n`
   where :g:`c` is a constant.
   If :g:`c` is transparent then it replaces :g:`c` with its
   definition and reduces again until no further reduction is possible.

   In the term :n:`{? forall @open_binders , } t__1 ... t__n`, where :n:`t__1` is not a
   :n:`@term_application`, :n:`t__1` is the :gdef:`head` of the term.
   In a term with the form :n:`{? forall @open_binders , } c t__1 ... t__n`, where
   :n:`c` is a :term:`constant`, :n:`c` is the :gdef:`head constant`.

   .. exn:: No head constant to reduce.
      :undocumented:

.. tacn:: unfold {+, @reference_occs } {? @occurrences }

   Applies :term:`delta-reduction` to
   the constants specified by each :n:`@reference_occs`.
   The selected hypotheses and/or goals are then reduced to βιζ-normal form.
   Use the general reduction tactics if you want to only apply the
   δ rule, for example :tacn:`cbv` :n:`delta [ @reference ]`.

   :n:`@reference_occs`
     If :n:`@reference` is a :n:`@qualid`, it must be a defined transparent
     constant or :term:`local definition <context-local definition>`
     (see :ref:`gallina-definitions` and :ref:`controlling-the-reduction-strategies`).

     If :n:`@reference` is a :n:`@string {? @scope_key}`, the :n:`@string` is
     the discriminating
     symbol of a notation (e.g. "+") or an expression defining a notation (e.g. `"_ +
     _"`) and the notation is an application whose head symbol
     is an unfoldable constant, then the tactic unfolds it.

   :n:`@occurrences`
     If :n:`@occurrences` is specified,
     the specified occurrences will be replaced in the selected hypotheses and/or goal.
     Otherwise every occurrence of the constants in the goal is replaced.
     If multiple :n:`@reference_occs` are given, any `at` clauses must be
     in the :n:`@reference_occs` rather than in :n:`@occurrences`.

   .. exn:: Cannot turn {| inductive | constructor } into an evaluable reference.

      Occurs when trying to unfold something that is
      defined as an inductive type (or constructor) and not as a
      definition.

      .. example::

         .. rocqtop:: abort all fail

            Goal 0 <= 1.
            unfold le.

   .. exn:: @ident is opaque.

      Raised if you are trying to unfold a definition
      that has been marked opaque.

      .. example::

         .. rocqtop:: abort all fail

            Opaque Nat.add.
            Goal 1 + 0 = 1.
            unfold Nat.add.

      .. exn:: Bad occurrence number of @qualid.
         :undocumented:

      .. exn:: @qualid does not occur.
         :undocumented:

.. tacn:: fold {+ @one_term } @simple_occurrences

   First, this tactic reduces each :n:`@one_term` using the :tacn:`red` tactic.
   Then, every occurrence of the resulting terms in the selected hypotheses and/or
   goal will be replaced by its associated :n:`@one_term`. This tactic is particularly
   useful for
   reversing undesired unfoldings, which may make the goal very hard to read.
   The undesired unfoldings may be due to the limited capabilities of
   other reduction tactics.
   On the other hand, when an unfolded function applied to its argument has been
   reduced, the :tacn:`fold` tactic doesn't do anything.

   :tacn:`fold` :n:`@one_term__1 @one_term__2` is equivalent to
   :n:`fold @one_term__1; fold @one_term__2`.

   .. example:: :tacn:`fold` doesn't always undo :tacn:`unfold`

      .. rocqtop:: all

         Goal ~0=0.
         unfold not.

      This :tacn:`fold` doesn't undo the preceeding :tacn:`unfold` (it makes no change):

      .. rocqtop:: all

         fold not.

      However, this :tacn:`pattern` followed by :tacn:`fold` does:

      .. rocqtop:: all abort

         pattern (0 = 0).
         fold not.

   .. example:: Use :tacn:`fold` to reverse unfolding of `fold_right`

      .. rocqtop:: none

         Require Import ListDef.
         Local Open Scope list_scope.

         Definition fold_right [A B] (f : B -> A -> A) (a0 : A) :=
           fix fold_right (l : list B) : A := match l with
                                              | nil => a0
                                              | b :: t => f b (fold_right t)
                                              end.

      .. rocqtop:: all abort

         Goal forall x xs, fold_right and True (x::xs).
         red.
         fold (fold_right and True).

.. tacn:: pattern {+, @pattern_occs } {? @occurrences }

   Performs beta-expansion (the inverse of :term:`beta-reduction`) for the
   selected hypotheses and/or goals.
   The :n:`@one_term`\s in :n:`@pattern_occs` must be free subterms in the selected items.
   The expansion is done for each selected item :g:`T`
   for a set of :n:`@one_term`\s in the :n:`@pattern_occs` by:

   + replacing all selected occurrences of the :n:`@one_term`\s in :g:`T` with fresh variables
   + abstracting these variables
   + applying the abstracted goal to the :n:`@one_term`\s

   For instance, if the current goal :g:`T` is expressible as :n:`φ(t__1 … t__n)`
   where the notation captures all the instances of the :n:`t__i` in φ, then :tacn:`pattern`
   :n:`t__1, …, t__n` generates the equivalent goal
   :n:`(fun (x__1:A__1 … (x__n:A__n) => φ(x__1 … x__n)) t__1 … t__n`.
   If :n:`t__i` occurs in one of the generated types :n:`A__j`
   (for `j > i`),
   occurrences will also be considered and possibly abstracted.

   This tactic can be used, for instance, when the tactic :tacn:`apply` fails
   on matching or to better control the behavior of :tacn:`rewrite`.

   See the example :ref:`here <example_apply_pattern>`.

Fast reduction tactics: vm_compute and native_compute
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:tacn:`vm_compute` is a brute-force but efficient tactic that
first normalizes the terms before comparing them. It is based on a
bytecode representation of terms similar to the bytecode
representation used in the ZINC virtual machine :cite:`Leroy90`. It is
especially useful for intensive computation of algebraic values, such
as numbers, and for reflection-based tactics.

:tacn:`native_compute` is based on on converting the Rocq code to OCaml.

Note that both these tactics ignore :cmd:`Opaque` markings
(see issue `#4776 <https://github.com/coq/coq/issues/4776>`_), nor do they
apply unfolding strategies such as from :cmd:`Strategy`.

:tacn:`native_compute` is typically two to five
times faster than :tacn:`vm_compute` at applying conversion rules
when Rocq is running native code, but :tacn:`native_compute` requires
considerably more overhead.  We recommend using :tacn:`native_compute`
when all of the following are true (otherwise use :tacn:`vm_compute`):

- the running time in :tacn:`vm_compute` at least 5-10 seconds
- the size of the input term is small (e.g. hand-generated code rather than
  automatically-generated code that may have nested destructs on inductives
  with dozens or hundreds of constructors)
- the output is small (e.g. you're returning a boolean, a natural number or
  an integer rather than a large abstract syntax tree)

These tactics change existential variables in a way similar to other conversions
while also adding a single explicit cast (see :ref:`type-cast`) to the proof term
to tell the kernel which reduction engine to use.

.. tacn:: vm_compute {? {| @reference_occs | @pattern_occs } } {? @occurrences }

   Evaluates the goal using the optimized call-by-value evaluation
   bytecode-based virtual machine described in :cite:`CompiledStrongReduction`.
   This algorithm is dramatically more efficient than the algorithm used for the
   :tacn:`cbv` tactic, but it cannot be fine-tuned. It is especially useful for
   full evaluation of algebraic objects. This includes the case of
   reflection-based tactics.

.. tacn:: native_compute {? {| @reference_occs | @pattern_occs } } {? @occurrences }

   Evaluates the goal by compilation to OCaml as described
   in :cite:`FullReduction`. Depending on the configuration, this tactic can either default to
   :tacn:`vm_compute`, recompile dependencies or fail due to some missing
   precompiled dependencies,
   see :ref:`the native-compiler option <native-compiler-options>` for details.

   .. flag:: NativeCompute Timing

      This :term:`flag` causes all calls to the native compiler to print
      timing information for the conversion to native code,
      compilation, execution, and reification phases of native
      compilation.  Timing is printed in units of seconds of
      wall-clock time.

   .. flag:: NativeCompute Profiling

      On Linux, if you have the ``perf`` profiler installed, this :term:`flag` makes
      it possible to profile :tacn:`native_compute` evaluations.

   .. opt:: NativeCompute Profile Filename @string

      This :term:`option` specifies the profile output; the default is
      ``native_compute_profile.data``. The actual filename used
      will contain extra characters to avoid overwriting an existing file; that
      filename is reported to the user.
      That means you can individually profile multiple uses of
      :tacn:`native_compute` in a script. From the Linux command line, run ``perf report``
      on the profile file to see the results. Consult the ``perf`` documentation
      for more details.

Computing in a term: eval and Eval
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Evaluation of a term can be performed with:

.. tacn:: eval @red_expr in @term


   .. insertprodn red_expr red_expr

   .. prodn::
      red_expr ::= lazy {? @reductions }
      | cbv {? @reductions }
      | compute {? @delta_reductions }
      | vm_compute {? {| @reference_occs | @pattern_occs } }
      | native_compute {? {| @reference_occs | @pattern_occs } }
      | red
      | hnf
      | simpl {? head } {? @delta_reductions } {? {| @reference_occs | @pattern_occs } }
      | cbn {? @reductions }
      | unfold {+, @reference_occs }
      | fold {+ @one_term }
      | pattern {+, @pattern_occs }
      | @ident

   :tacn:`eval` is a :token:`value_tactic`.  It returns the result of
   applying the conversion rules specified by :n:`@red_expr`.  It does not
   change the proof state.

   The :n:`@red_expr` alternatives that begin with a keyword correspond to the
   tactic with the same name, though in several cases with simpler syntax
   than the tactic.  :n:`@ident` is a named reduction expression created
   with :cmd:`Declare Reduction`.

   .. seealso:: Section :ref:`applyingconversionrules`.

.. cmd:: Eval @red_expr in @term

   Performs the specified reduction on :n:`@term` and displays
   the resulting term with its type. If a proof is open, :n:`@term`
   may reference hypotheses of the selected goal.  :cmd:`Eval` is
   a :token:`query_command`, so it may be prefixed with a goal selector.

   .. cmd:: Compute @term

      Evaluates :n:`@term` using the bytecode-based virtual machine.
      It is a shortcut for :cmd:`Eval` :n:`vm_compute in @term`.
      :cmd:`Compute` is a :token:`query_command`, so it may be prefixed
      with a goal selector.

.. cmd:: Declare Reduction @ident := @red_expr

   Declares a short name for the reduction expression :n:`@red_expr`, for
   instance ``lazy beta delta [foo bar]``. This short name can then be used
   in :n:`Eval @ident in` or ``eval`` constructs. This command
   accepts the :attr:`local` attribute, which indicates that the reduction
   will be discarded at the end of the
   file or module. The name is not qualified. In
   particular declaring the same name in several modules or in several
   functor applications will be rejected if these declarations are not
   local. The name :n:`@ident` cannot be used directly as an Ltac tactic, but
   nothing prevents the user from also performing a
   :n:`Ltac @ident := @red_expr`.

.. _controlling-the-reduction-strategies:

Controlling reduction strategies and the conversion algorithm
-------------------------------------------------------------

The commands to fine-tune the reduction strategies and the lazy conversion
algorithm are described in this section.  Also see :ref:`Args_effect_on_unfolding`,
which supports additional fine-tuning.

.. cmd:: Opaque {? ! } {+ @reference }

   Marks the specified constants as :term:`opaque` so tactics won't :term:`unfold` them
   with :term:`delta-reduction`.
   "Constants" are items defined by commands such as :cmd:`Definition`,
   :cmd:`Let` (with an explicit body), :cmd:`Fixpoint`, :cmd:`CoFixpoint`
   and :cmd:`Function`.

   This command accepts the :attr:`global` attribute.  By default, the scope
   of :cmd:`Opaque` is limited to the current section or module.

   :cmd:`Opaque` also affects Rocq's conversion algorithm, causing
   it to delay unfolding the specified constants as much as possible when it
   has to check that two distinct applied constants are convertible.
   See Section :ref:`conversion-rules`.

   In the particular case where the constants refer to primitive projections,
   a :token:`!` can be used to make the compatibility constants opaque, while
   by default the projection themselves are made opaque and the compatibility
   constants always remain transparent. This mechanism is only intended for
   debugging purposes.

   Use the :cmd:`About` command to see if a symbol is transparent or opaque.

.. cmd:: Transparent {? ! } {+ @reference }

   The opposite of :cmd:`Opaque`, it marks the specified constants
   as :term:`transparent`
   so that tactics may unfold them.  See :cmd:`Opaque` above.

   This command accepts the :attr:`global` attribute.  By default, the scope
   of :cmd:`Transparent` is limited to the current section or module.

   Note that constants defined by proofs ending with :cmd:`Qed` are
   irreversibly opaque; :cmd:`Transparent` will not make them transparent.
   This is consistent
   with the usual mathematical practice of *proof irrelevance*: what
   matters in a mathematical development is the sequence of lemma
   statements, not their actual proofs. This distinguishes lemmas from
   the usual defined constants, whose actual values are of course
   relevant in general.

   In the particular case where the constants refer to primitive projections,
   a :token:`!` can be used to make the compatibility constants transparent
   (see :cmd:`Opaque` for more details).

   .. exn:: The reference @qualid was not found in the current environment.

      There is no constant named :n:`@qualid` in the environment.

.. seealso:: :ref:`applyingconversionrules`, :cmd:`Qed` and :cmd:`Defined`

.. _vernac-strategy:

.. cmd:: Strategy {+ @strategy_level [ {+ @reference } ] }

   .. insertprodn strategy_level strategy_level

   .. prodn::
      strategy_level ::= opaque
      | @integer
      | expand
      | transparent

   Generalizes the behavior of the :cmd:`Opaque` and :cmd:`Transparent`
   commands. It is used to fine-tune the strategy for unfolding
   constants, both at the tactic level and at the kernel level. This
   command associates a :n:`@strategy_level` with the qualified names in the :n:`@reference`
   sequence. Whenever two
   expressions with two distinct :term:`head constants <head constant>` are compared (for
   example, typechecking `f x` where `f : A -> B` and `x : C` will result in
   converting `A` and `C`), the one
   with lower level is expanded first. In case of a tie, the second one
   (appearing in the cast type) is expanded.

   This command accepts the :attr:`local` attribute, which limits its effect
   to the current section or module, in which case the section and module
   behavior is the same as :cmd:`Opaque` and :cmd:`Transparent` (without :attr:`global`).

   Levels can be one of the following (higher to lower):

    + ``opaque`` : level of opaque constants. They cannot be expanded by
      tactics (behaves like +∞, see next item).
    + :n:`@integer` : levels indexed by an integer. Level 0 corresponds to the
      default behavior, which corresponds to transparent constants. This
      level can also be referred to as ``transparent``. Negative levels
      correspond to constants to be expanded before normal transparent
      constants, while positive levels correspond to constants to be
      expanded after normal transparent constants.
    + ``expand`` : level of constants that should be expanded first (behaves
      like −∞)
    + ``transparent`` : Equivalent to level 0

.. cmd:: Print Strategy @reference

   This command prints the strategy currently associated with :n:`@reference`. It
   fails if :n:`@reference` is not an unfoldable reference, that is, neither a
   variable nor a constant.

   .. exn:: The reference is not unfoldable.
      :undocumented:

.. cmd:: Print Strategies

   Print all the currently non-transparent strategies.

.. tacn:: with_strategy @strategy_level_or_var [ {+ @reference } ] @ltac_expr3

   .. insertprodn strategy_level_or_var strategy_level_or_var

   .. prodn::
      strategy_level_or_var ::= @strategy_level
      | @ident

   Executes :token:`ltac_expr3`, applying the alternate unfolding
   behavior that the :cmd:`Strategy` command controls, but only for
   :token:`ltac_expr3`.  This can be useful for guarding calls to
   reduction in tactic automation to ensure that certain constants are
   never unfolded by tactics like :tacn:`simpl` and :tacn:`cbn` or to
   ensure that unfolding does not fail.

   .. example::

      .. rocqtop:: all reset abort

         Opaque id.
         Goal id 10 = 10.
         Fail unfold id.
         with_strategy transparent [id] unfold id.

   .. warning::

      Use this tactic with care, as effects do not persist past the
      end of the proof script.  Notably, this fine-tuning of the
      conversion strategy is not in effect during :cmd:`Qed` nor
      :cmd:`Defined`, so this tactic is most useful either in
      combination with :tacn:`abstract`, which will check the proof
      early while the fine-tuning is still in effect, or to guard
      calls to conversion in tactic automation to ensure that, e.g.,
      :tacn:`unfold` does not fail just because the user made a
      constant :cmd:`Opaque`.

      This can be illustrated with the following example involving the
      factorial function.

      .. rocqtop:: in reset

         Fixpoint fact (n : nat) : nat :=
           match n with
           | 0 => 1
           | S n' => n * fact n'
           end.

      Suppose now that, for whatever reason, we want in general to
      unfold the :g:`id` function very late during conversion:

      .. rocqtop:: in

         Strategy 1000 [id].

      If we try to prove :g:`id (fact n) = fact n` by
      :tacn:`reflexivity`, it will now take time proportional to
      :math:`n!`, because Rocq will keep unfolding :g:`fact` and
      :g:`*` and :g:`+` before it unfolds :g:`id`, resulting in a full
      computation of :g:`fact n` (in unary, because we are using
      :g:`nat`), which takes time :math:`n!`.  We can see this cross
      the relevant threshold at around :math:`n = 9`:

      .. rocqtop:: all abort

         Goal True.
         Time assert (id (fact 8) = fact 8) by reflexivity.
         Time assert (id (fact 9) = fact 9) by reflexivity.

      Note that behavior will be the same if you mark :g:`id` as
      :g:`Opaque` because while most reduction tactics refuse to
      unfold :g:`Opaque` constants, conversion treats :g:`Opaque` as
      merely a hint to unfold this constant last.

      We can get around this issue by using :tacn:`with_strategy`:

      .. rocqtop:: all

         Goal True.
         Fail Timeout 1 assert (id (fact 100) = fact 100) by reflexivity.
         Time assert (id (fact 100) = fact 100) by with_strategy -1 [id] reflexivity.

      However, when we go to close the proof, we will run into
      trouble, because the reduction strategy changes are local to the
      tactic passed to :tacn:`with_strategy`.

      .. rocqtop:: all abort fail

         exact I.
         Timeout 1 Defined.

      We can fix this issue by using :tacn:`abstract`:

      .. rocqtop:: all

         Goal True.
         Time assert (id (fact 100) = fact 100) by with_strategy -1 [id] abstract reflexivity.
         exact I.
         Time Defined.

      On small examples this sort of behavior doesn't matter, but
      because Rocq is a super-linear performance domain in so many
      places, unless great care is taken, tactic automation using
      :tacn:`with_strategy` may not be robustly performant when
      scaling the size of the input.

   .. warning::

      In much the same way this tactic does not play well with
      :cmd:`Qed` and :cmd:`Defined` without using :tacn:`abstract` as
      an intermediary, this tactic does not play well with ``rocqchk``,
      even when used with :tacn:`abstract`, due to the inability of
      tactics to persist information about conversion hints in the
      proof term. See `#12200
      <https://github.com/coq/coq/issues/12200>`_ for more details.
