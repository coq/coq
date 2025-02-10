==============================
Reasoning with inductive types
==============================

Applying constructors
---------------------

The tactics presented here specialize :tacn:`apply` and
:tacn:`eapply` to constructors of inductive types.

.. tacn:: constructor {? @nat_or_var } {? with @bindings }

   First does :n:`repeat intro; hnf` on the goal.  If the result is an inductive
   type :g:`I`, then apply the appropriate constructor(s), and otherwise fail.
   If :n:`@nat_or_var` is specified and has the
   value `i`, it uses :n:`apply c__i`, where :n:`c__i` is the i-th constructor
   of :g:`I`.  If not specified, the tactic tries all the constructors,
   which can result in more than one success (e.g. for `\\/`) when using
   backtracking tactics such as `constructor; ...`.  See :tacn:`ltac-seq`.

   :n:`{? with @bindings }`
     If specified, the :n:`apply` is done as :n:`apply … with @bindings`.

     .. warning::

        The terms in :token:`bindings` are checked in the context
        where constructor is executed and not in the context where :tacn:`apply`
        is executed (the introductions are not taken into account).

   .. exn:: Not an inductive product.
      :undocumented:

   .. exn:: Not enough constructors.
      :undocumented:

   .. exn:: The type has no constructors.
      :undocumented:

.. tacn:: split {? with @bindings }

   Equivalent to :n:`constructor 1 {? with @bindings }` when the
   conclusion is an inductive type with a single constructor.  The :n:`@bindings`
   specify any parameters required for the constructor. It is
   typically used to split conjunctions in the conclusion such as `A /\\ B` into
   two new goals `A` and `B`.

.. tacn:: exists {*, @bindings }

   Equivalent to :n:`constructor 1 with @bindings__i` for each set of bindings
   (or just :n:`constructor 1` if there are no :n:`@bindings`)
   when the conclusion is an
   inductive type with a single constructor.  It is typically used on
   existential quantifications in the form `exists x, P x.`

   .. exn:: Not an inductive goal with 1 constructor.
      :undocumented:

.. tacn:: left {? with @bindings }
          right {? with @bindings }

   These tactics apply only if :g:`I` has two constructors, for
   instance in the case of a disjunction `A \\/ B`.
   Then they are respectively equivalent to
   :n:`constructor 1 {? with @bindings }` and
   :n:`constructor 2 {? with @bindings }`.

   .. exn:: Not an inductive goal with 2 constructors.
      :undocumented:

.. tacn:: econstructor {? @nat_or_var {? with @bindings } }
          eexists {*, @bindings }
          esplit {? with @bindings }
          eleft {? with @bindings }
          eright {? with @bindings }

   These tactics behave like :tacn:`constructor`,
   :tacn:`exists`, :tacn:`split`, :tacn:`left` and :tacn:`right`,
   but they introduce existential variables instead of failing
   when a variable can't be instantiated
   (cf. :tacn:`eapply` and :tacn:`apply`).

.. example:: :tacn:`constructor`, :tacn:`left` and :tacn:`right`

   .. rocqtop:: reset all

      Print or.  (* or, represented by \/, has two constructors, or_introl and or_intror *)
      Goal  forall P1 P2 : Prop, P1 -> P1 \/ P2.
      constructor 1.  (* equivalent to "left" *)
      apply H.  (* success *)

   In contrast, we won't be able to complete the proof if we select constructor 2:

   .. rocqtop:: reset none

      Goal  forall P1 P2 : Prop, P1 -> P1 \/ P2.

   .. rocqtop:: all

      constructor 2.  (* equivalent to "right" *)

   You can also apply a constructor by name:

   .. rocqtop:: reset none

      Goal  forall P1 P2 : Prop, P1 -> P1 \/ P2.

   .. rocqtop:: all

      intros; apply or_introl.  (* equivalent to "left" *)


.. _CaseAnalysisAndInduction:

Case analysis
-------------

The tactics in this section implement case
analysis on inductive or coinductive objects (see :ref:`variants`).

.. comment Notes contrasting the various case analysis tactics:
   https://github.com/coq/coq/pull/14676#discussion_r697904963

.. tacn:: destruct {+, @induction_clause } {? @induction_principle }

   .. insertprodn induction_clause induction_arg

   .. prodn::
      induction_clause ::= @induction_arg {? as @or_and_intropattern } {? eqn : @naming_intropattern } {? @occurrences }
      induction_arg ::= @one_term_with_bindings
      | @natural

   Performs case analysis by generating a subgoal for each constructor of the
   inductive or coinductive type selected by :n:`@induction_arg`.  The selected
   subterm, after possibly doing an :tacn:`intros`, must have
   an inductive or coinductive type.  Unlike :tacn:`induction`,
   :n:`destruct` generates no induction hypothesis.

   In each new subgoal, the tactic replaces the selected subterm with the associated
   constructor applied to its arguments, if any.

   :n:`{+, @induction_clause }`
     Giving multiple :n:`@induction_clause`\s is equivalent to applying :n:`destruct`
     serially on each :n:`@induction_clause`.

   :n:`@induction_arg`
     + If :n:`@one_term` (in :n:`@one_term_with_bindings`)
       is an identifier :n:`@ident`:

       + If :n:`@ident` denotes a :n:`forall` variable in the
         goal, then :n:`destruct @ident` behaves like
         :tacn:`intros` :n:`until @ident; destruct @ident`.

       + If :n:`@ident` is no longer dependent in the
         goal after application of :n:`destruct`, it is erased. To avoid erasure,
         use parentheses, as in :n:`destruct (@ident)`.

     + :n:`@one_term` may contain holes that are denoted by “_”. In this case,
       the tactic selects the first subterm that matches the pattern and performs
       case analysis using that subterm.
     + If :n:`@induction_arg` is a :n:`@natural`, then :n:`destruct @natural` behaves like
       :n:`intros until @natural` followed by :n:`destruct` applied to the last
       introduced hypothesis.

   :n:`as @or_and_intropattern`
      Provides names for (or applies further transformations to)
      the variables and hypotheses introduced in each new subgoal.  The
      :token:`or_and_intropattern` must have one :n:`{* @intropattern }`
      for each constructor, given in the order in which the constructors are
      defined.  If there are not enough names, Rocq picks fresh names.
      Inner :n:`intropattern`\s can also split introduced hypotheses into
      multiple hypotheses or subgoals.

   :n:`eqn : @naming_intropattern`
      Generates a new hypothesis in each new subgoal that is an equality between
      the term being case-analyzed and the associated constructor (applied to
      its arguments).  The name of the new item may be specified in the
      :n:`@naming_intropattern`.

   :n:`with @bindings`  (in :n:`@one_term_with_bindings`)
      Provides explicit instances for
      the :term:`dependent premises <dependent premise>` of the type of
      :token:`one_term`.

   :n:`@occurrences`
     Selects specific subterms of the goal and/or hypotheses to apply
     the tactic to.  See :ref:`Occurrence clauses <occurrenceclauses>`.
     If it occurs in the :n:`@induction_principle`, then
     there can only be one :n:`@induction_clause`, which can't have its
     own :n:`@occurrences` clause.

   :n:`@induction_principle`
     Makes the tactic equivalent to
     :tacn:`induction` :n:`{+, @induction_clause } @induction_principle`.

   .. _example_destruct_ind_concl:

   .. example:: Using :tacn:`destruct` on an argument with premises

      .. rocqtop:: reset in

         Parameter A B C D : Prop.

      .. rocqtop:: all

         Goal (A -> B \/ C) -> D.
         intros until 1.
         destruct H.
         Show 2.
         Show 3.

      The single tactic :n:`destruct 1` is equivalent to the
      :tacn:`intros` and :tacn:`destruct` used here.

   .. tacn:: edestruct {+, @induction_clause } {? @induction_principle }

      If the type of :n:`@one_term` (in :n:`@induction_arg`) has
      :term:`dependent premises <dependent premise>`
      whose values can't be inferred from the :n:`with @bindings` clause,
      :n:`edestruct` turns them into existential variables to be resolved later on.

.. tacn:: case {+, @induction_clause } {? @induction_principle }

   An older, more basic tactic to perform case analysis without
   recursion.  We recommend using :tacn:`destruct` instead where possible.
   `case` only modifies the goal; it does not modify the :term:`local context`.

   .. tacn:: ecase {+, @induction_clause } {? @induction_principle }

      If the type of :n:`@one_term` (in :n:`@induction_arg`) has
      :term:`dependent premises <dependent premise>`
      whose values can't be inferred from the :n:`with @bindings` clause,
      :n:`ecase` turns them into existential variables to be resolved later on.

   .. tacn:: case_eq @one_term

      A variant of the :n:`case` tactic that allows
      performing case analysis on a term without completely forgetting its original
      form. This is done by generating equalities between the original form of the
      term and the outcomes of the case analysis.  We recommend using the
      :tacn:`destruct` tactic with an `eqn:` clause instead.

.. tacn:: simple destruct {| @ident | @natural }

   Equivalent to :tacn:`intros` :n:`until {| @ident | @natural }; case @ident`
   where :n:`@ident` is a :n:`forall` variable in the goal and otherwise fails.

.. tacn:: dependent destruction @ident {? generalizing {+ @ident } } {? using @one_term }
   :undocumented:

   .. note::
      This tactic requires the Stdlib library.

   There is a long example of :tacn:`dependent destruction` and an explanation
   of the underlying technique :ref:`here <dependent-induction-examples>`.

.. tacn:: decompose [ {+ @one_term } ] @one_term

   Recursively decomposes a complex proposition in order to obtain atomic ones.

   .. example::

      .. rocqtop:: reset all

         Goal forall A B C:Prop, A /\ B /\ C \/ B /\ C \/ C /\ A -> C.
           intros A B C H; decompose [and or] H.
           all: assumption.
         Qed.

   .. note::

      :tacn:`decompose` does not work on right-hand sides of implications or
      products.

   .. tacn:: decompose sum @one_term

      This decomposes sum types (like :g:`or`).

   .. tacn:: decompose record @one_term

      This decomposes record types (inductive types with one constructor,
      like :g:`and` and :g:`exists` and those defined with the :cmd:`Record`
      command.

.. tacn:: destauto {? in @ident }

   .. todo: keep or remove destauto?
      destauto added in https://github.com/coq/coq/commit/f3a53027589813ff19b3a7c46d84e5bd2fc65741

   Reduces one :n:`match t with ...` by doing :n:`destruct t`.  If :n:`t` is
   not a variable, the tactic does
   :n:`case_eq t;intros ... heq;rewrite heq in *|-`.
   :n:`heq` is preserved.

Induction
---------

.. tacn:: induction {+, @induction_clause } {? @induction_principle }

   .. insertprodn induction_principle induction_principle

   .. prodn::
      induction_principle ::= using @one_term_with_bindings {? @occurrences }

   Applies an :term:`induction principle` to generate a subgoal for
   each constructor of an inductive type.

   If the argument is :term:`dependent <dependent product>` in the conclusion or some
   hypotheses of the goal, the argument is replaced by the appropriate
   constructor in each of the resulting subgoals and induction
   hypotheses are added to the local context using names whose prefix
   is **IH**.  The tactic is similar to :tacn:`destruct`, except that
   `destruct` doesn't generate induction hypotheses.

   :n:`induction` and :tacn:`destruct` are very similar.  Aside from the following
   differences, please refer to the description of :tacn:`destruct` while mentally substituting
   :n:`induction` for :tacn:`destruct`.

   :n:`{+, @induction_clause }`
     If no :n:`@induction_principle` clause is provided, this is equivalent to doing
     :n:`induction` on the first :n:`@induction_clause` followed by :n:`destruct`
     on any subsequent clauses.

   :n:`@induction_principle`
     :n:`@one_term` specifies which :term:`induction principle` to use.  The
     optional :n:`with @bindings` gives any values that must be substituted
     into the induction principle.  The number of :n:`@bindings`
     must be the same as the number of parameters of the induction principle.

     If unspecified, the tactic applies the appropriate :term:`induction principle`
     that was automatically generated when the inductive type was declared based
     on the sort of the goal.

   .. exn:: Cannot recognize a statement based on @reference.

      The type of the :n:`@induction_arg` (in an :n:`@induction_clause`) must reduce to the
      :n:`@reference` which was inferred as the type the induction
      principle operates on. Note that it is not enough to be convertible, but you can
      work around that with :tacn:`change`:

      .. rocqtop:: reset all

         Definition N := nat.
         Axiom strong : forall P, (forall n:N, (forall m:N, m < n -> P m) -> P n)
           -> forall n, P n.

         Axiom P : N -> Prop.

         Goal forall n:nat, P n.
         intros.
         Fail induction n using strong.
         change N in n.
         (* n is now of type N, matching the inferred type that strong operates on *)
         induction n using strong.

   .. exn:: Unable to find an instance for the variables @ident … @ident.

      Use the :n:`with @bindings` clause or the :tacn:`einduction` tactic instead.

   .. example::

      .. rocqtop:: reset all

         Lemma induction_test : forall n:nat, n = n -> n <= n.
         intros n H.
         induction n.
         exact (le_n 0).

   .. example:: :n:`induction` with :n:`@occurrences`

      .. rocqtop:: reset all

         Lemma induction_test2 : forall n:nat, n = n -> n <= n.
         intros.
         induction n in H |-.
         Show 2.

   .. tacn:: einduction {+, @induction_clause } {? @induction_principle }

      Behaves like :tacn:`induction` except that it does not fail if
      some :term:`dependent premise` of the type of :n:`@one_term` can't be inferred. Instead,
      the unresolved premises are posed as existential variables to be inferred
      later, in the same way as :tacn:`eapply` does.

.. tacn:: elim @one_term_with_bindings {? using @one_term_with_bindings }

   An older, more basic induction tactic.  Unlike :tacn:`induction`, ``elim`` only
   modifies the goal; it does not modify the :term:`local context`.  We recommend
   using :tacn:`induction` instead where possible.

   :n:`with @bindings`   (in :n:`@one_term_with_bindings`)
     Explicitly gives instances to the premises of the type of :n:`@one_term`
     (see :ref:`bindings`).

   :n:`{? using @one_term_with_bindings }`
     Allows explicitly giving an induction principle :n:`@one_term` that
     is not the standard one for the underlying inductive type of :n:`@one_term`. The
     :n:`@bindings` clause allows instantiating premises of the type of
     :n:`@one_term`.

   .. tacn:: eelim @one_term_with_bindings {? using @one_term_with_bindings }

      If the type of :n:`@one_term` has dependent premises, this turns them into
      existential variables to be resolved later on.

.. tacn:: simple induction {| @ident | @natural }

   Behaves like :n:`intros until {| @ident | @natural }; elim @ident` when
   :n:`@ident` is a :n:`forall` variable in the goal.

.. tacn:: dependent induction @ident {? {| generalizing | in } {+ @ident } } {? using @one_term }

   .. note::
      This tactic requires the Stdlib library.

   The *experimental* tactic :tacn:`dependent induction` performs
   induction-inversion on an instantiated inductive predicate. One needs to first
   :cmd:`Require` the `Stdlib.Program.Equality` module to use this tactic. The tactic
   is based on the BasicElim tactic by Conor McBride
   :cite:`DBLP:conf/types/McBride00` and the work of Cristina Cornes around
   inversion :cite:`DBLP:conf/types/CornesT95`. From an instantiated
   inductive predicate and a goal, it generates an equivalent goal where
   the hypothesis has been generalized over its indexes which are then
   constrained by equalities to be the right instances. This permits to
   state lemmas without resorting to manually adding these equalities and
   still get enough information in the proofs.

   :n:`{| generalizing | in } {+ @ident }`
     First generalizes the goal by the given variables so that they are universally
     quantified in the goal.  This is generally what one wants to do with
     variables that are inside constructors in the induction hypothesis.  The other
     ones need not be further generalized.

   There is a long example of :tacn:`dependent induction` and an explanation
   of the underlying technique :ref:`here <dependent-induction-examples>`.

   .. example::

      .. rocqtop:: reset all

         Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
         intros n H ; induction H.

      Here we did not get any information on the indexes to help fulfill
      this proof. The problem is that, when we use the ``induction`` tactic, we
      lose information on the hypothesis instance, notably that the second
      argument is 1 here. Dependent induction solves this problem by adding
      the corresponding equality to the context.

      .. rocqtop:: reset all extra-stdlib

         Require Import Stdlib.Program.Equality.
         Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
         intros n H ; dependent induction H.

      The subgoal is cleaned up as the tactic tries to automatically
      simplify the subgoals with respect to the generated equalities. In
      this enriched context, it becomes possible to solve this subgoal.

      .. rocqtop:: all extra-stdlib

         reflexivity.

      Now we are in a contradictory context and the proof can be solved.

      .. rocqtop:: all abort extra-stdlib

         inversion H.

      This technique works with any inductive predicate. In fact, the
      :tacn:`dependent induction` tactic is just a wrapper around the :tacn:`induction`
      tactic. One can make its own variant by just writing a new tactic
      based on the definition found in ``Stdlib.Program.Equality``.

   .. seealso:: :tacn:`functional induction`

.. tacn:: fix @ident @natural {? with {+ ( @ident {* @simple_binder } {? %{ struct @name %} } : @type ) } }

   A primitive tactic that starts a proof by induction. Generally,
   higher-level tactics such as :tacn:`induction` or :tacn:`elim`
   are easier to use.

   The :n:`@ident`\s (including the first one before the `with`
   clause) are the names of
   the induction hypotheses. :n:`@natural` tells on which
   premise of the current goal the induction acts, starting from 1,
   counting both dependent and non-dependent products, but skipping local
   definitions. The current lemma must be composed of at
   least :n:`@natural` products.

   As in a fix expression, induction hypotheses must be used on
   structurally smaller arguments. The verification that inductive proof
   arguments are correct is done only when registering the
   lemma in the global environment. To know if the use of induction hypotheses
   is correct during the interactive development of a proof, use
   the command :cmd:`Guarded`.

   :n:`with {+ ( @ident {* @simple_binder } {? %{ struct @name %} } : @type ) }`
     Starts a proof by mutual induction. The statements to be proven
     are :n:`forall @simple_binder__i, @type__i`.
     The identifiers :n:`@ident` (including the first one before the `with` clause)
     are the names of the induction hypotheses. The identifiers
     :n:`@name` (in the `{ struct ... }` clauses) are the respective names of
     the premises on which the induction
     is performed in the statements to be proved (if not given, Rocq
     guesses what they are).

.. tacn:: cofix @ident {? with {+ ( @ident {* @simple_binder } : @type ) } }

   Starts a proof by coinduction. The :n:`@ident`\s (including the first one
   before the `with` clause) are the
   names of the coinduction hypotheses. As in a cofix expression,
   the use of induction hypotheses must be guarded by a constructor. The
   verification that the use of coinductive hypotheses is correct is
   done only at the time of registering the lemma in the global environment. To
   know if the use of coinduction hypotheses is correct at some time of
   the interactive development of a proof, use the command :cmd:`Guarded`.

   :n:`with {+ ( @ident {* @simple_binder } : @type ) }`
     Starts a proof by mutual coinduction. The statements to be
     proven are :n:`forall @simple_binder__i, @type__i`.
     The identifiers :n:`@ident` (including the first one before the `with` clause)
     are the names of the coinduction hypotheses.

.. _equality-inductive_types:

Equality of inductive types
---------------------------

This section describes some special purpose tactics to work with
:term:`Leibniz equality` of inductive sets or types.

.. tacn:: discriminate {? @induction_arg }

   Proves goals for which a hypothesis or a :term:`premise` in
   the goal that is convertible to the form :n:`@term__1 = @term__2`
   has inconsistent constructors between the two sides of
   the equality (i.e., a contradiction).  The tactic also works for goals
   in the form :n:`@term__1 <> @term__2` that are inconsistent
   (:ref:`example <discriminate_goal_inequality_ex>`).

   If :n:`@induction_arg` is provided, only the provided proof term or
   hypothesis is checked for inconsistency.
   If :n:`@induction_arg` is not given, the tactic does an :tacn:`intro`
   for each premise in the goal, then it checks all the resulting hypotheses
   for impossible equalities.

   The tactic relies on the fact that constructors of inductive types are injective
   and disjoint, i.e. if `C1` and `C2` are distinct constructors of an inductive type then
   :n:`C1 @term__1 = C1 @term__2` implies that :n:`@term__1 = @term__2` (injectivity)
   and :n:`C1 @term__1 = C2 @term__2` is a contradiction (disjointedness).
   For example, :g:`S (S O) = S O` is a contradiction: while
   the outermost constructors are both `S`, the next ones differ (`S` versus `O`).

   The tactic traverses the normal forms of :n:`@term__1` and :n:`@term__2`,
   looking for subterms placed in the same positions whose
   head symbols are different constructors. If such subterms are present, the
   equality is impossible and the current goal is completed.
   Otherwise the tactic fails.  Note that opaque constants are not expanded by
   δ reductions while computing the head normal form.

   Note that :n:`discriminate` doesn't handle contradictory equalities such as
   :g:`n = S n`.  In this case you must use :tacn:`induction` (see
   :ref:`example <discriminate_example>`).

   :n:`@ident`  (as :n:`@induction_arg`)
     Checks the hypothesis :n:`@ident` for impossible equalities.
     If :n:`@ident` is not already in the context, this is equivalent to
     :n:`intros until @ident; discriminate @ident`.

   :n:`@natural` (as :n:`@induction_arg`)
     Equivalent to :tacn:`intros` :n:`until @natural; discriminate @ident`,
     where :n:`@ident` is the identifier for the last introduced hypothesis.

   :n:`@one_term with @bindings`  (in :n:`@induction_arg`)
     Equivalent to :n:`discriminate @one_term` but uses the given
     bindings to instantiate parameters or hypotheses of :n:`@one_term`.
     :n:`@one_term` must be a proof of :n:`@term__1 = @term__2`.

   .. exn:: No primitive equality found.
      :undocumented:

   .. exn:: Not a discriminable equality.
      :undocumented:

   .. tacn:: ediscriminate {? @induction_arg }

      Works the same as :tacn:`discriminate` but if the type of :token:`one_term`, or the
      type of the hypothesis referred to by :token:`natural`, has uninstantiated
      parameters, these parameters are left as existential variables.

.. _discriminate_goal_inequality_ex:

   .. example:: Proving `1 <> 2`

      .. rocqtop:: reset in

         Goal 1 <> 2.
         discriminate.
         Qed.

      This works because `1 <> 2` is represented internally as `not (1 = 2)`,
      which is just `(1 = 2) -> False` from the definition of `not`:

      .. rocqtop:: all

         Print not.

      You can see this better by doing the :n:`intro` explicitly:

      .. rocqtop:: in

         Goal 1 <> 2.

      .. rocqtop:: all

         intro.      (* if omitted, "discriminate" does an intro *)

      .. rocqtop:: in

         discriminate.
         Qed.

.. _discriminate_example:

   .. example:: :n:`discriminate` limitation: proving `n <> S n`

      .. rocqtop:: reset in

         Goal forall n:nat, n <> S n.
         intro n.
         induction n.

      .. rocqtop:: all

         - discriminate.       (* works: O and (S O) start with different constructors *)
         - Fail discriminate.  (* fails: discriminate doesn't handle this case *)
           injection.

      .. rocqtop:: in

           assumption.
           Qed.

.. tacn:: injection {? @induction_arg } {? as {* @simple_intropattern } }

   Exploits the property that constructors of
   inductive types are injective, i.e. that if :n:`c` is a constructor of an
   inductive type and :n:`c t__1 = c t__2` then
   :n:`t__1 = t__2` are equal too.

   If there is a hypothesis `H` in the form :n:`@term__1 = @term__2`,
   then :n:`injection H` applies the injectivity of constructors as deep as
   possible to derive the equality of subterms of :n:`@term__1` and
   :n:`@term__2` wherever the subterms start to differ. For example, from
   :g:`(S p, S n) = (q, S (S m))` we may derive :g:`S p = q` and
   :g:`n = S m`. The terms must have inductive types and the same head
   constructor, but must not be convertible. If so, the tactic derives the
   equalities and adds them to the current goal as :term:`premises <premise>`
   (except if the :n:`as` clause is used).

   If no :n:`induction_arg` is provided and the current goal is of the form
   :n:`@term <> @term`, :tacn:`injection` is equivalent to
   :n:`intro @ident; injection @ident`.

   :n:`@ident`  (in :n:`@induction_arg`)
     Derives equalities based on constructor injectivity for the hypothesis
     :n:`@ident`.
     If :n:`@ident` is not already in the context, this is equivalent to
     :n:`intros until @ident; injection @ident`.

   :n:`@natural` (in :n:`@induction_arg`)
     Equivalent to :tacn:`intros` :n:`until @natural` followed by
     :n:`injection @ident` where :n:`@ident` is the identifier for the last
     introduced hypothesis.

   :n:`@one_term with @bindings`  (in :n:`@induction_arg`)
     Like :n:`injection @one_term` but uses the given bindings to
     instantiate parameters or hypotheses of :n:`@one_term`.

   :n:`as [= {* @intropattern } ]`
     Specifies names to apply after the injection so
     that all generated equalities become hypotheses, which (unlike :tacn:`intros`)
     may replace existing hypotheses with same name.  The number of
     provided names must not exceed
     the number of newly generated equalities. If it is smaller, fresh
     names are generated for the unspecified items. The original equality is
     erased if it corresponds to a provided name or if the list of provided
     names is incomplete.

     Note that, as a convenience for users, specifying
     :n:`{+ @simple_intropattern }` is treated as if
     :n:`[= {+ @simple_intropattern } ]` was specified.

   .. example::

      Consider the following goal:

      .. rocqtop:: in

         Inductive list : Set :=
         | nil : list
         | cons : nat -> list -> list.
         Parameter P : list -> Prop.
         Goal forall l n, P nil -> cons n l = cons 0 nil -> P l.

      .. rocqtop:: all

         intros.
         injection H0.

   .. note::
      Beware that injection yields an equality in a sigma type whenever the
      injected object has a dependent type :g:`P` with its two instances in
      different types :n:`(P t__1 … t__n)` and :n:`(P u__1 … u__n)`. If :n:`t__1` and
      :n:`u__1` are the same and have for type an inductive type for which a decidable
      equality has been declared using :cmd:`Scheme Equality`,
      the use of a sigma type is avoided.

   .. exn:: No information can be deduced from this equality and the injectivity of constructors. This may be because the terms are convertible, or due to pattern matching restrictions in the sort Prop. You can try to use option Set Keep Proof Equalities.
      :undocumented:

   .. exn:: Not a negated primitive equality

      When :n:`@induction_arg` is not provided, the goal must be in the form
      :n:`@term <> @term`.

   .. exn:: Nothing to inject.

      Generated when one side of the equality is not a constructor.

   .. tacn:: einjection {? @induction_arg } {? as {* @simple_intropattern } }

      Works the same as :n:`injection` but if the type of :n:`@one_term`, or the
      type of the hypothesis referred to by :n:`@natural` has uninstantiated
      parameters, these parameters are left as existential variables.

   .. tacn:: simple injection {? @induction_arg }

      Similar to :tacn:`injection`, but always adds the derived equalities
      as new :term:`premises <premise>` in the current goal (instead of as
      new hypotheses) even if the :flag:`Structural Injection` flag is set.

   .. flag:: Structural Injection

      When this :term:`flag` is set, :n:`injection @term` erases the original hypothesis
      and adds the generated equalities as new hypotheses rather than adding them
      to the current goal as :term:`premises <premise>`, as if giving :n:`injection @term as`
      (with an empty list of names). This flag is off by default.

   .. flag:: Keep Proof Equalities

      By default, :tacn:`injection` only creates new equalities between :n:`@term`\s
      whose type is in sort :g:`Type` or :g:`Set`, thus implementing a special
      behavior for objects that are proofs of a statement in :g:`Prop`. This :term:`flag`
      controls this behavior.

   .. table:: Keep Equalities @qualid

      This :term:`table` specifies a set of inductive types for which proof
      equalities are always kept by :tacn:`injection`. This overrides the
      :flag:`Keep Proof Equalities` flag for those inductive types.
      Use the :cmd:`Add` and :cmd:`Remove` commands to update this set manually.

.. tacn:: simplify_eq {? @induction_arg }

   Examines a hypothesis that has the form :n:`@term__1 = @term__2`.  If the terms are
   structurally different, the tactic does a :tacn:`discriminate`.  Otherwise, it does
   an :tacn:`injection` to simplify the equality, if possible.  If :n:`induction_arg`
   is not provided, the tactic examines the goal, which must be in the form
   :n:`@term__1 <> @term__2`.

   See the description of :token:`induction_arg` in :tacn:`injection` for an
   explanation of the parameters.

   .. tacn:: esimplify_eq {? @induction_arg }

      Works the same as :tacn:`simplify_eq` but if the type of :n:`@one_term` or the
      type of the hypothesis referred to by :n:`@natural` has uninstantiated
      parameters, these parameters are left as existential variables.

.. tacn:: inversion {| @ident | @natural } {? as @or_and_intropattern } {? in {+ @ident } }
          inversion {| @ident | @natural } using @one_term {? in {+ @ident } }
   :name: inversion; _

   .. comment: the other inversion* tactics don't support the using clause,
      but they should be able to, if desired.  It wouldn't make sense for
      inversion_sigma.
      See https://github.com/coq/coq/pull/14179#discussion_r642193096

   For a hypothesis whose type is a (co)inductively defined
   proposition, the tactic introduces a goal for each constructor
   of the proposition that isn't self-contradictory.  Each such goal
   includes the hypotheses needed to deduce the proposition.
   :gdef:`(Co)inductively defined propositions <inductively defined proposition>`
   are those defined with the :cmd:`Inductive` or :cmd:`CoInductive` commands whose
   contructors yield a `Prop`, as in this :ref:`example <inversion-intropattern-ex>`.


   :n:`@ident`
     The name of the hypothesis to invert.
     If :n:`@ident` does not denote a hypothesis in the local context but
     refers to a hypothesis quantified in the goal, then the latter is
     first introduced in the local context using :n:`intros until @ident`.

   :n:`@natural`
     Equivalent to :n:`intros until @natural; inversion @ident`
     where :n:`@ident` is the identifier for the last introduced hypothesis.

   :n:`{? in {+ @ident } }`
     When :n:`{+ @ident}` are identifiers in the local context, this does
     a :tacn:`generalize` :n:`{+ @ident}` as the initial step of `inversion`.

   :n:`as @or_and_intropattern`
     Provides names for the variables introduced in each new subgoal.  The
     :token:`or_and_intropattern` must have one :n:`{* @intropattern }`
     for each constructor of the (co)inductive predicate, given in the order
     in which the constructors are defined.
     If there are not enough names, Rocq picks fresh names.

     If an equation splits into several
     equations (because ``inversion`` applies ``injection`` on the equalities it
     generates), the corresponding :n:`@intropattern` should be in the form
     :n:`[ {* @intropattern } ]` (or the equivalent :n:`{*, ( @simple_intropattern ) }`),
     with the number of entries equal to the number
     of subequalities obtained from splitting the original equation.
     Example :ref:`here <inversion-intropattern-ex>`.

   .. note::
      The ``inversion … as`` variant of
      ``inversion`` generally behaves in a slightly more expected way than
      ``inversion`` (no artificial duplication of some hypotheses referring to
      other hypotheses). To take advantage of these improvements, it is enough to use
      ``inversion … as []``, letting Rocq choose fresh names.

   .. note::
      As ``inversion`` proofs may be large, we recommend
      creating and using lemmas whenever the same instance needs to be
      inverted several times. See :ref:`derive-inversion`.

   .. note::
      Part of the behavior of the :tacn:`inversion` tactic is to generate
      equalities between expressions that appeared in the hypothesis that is
      being processed. By default, no equalities are generated if they
      relate two proofs (i.e. equalities between :token:`term`\s whose type is in sort
      :g:`Prop`). This behavior can be turned off by using the
      :flag:`Keep Proof Equalities` setting.

.. _inversion-intropattern-ex:

   .. example:: :tacn:`inversion` with :n:`as @or_and_intropattern`

      .. rocqtop:: reset all

         Inductive contains0 : list nat -> Prop :=
         | in_hd : forall l, contains0 (0 :: l)
         | in_tl : forall l b, contains0 l -> contains0 (b :: l).

      .. rocqtop:: in

         Goal forall l:list nat, contains0 (1 :: l) -> contains0 l.

      .. rocqtop:: all

         intros l H.
         inversion H as [ | l' p Hl' [Heqp Heql'] ].

   .. tacn:: inversion_clear {| @ident | @natural } {? as @or_and_intropattern } {? in {+ @ident } }

      Does an :tacn:`inversion` and then erases the hypothesis that was used for
      the inversion.

   .. tacn:: simple inversion {| @ident | @natural } {? as @or_and_intropattern } {? in {+ @ident } }

      A very simple inversion tactic that derives all the necessary
      equalities but does not simplify the constraints as :tacn:`inversion` does.

   .. tacn:: dependent inversion {| @ident | @natural } {? as @or_and_intropattern } {? with @one_term }

      For use when the inverted hypothesis appears in the current goal.
      Does an :tacn:`inversion` and then substitutes the name of the hypothesis
      where the corresponding term appears in the goal.

   .. tacn:: dependent inversion_clear {| @ident | @natural } {? as @or_and_intropattern } {? with @one_term }

      Does a :tacn:`dependent inversion` and then erases the hypothesis that was used for
      the dependent inversion.

   .. tacn:: dependent simple inversion {| @ident | @natural } {? as @or_and_intropattern } {? with @one_term }
      :undocumented:

.. tacn:: inversion_sigma {? @ident {? as @simple_intropattern } }

   .. note::
      This tactic requires the Stdlib library.

   Turns equalities of dependent pairs (e.g.,
   :g:`existT P x p = existT P y q`, frequently left over by :tacn:`inversion` on
   a dependent type family) into pairs of equalities (e.g., a hypothesis
   :g:`H : x = y` and a hypothesis of type :g:`rew H in p = q`); these
   hypotheses can subsequently be simplified using :tacn:`subst`, without ever
   invoking any kind of axiom asserting uniqueness of identity proofs. If you
   want to explicitly specify the hypothesis to be inverted, you can pass it as
   an argument to :tacn:`inversion_sigma`. This tactic also works for
   :g:`sig`, :g:`sigT2`, :g:`sig2`, :g:`ex`, and :g:`ex2` and there are similar :g:`eq_sig`
   :g:`***_rect` induction lemmas.


   .. exn:: Type of @ident is not an equality of recognized Σ types: expected one of sig sig2 sigT sigT2 sigT2 ex or ex2 but got @term

      When applied to a hypothesis, :tacn:`inversion_sigma` can only handle equalities of the
      listed sigma types.

   .. exn:: @ident is not an equality of Σ types

      When applied to a hypothesis, :tacn:`inversion_sigma` can only be called on hypotheses that
      are equalities using :g:`Stdlib.Logic.Init.eq`.

.. example:: Non-dependent inversion

   Let us consider the relation :g:`Le` over natural numbers:

   .. rocqtop:: reset in

      Inductive Le : nat -> nat -> Set :=
      | LeO : forall n:nat, Le 0 n
      | LeS : forall n m:nat, Le n m -> Le (S n) (S m).


   Let us consider the following goal:

   .. rocqtop:: none

      Section Section.
      Variable P : nat -> nat -> Prop.
      Variable Q : forall n m:nat, Le n m -> Prop.
      Goal forall n m, Le (S n) m -> P n m.

   .. rocqtop:: out

      intros.

   To prove the goal, we may need to reason by cases on :g:`H` and to derive
   that :g:`m` is necessarily of the form :g:`(S m0)` for certain :g:`m0` and that
   :g:`(Le n m0)`. Deriving these conditions corresponds to proving that the only
   possible constructor of :g:`(Le (S n) m)` is :g:`LeS` and that we can invert
   the arrow in the type of :g:`LeS`. This inversion is possible because :g:`Le`
   is the smallest set closed by the constructors :g:`LeO` and :g:`LeS`.

   .. rocqtop:: all

      inversion_clear H.

   Note that :g:`m` has been substituted in the goal for :g:`(S m0)` and that the
   hypothesis :g:`(Le n m0)` has been added to the context.

   Sometimes it is interesting to have the equality :g:`m = (S m0)` in the
   context to use it after. In that case we can use :tacn:`inversion` that does
   not clear the equalities:

   .. rocqtop:: none restart

      intros.

   .. rocqtop:: all

      inversion H.

.. example:: Dependent inversion

   Let us consider the following goal:

   .. rocqtop:: none

      Abort.
      Goal forall n m (H:Le (S n) m), Q (S n) m H.

   .. rocqtop:: out

      intros.

   As :g:`H` occurs in the goal, we may want to reason by cases on its
   structure and so, we would like inversion tactics to substitute :g:`H` by
   the corresponding @term in constructor form. Neither :tacn:`inversion` nor
   :tacn:`inversion_clear` do such a substitution. To have such a behavior we
   use the dependent inversion tactics:

   .. rocqtop:: all

      dependent inversion_clear H.

   Note that :g:`H` has been substituted by :g:`(LeS n m0 l)` and :g:`m` by :g:`(S m0)`.

.. example:: Using :tacn:`inversion_sigma`

   Let us consider the following inductive type of
   length-indexed lists, and a lemma about inverting equality of cons:

   .. rocqtop:: reset all extra-stdlib

      Require Import Stdlib.Logic.Eqdep_dec.

      Inductive vec A : nat -> Type :=
      | nil : vec A O
      | cons {n} (x : A) (xs : vec A n) : vec A (S n).

      Lemma invert_cons : forall A n x xs y ys,
               @cons A n x xs = @cons A n y ys
               -> xs = ys.

      Proof.
      intros A n x xs y ys H.

   After performing inversion, we are left with an equality of existTs:

   .. rocqtop:: all extra-stdlib

      inversion H.

   We can turn this equality into a usable form with inversion_sigma:

   .. rocqtop:: all extra-stdlib

      inversion_sigma.

   To finish cleaning up the proof, we will need to use the fact that
   that all proofs of n = n for n a nat are eq_refl:

   .. rocqtop:: all extra-stdlib

      let H := match goal with H : n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
      simpl in *.

   Finally, we can finish the proof:

   .. rocqtop:: all extra-stdlib

      assumption.
      Qed.

.. seealso:: :tacn:`functional inversion`

Helper tactics
~~~~~~~~~~~~~~

.. tacn:: decide @one_term__1 with @one_term__2

   Replaces occurrences of :n:`@one_term__1` in the form :g:`{P}+{~P}` in the goal
   with :g:`(left _)` or :g:`(right _)`, depending on :n:`@one_term__2`.
   :n:`@one_term__2` must be of type either :g:`P` or :g:`~P`,
   and :g:`P` must be of type :g:`Prop`.

   .. example:: Using :tacn:`decide` to rewrite the goal

      .. rocqtop:: in extra-stdlib

         Goal forall (P Q : Prop) (Hp : {P} + {~P}) (Hq : {Q} + {~Q}),
             P -> ~Q -> (if Hp then true else false) = (if Hq then false else true).

      .. rocqtop:: all extra-stdlib

         intros P Q Hp Hq p nq.
         decide Hp with p.
         decide Hq with nq.

      .. rocqtop:: in extra-stdlib

         reflexivity.
         Qed.

.. tacn:: decide equality

   Solves a goal of the form :n:`{? forall x y : R, } {x = y} + {~ x = y}` or
   :n:`{? forall x y : R, } (x = y) \/ (~ x = y)`, where :g:`R` is an
   inductive type whose constructors do not take proofs or functions as
   arguments, nor objects in dependent types.

.. tacn:: compare @one_term__1 @one_term__2

   Compares two :n:`@one_term`\s of an
   inductive datatype. If :g:`G` is the current goal, it leaves the
   sub-goals :n:`@one_term__1 = @one_term__2 -> G` and :n:`~ @one_term__1 = @one_term__2 -> G`.
   The type of the :n:`@one_term`\s must satisfy the same restrictions as in the
   tactic :tacn:`decide equality`.

.. tacn:: dependent rewrite {? {| -> | <- } } @one_term {? in @ident }

   If :n:`@ident` has type
   :g:`(existT B a b)=(existT B a' b')` in the local context (i.e. each
   term of the equality has a sigma type :g:`{ a:A & (B a)}`) this tactic
   rewrites :g:`a` into :g:`a'` and :g:`b` into :g:`b'` in the current goal.
   This tactic works even if :g:`B` is also a sigma type. This kind of
   equalities between dependent pairs may be derived by the
   :tacn:`injection` and :tacn:`inversion` tactics.

   :n:`{? {| -> | <- } }`
     By default, the equality is applied from left to right.  Specify `<-` to
     apply the equality from right to left.

.. _proofschemes-induction-principles:

Generation of induction principles with ``Scheme``
--------------------------------------------------------

.. cmd:: Scheme {? @ident := } @scheme_kind {* with {? @ident := } @scheme_kind }

   .. insertprodn scheme_kind sort_family scheme_type

   .. prodn::
      scheme_kind ::= @scheme_type for @reference Sort @sort_family
      scheme_type ::= Induction
      | Minimality
      | Elimination
      | Case
      sort_family ::= Prop
      | SProp
      | Set
      | Type

   Generates :term:`induction principles <induction principle>` with given
   :n:`scheme_type`\s and :n:`scheme_sort`\s for an inductive type. In the case
   where the inductive definition is a mutual inductive definition, the
   :n:`with` clause is used to generate a mutually recursive inductive scheme
   for each clause of the mutual inductive type.

   :n:`@ident`
      The name of the scheme. If not provided, the name will be determined
      automatically from the :n:`@scheme_type` and :n:`@sort_family`.

   The following :n:`@scheme_type`\s generate induction principles with
   given properties:

   =================== =========== ===========
    :n:`@scheme_type`   Recursive   Dependent
   =================== =========== ===========
    :n:`Induction`         Yes         Yes
    :n:`Minimality`        Yes         No
    :n:`Elimination`       No          Yes
    :n:`Case`              No          No
   =================== =========== ===========

   See examples of the :n:`@scheme_type`\s :ref:`here <scheme_example>`.

.. cmd:: Scheme {? Boolean } Equality for @reference
   :name: Scheme Equality; Scheme Boolean Equality

   Tries to generate a Boolean equality for :n:`@reference`. If
   :n:`Boolean` is not specified, the command also tries to generate
   a proof of the decidability of propositional equality over
   :n:`@reference`.
   If :token:`reference` involves independent constants or other
   inductive types, we recommend defining their equality first.

.. example:: Induction scheme for tree and forest

   Currently the automatically-generated :term:`induction principles <induction principle>`
   such as `odd_ind` are not useful for mutually-inductive types such as `odd` and `even`.
   You can define a mutual induction principle for tree and forest in sort ``Set`` with
   the :cmd:`Scheme` command:

    .. rocqtop:: reset none

       Axiom A : Set.
       Axiom B : Set.

    .. rocqtop:: in

     Inductive tree : Set :=
     | node : A -> forest -> tree
     with forest : Set :=
     | leaf : B -> forest
     | cons : tree -> forest -> forest.

    .. rocqtop:: all

     Scheme tree_forest_rec := Induction for tree Sort Set
       with forest_tree_rec := Induction for forest Sort Set.

  You may now look at the type of tree_forest_rec:

  .. rocqtop:: all

    Check tree_forest_rec.

  This principle involves two different predicates for trees and forests;
  it also has three premises each one corresponding to a constructor of
  one of the inductive definitions.

  The principle `forest_tree_rec` shares exactly the same premises, only
  the conclusion now refers to the property of forests.

.. example:: Predicates odd and even on naturals

  Let odd and even be inductively defined as:

   .. rocqtop:: in

      Inductive odd : nat -> Prop :=
      | oddS : forall n : nat, even n -> odd (S n)
      with even : nat -> Prop :=
      | evenO : even 0
      | evenS : forall n : nat, odd n -> even (S n).

  The following command generates a powerful elimination principle:

   .. rocqtop:: all

    Scheme odd_even := Minimality for odd Sort Prop
    with even_odd := Minimality for even Sort Prop.

  The type of odd_even for instance will be:

  .. rocqtop:: all

    Check odd_even.

  The type of `even_odd` shares the same premises but the conclusion is
  `forall n : nat, even n -> P0 n`.

.. _scheme_example:

   .. example:: `Scheme` commands with various :n:`@scheme_type`\s

      Let us demonstrate the difference between the Scheme commands.

      .. rocqtop:: all

         Unset Elimination Schemes.

         Inductive Nat :=
         | z : Nat
         | s : Nat -> Nat.

         (* dependent, recursive *)
         Scheme Induction for Nat Sort Set.
         About Nat_rec.

         (* non-dependent, recursive *)
         Scheme Minimality for Nat Sort Set.
         About Nat_rec_nodep.

         (* dependent, non-recursive *)
         Scheme Elimination for Nat Sort Set.
         About Nat_case.

         (* non-dependent, non-recursive *)
         Scheme Case for Nat Sort Set.
         About Nat_case_nodep.

Automatic declaration of schemes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Elimination Schemes

   This :term:`flag` enables automatic declaration of induction principles when defining a new
   inductive type.  Defaults to on.

.. flag:: Nonrecursive Elimination Schemes

   This :term:`flag` enables automatic declaration of induction
   principles for types declared with the :cmd:`Variant` and
   :cmd:`Record` commands.  Defaults to off.

.. flag:: Case Analysis Schemes

   This :term:`flag` governs the generation of case analysis lemmas for inductive types,
   i.e. corresponding to the pattern matching term alone and without fixpoint.

.. flag:: Boolean Equality Schemes
          Decidable Equality Schemes

   These :term:`flags <flag>` control the automatic declaration of those Boolean equalities (see
   the second variant of ``Scheme``).

.. warning::

   You have to be careful with these flags since Rocq may now reject well-defined
   inductive types because it cannot compute a Boolean equality for them.

.. flag:: Rewriting Schemes

   This :term:`flag` governs generation of equality-related schemes such as congruence.

Combined Scheme
~~~~~~~~~~~~~~~

.. cmd:: Combined Scheme @ident__def from {+, @ident }

   Combines induction principles generated
   by the :cmd:`Scheme` command.
   Each :n:`@ident` is a different inductive principle that must  belong
   to the same package of mutual inductive principle definitions.
   This command generates :n:`@ident__def` as the conjunction of the
   principles: it is built from the common premises of the principles
   and concluded by the conjunction of their conclusions.
   In the case where all the inductive principles used are in sort
   ``Prop``, the propositional conjunction ``and`` is used, otherwise
   the simple product ``prod`` is used instead.

.. example::

  We can define the induction principles for trees and forests using:

  .. rocqtop:: all

    Scheme tree_forest_ind := Induction for tree Sort Prop
    with forest_tree_ind := Induction for forest Sort Prop.

  Then we can build the combined induction principle which gives the
  conjunction of the conclusions of each individual principle:

  .. rocqtop:: all

    Combined Scheme tree_forest_mutind from tree_forest_ind,forest_tree_ind.

  The type of tree_forest_mutind will be:

  .. rocqtop:: all

    Check tree_forest_mutind.

.. example::

   We can also combine schemes at sort ``Type``:

  .. rocqtop:: all

     Scheme tree_forest_rect := Induction for tree Sort Type
     with forest_tree_rect := Induction for forest Sort Type.

  .. rocqtop:: all

     Combined Scheme tree_forest_mutrect from tree_forest_rect, forest_tree_rect.

  .. rocqtop:: all

     Check tree_forest_mutrect.

.. seealso:: :ref:`functional-scheme`

.. _derive-inversion:

Generation of inversion principles with ``Derive`` ``Inversion``
-----------------------------------------------------------------

.. cmd:: Derive Inversion @ident with @one_term {? Sort @sort_family }

   Generates an inversion lemma for the
   :tacn:`inversion` tactic.  :token:`ident` is the name
   of the generated lemma.  :token:`one_term` should be in the form
   :token:`qualid` or :n:`(forall {+ @binder }, @qualid @term)` where
   :token:`qualid` is the name of an inductive
   predicate and :n:`{+ @binder }` binds the variables occurring in the term
   :token:`term`. The lemma is generated for the sort
   :token:`sort_family` corresponding to :token:`one_term`.
   Applying the lemma is equivalent to inverting the instance with the
   :tacn:`inversion` tactic.

.. cmd:: Derive Inversion_clear @ident with @one_term {? Sort @sort_family }

   When applied, it is equivalent to having inverted the instance with the
   tactic inversion replaced by the tactic `inversion_clear`.

.. cmd:: Derive Dependent Inversion @ident with @one_term Sort @sort_family

   When applied, it is equivalent to having inverted the instance with
   the tactic `dependent inversion`.

.. cmd:: Derive Dependent Inversion_clear @ident with @one_term Sort @sort_family

   When applied, it is equivalent to having inverted the instance
   with the tactic `dependent inversion_clear`.

.. example::

  Consider the relation `Le` over natural numbers and the following
  parameter ``P``:

  .. rocqtop:: all

    Inductive Le : nat -> nat -> Set :=
    | LeO : forall n:nat, Le 0 n
    | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

    Parameter P : nat -> nat -> Prop.

  To generate the inversion lemma for the instance :g:`(Le (S n) m)` and the
  sort :g:`Prop`, we do:

  .. rocqtop:: all

    Derive Inversion_clear leminv with (forall n m:nat, Le (S n) m) Sort Prop.
    Check leminv.

  Then we can use the proven inversion lemma:

  .. rocqtop:: none

    Goal forall (n m : nat) (H : Le (S n) m), P n m.
    intros.

  .. rocqtop:: all

    Show.

    inversion H using leminv.

.. _dependent-induction-examples:

Examples of :tacn:`dependent destruction` / :tacn:`dependent induction`
-----------------------------------------------------------------------

.. note::
   These tactics require the Stdlib library.

The tactics :tacn:`dependent induction` and :tacn:`dependent destruction` are another
solution for inverting inductive predicate instances and potentially
doing induction at the same time. It is based on the ``BasicElim`` tactic
of Conor McBride which works by abstracting each argument of an
inductive instance by a variable and constraining it by equalities
afterwards. This way, the usual induction and destruct tactics can be
applied to the abstracted instance and after simplification of the
equalities we get the expected goals.

The abstracting tactic is called generalize_eqs and it takes as
argument a hypothesis to generalize. It uses the JMeq datatype
defined in Stdlib.Logic.JMeq, hence we need to require it before. For
example, revisiting the first example of the inversion documentation:

.. rocqtop:: in reset extra-stdlib

   Require Import Stdlib.Logic.JMeq.

   Inductive Le : nat -> nat -> Set :=
        | LeO : forall n:nat, Le 0 n
        | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

   Parameter P : nat -> nat -> Prop.

   Goal forall n m:nat, Le (S n) m -> P n m.

   intros n m H.

.. rocqtop:: all extra-stdlib

   generalize_eqs H.

The index ``S n`` gets abstracted by a variable here, but a corresponding
equality is added under the abstract instance so that no information
is actually lost. The goal is now almost amenable to do induction or
case analysis. One should indeed first move ``n`` into the goal to
strengthen it before doing induction, or ``n`` will be fixed in the
inductive hypotheses (this does not matter for case analysis). As a
rule of thumb, all the variables that appear inside constructors in
the indices of the hypothesis should be generalized. This is exactly
what the ``generalize_eqs_vars`` variant does:

.. rocqtop:: all abort extra-stdlib

   generalize_eqs_vars H.
   induction H.

As the hypothesis itself did not appear in the goal, we did not need
to use an heterogeneous equality to relate the new hypothesis to the
old one (which just disappeared here). However, the tactic works just
as well in this case, e.g.:

.. rocqtop:: none extra-stdlib

   Require Import Stdlib.Program.Equality.

.. rocqtop:: in extra-stdlib

   Parameter Q : forall (n m : nat), Le n m -> Prop.
   Goal forall n m (p : Le (S n) m), Q (S n) m p.

.. rocqtop:: all extra-stdlib

   intros n m p.
   generalize_eqs_vars p.

One drawback of this approach is that in the branches one will have to
substitute the equalities back into the instance to get the right
assumptions. Sometimes injection of constructors will also be needed
to recover the needed equalities. Also, some subgoals should be
directly solved because of inconsistent contexts arising from the
constraints on indexes. The nice thing is that we can make a tactic
based on discriminate, injection and variants of substitution to
automatically do such simplifications (which may involve the axiom K).
This is what the ``simplify_dep_elim`` tactic from ``Stdlib.Program.Equality``
does. For example, we might simplify the previous goals considerably:

.. rocqtop:: all abort extra-stdlib

   induction p ; simplify_dep_elim.

The higher-order tactic ``do_depind`` defined in ``Stdlib.Program.Equality``
takes a tactic and combines the building blocks we have seen with it:
generalizing by equalities calling the given tactic with the
generalized induction hypothesis as argument and cleaning the subgoals
with respect to equalities. Its most important instantiations
are :tacn:`dependent induction` and :tacn:`dependent destruction` that do induction or
simply case analysis on the generalized hypothesis. For example we can
redo what we've done manually with dependent destruction:

.. rocqtop:: in extra-stdlib

   Lemma ex : forall n m:nat, Le (S n) m -> P n m.

.. rocqtop:: in extra-stdlib

   intros n m H.

.. rocqtop:: all abort extra-stdlib

   dependent destruction H.

This gives essentially the same result as inversion. Now if the
destructed hypothesis actually appeared in the goal, the tactic would
still be able to invert it, contrary to dependent inversion. Consider
the following example on vectors:

.. rocqtop:: in extra-stdlib

   Set Implicit Arguments.

.. rocqtop:: in extra-stdlib

   Parameter A : Set.

.. rocqtop:: in extra-stdlib

   Inductive vector : nat -> Type :=
            | vnil : vector 0
            | vcons : A -> forall n, vector n -> vector (S n).

.. rocqtop:: in extra-stdlib

   Goal forall n, forall v : vector (S n),
            exists v' : vector n, exists a : A, v = vcons a v'.

.. rocqtop:: in extra-stdlib

   intros n v.

.. rocqtop:: all extra-stdlib

   dependent destruction v.

In this case, the ``v`` variable can be replaced in the goal by the
generalized hypothesis only when it has a type of the form ``vector (S n)``,
that is only in the second case of the destruct. The first one is
dismissed because ``S n <> 0``.


A larger example
~~~~~~~~~~~~~~~~

Let's see how the technique works with induction on inductive
predicates on a real example. We will develop an example application
to the theory of simply-typed lambda-calculus formalized in a
dependently-typed style:

.. rocqtop:: in reset

   Inductive type : Type :=
            | base : type
            | arrow : type -> type -> type.

.. rocqtop:: in

   Notation " t --> t' " := (arrow t t') (at level 20, t' at next level).

.. rocqtop:: in

   Inductive ctx : Type :=
            | empty : ctx
            | snoc : ctx -> type -> ctx.

.. rocqtop:: in

   Notation " G , tau " := (snoc G tau) (at level 20, tau at next level).

.. rocqtop:: in

   Fixpoint conc (G D : ctx) : ctx :=
            match D with
            | empty => G
            | snoc D' x => snoc (conc G D') x
            end.

.. rocqtop:: in

   Notation " G ; D " := (conc G D) (at level 20).

.. rocqtop:: in

   Inductive term : ctx -> type -> Type :=
            | ax : forall G tau, term (G, tau) tau
            | weak : forall G tau,
                       term G tau -> forall tau', term (G, tau') tau
            | abs : forall G tau tau',
                      term (G , tau) tau' -> term G (tau --> tau')
            | app : forall G tau tau',
                      term G (tau --> tau') -> term G tau -> term G tau'.

We have defined types and contexts which are snoc-lists of types. We
also have a ``conc`` operation that concatenates two contexts. The ``term``
datatype represents in fact the possible typing derivations of the
calculus, which are isomorphic to the well-typed terms, hence the
name. A term is either an application of:


+ the axiom rule to type a reference to the first variable in a
  context
+ the weakening rule to type an object in a larger context
+ the abstraction or lambda rule to type a function
+ the application to type an application of a function to an argument


Once we have this datatype we want to do proofs on it, like weakening:

.. rocqtop:: in abort

   Lemma weakening : forall G D tau, term (G ; D) tau ->
                     forall tau', term (G , tau' ; D) tau.

The problem here is that we can't just use induction on the typing
derivation because it will forget about the ``G ; D`` constraint appearing
in the instance. A solution would be to rewrite the goal as:

.. rocqtop:: in abort

   Lemma weakening' : forall G' tau, term G' tau ->
                      forall G D, (G ; D) = G' ->
                      forall tau', term (G, tau' ; D) tau.

With this proper separation of the index from the instance and the
right induction loading (putting ``G`` and ``D`` after the inducted-on
hypothesis), the proof will go through, but it is a very tedious
process. One is also forced to make a wrapper lemma to get back the
more natural statement. The :tacn:`dependent induction` tactic alleviates this
trouble by doing all of this plumbing of generalizing and substituting
back automatically. Indeed we can simply write:

.. rocqtop:: in extra-stdlib

   Require Import Stdlib.Program.Tactics.
   Require Import Stdlib.Program.Equality.

.. rocqtop:: in extra-stdlib

   Lemma weakening : forall G D tau, term (G ; D) tau ->
                     forall tau', term (G , tau' ; D) tau.

.. rocqtop:: in extra-stdlib

   Proof with simpl in * ; simpl_depind ; auto.

.. rocqtop:: in extra-stdlib

   intros G D tau H. dependent induction H generalizing G D ; intros.

This call to :tacn:`dependent induction` has an additional arguments which is
a list of variables appearing in the instance that should be
generalized in the goal, so that they can vary in the induction
hypotheses. By default, all variables appearing inside constructors
(except in a parameter position) of the instantiated hypothesis will
be generalized automatically but one can always give the list
explicitly.

.. rocqtop:: all extra-stdlib

   Show.

The ``simpl_depind`` tactic includes an automatic tactic that tries to
simplify equalities appearing at the beginning of induction
hypotheses, generally using trivial applications of ``reflexivity``. In
cases where the equality is not between constructor forms though, one
must help the automation by giving some arguments, using the
``specialize`` tactic for example.

.. rocqtop:: in extra-stdlib

   destruct D... apply weak; apply ax. apply ax.

.. rocqtop:: in extra-stdlib

   destruct D...

.. rocqtop:: all extra-stdlib

   Show.

.. rocqtop:: all extra-stdlib

   specialize (IHterm G0 empty eq_refl).

Once the induction hypothesis has been narrowed to the right equality,
it can be used directly.

.. rocqtop:: all extra-stdlib

   apply weak, IHterm.

Now concluding this subgoal is easy.

.. rocqtop:: in extra-stdlib

   constructor; apply IHterm; reflexivity.
