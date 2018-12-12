.. _tactics:

Tactics
========

A deduction rule is a link between some (unique) formula, that we call
the *conclusion* and (several) formulas that we call the *premises*. A
deduction rule can be read in two ways. The first one says: “if I know
this and this then I can deduce this”. For instance, if I have a proof
of A and a proof of B then I have a proof of A ∧ B. This is forward
reasoning from premises to conclusion. The other way says: “to prove
this I have to prove this and this”. For instance, to prove A ∧ B, I
have to prove A and I have to prove B. This is backward reasoning from
conclusion to premises. We say that the conclusion is the *goal* to
prove and premises are the *subgoals*. The tactics implement *backward
reasoning*. When applied to a goal, a tactic replaces this goal with
the subgoals it generates. We say that a tactic reduces a goal to its
subgoal(s).

Each (sub)goal is denoted with a number. The current goal is numbered
1. By default, a tactic is applied to the current goal, but one can
address a particular goal in the list by writing n:tactic which means
“apply tactic tactic to goal number n”. We can show the list of
subgoals by typing Show (see Section :ref:`requestinginformation`).

Since not every rule applies to a given statement, not every tactic can
be used to reduce a given goal. In other words, before applying a tactic
to a given goal, the system checks that some *preconditions* are
satisfied. If it is not the case, the tactic raises an error message.

Tactics are built from atomic tactics and tactic expressions (which
extends the folklore notion of tactical) to combine those atomic
tactics. This chapter is devoted to atomic tactics. The tactic
language will be described in Chapter :ref:`ltac`.

.. _invocation-of-tactics:

Invocation of tactics
-------------------------

A tactic is applied as an ordinary command. It may be preceded by a
goal selector (see Section :ref:`ltac-semantics`). If no selector is
specified, the default selector is used.

.. _tactic_invocation_grammar:

  .. productionlist:: `sentence`
     tactic_invocation : toplevel_selector : tactic.
                       : |tactic .

.. opt:: Default Goal Selector "@toplevel_selector"
   :name: Default Goal Selector

   This option controls the default selector, used when no selector is
   specified when applying a tactic. The initial value is 1, hence the
   tactics are, by default, applied to the first goal.

   Using value ``all`` will make it so that tactics are, by default,
   applied to every goal simultaneously. Then, to apply a tactic tac
   to the first goal only, you can write ``1:tac``.

   Using value ``!`` enforces that all tactics are used either on a
   single focused goal or with a local selector (’’strict focusing
   mode’’).

   Although more selectors are available, only ``all``, ``!`` or a
   single natural number are valid default goal selectors.

.. _bindingslist:

Bindings list
~~~~~~~~~~~~~~~~~~~

Tactics that take a term as argument may also support a bindings list,
so as to instantiate some parameters of the term by name or position.
The general form of a term equipped with a bindings list is ``term with
bindings_list`` where ``bindings_list`` may be of two different forms:

.. _bindings_list_grammar:

  .. productionlist:: `bindings_list`
     bindings_list : (ref := `term`) ... (ref := `term`)
                   : `term` ... `term`

+ In a bindings list of the form :n:`{* (ref:= term)}`, :n:`ref` is either an
  :n:`@ident` or a :n:`@num`. The references are determined according to the type of
  ``term``. If :n:`ref` is an identifier, this identifier has to be bound in the
  type of ``term`` and the binding provides the tactic with an instance for the
  parameter of this name. If :n:`ref` is some number ``n``, this number denotes
  the ``n``-th non dependent premise of the ``term``, as determined by the type
  of ``term``.

  .. exn:: No such binder.
     :undocumented:

+ A bindings list can also be a simple list of terms :n:`{* term}`.
  In that case the references to which these terms correspond are
  determined by the tactic. In case of :tacn:`induction`, :tacn:`destruct`, :tacn:`elim`
  and :tacn:`case`, the terms have to
  provide instances for all the dependent products in the type of term while in
  the case of :tacn:`apply`, or of :tacn:`constructor` and its variants, only instances
  for the dependent products that are not bound in the conclusion of the type
  are required.

  .. exn:: Not the right number of missing arguments.
     :undocumented:

.. _occurrencessets:

Occurrence sets and occurrence clauses
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An occurrence clause is a modifier to some tactics that obeys the
following syntax:

  .. productionlist:: `sentence`
     occurrence_clause : in `goal_occurrences`
     goal_occurrences : [`ident` [`at_occurrences`], ... , ident [`at_occurrences`] [|- [* [`at_occurrences`]]]]
                      :| * |- [* [`at_occurrences`]]
                      :| *
     at_occurrences : at `occurrences`
     occurrences     : [-] `num` ... `num`

The role of an occurrence clause is to select a set of occurrences of a term
in a goal. In the first case, the :n:`@ident {? at {* num}}` parts indicate
that occurrences have to be selected in the hypotheses named :token:`ident`.
If no numbers are given for hypothesis :token:`ident`, then all the
occurrences of :token:`term` in the hypothesis are selected. If numbers are
given, they refer to occurrences of :token:`term` when the term is printed
using option :flag:`Printing All`, counting from left to right. In particular,
occurrences of :token:`term` in implicit arguments
(see :ref:`ImplicitArguments`) or coercions (see :ref:`Coercions`) are
counted.

If a minus sign is given between ``at`` and the list of occurrences, it
negates the condition so that the clause denotes all the occurrences
except the ones explicitly mentioned after the minus sign.

As an exception to the left-to-right order, the occurrences in
the return subexpression of a match are considered *before* the
occurrences in the matched term.

In the second case, the ``*`` on the left of ``|-`` means that all occurrences
of term are selected in every hypothesis.

In the first and second case, if ``*`` is mentioned on the right of ``|-``, the
occurrences of the conclusion of the goal have to be selected. If some numbers
are given, then only the occurrences denoted by these numbers are selected. If
no numbers are given, all occurrences of :token:`term` in the goal are selected.

Finally, the last notation is an abbreviation for ``* |- *``. Note also
that ``|-`` is optional in the first case when no ``*`` is given.

Here are some tactics that understand occurrence clauses: :tacn:`set`,
:tacn:`remember`, :tacn:`induction`, :tacn:`destruct`.


.. seealso::

   :ref:`Managingthelocalcontext`, :ref:`caseanalysisandinduction`,
   :ref:`printing_constructions_full`.


.. _applyingtheorems:

Applying theorems
---------------------

.. tacn:: exact @term
   :name: exact

   This tactic applies to any goal. It gives directly the exact proof
   term of the goal. Let ``T`` be our goal, let ``p`` be a term of type ``U`` then
   ``exact p`` succeeds iff ``T`` and ``U`` are convertible (see
   :ref:`Conversion-rules`).

   .. exn:: Not an exact proof.
      :undocumented:

   .. tacv:: eexact @term.
      :name: eexact

      This tactic behaves like :tacn:`exact` but is able to handle terms and
      goals with existential variables.

.. tacn:: assumption
   :name: assumption

   This tactic looks in the local context for a hypothesis whose type is
   convertible to the goal. If it is the case, the subgoal is proved.
   Otherwise, it fails.

   .. exn:: No such assumption.
      :undocumented:

   .. tacv:: eassumption
      :name: eassumption

      This tactic behaves like :tacn:`assumption` but is able to handle
      goals with existential variables.

.. tacn:: refine @term
   :name: refine

   This tactic applies to any goal. It behaves like :tacn:`exact` with a big
   difference: the user can leave some holes (denoted by ``_``
   or :n:`(_ : @type)`) in the term. :tacn:`refine` will generate as many
   subgoals as there are holes in the term. The type of holes must be either
   synthesized by the system or declared by an explicit cast
   like ``(_ : nat -> Prop)``. Any subgoal that
   occurs in other subgoals is automatically shelved, as if calling
   :tacn:`shelve_unifiable`. This low-level tactic can be
   useful to advanced users.

   .. example::

      .. coqtop:: reset all

         Inductive Option : Set :=
         | Fail : Option
         | Ok : bool -> Option.

         Definition get : forall x:Option, x <> Fail -> bool.
           refine
             (fun x:Option =>
               match x return x <> Fail -> bool with
               | Fail => _
               | Ok b => fun _ => b
               end).
           intros; absurd (Fail = Fail); trivial.
         Defined.

   .. exn:: Invalid argument.

      The tactic :tacn:`refine` does not know what to do with the term you gave.

   .. exn:: Refine passed ill-formed term.

      The term you gave is not a valid proof (not easy to debug in general). This
      message may also occur in higher-level tactics that call :tacn:`refine`
      internally.

   .. exn:: Cannot infer a term for this placeholder.
      :name: Cannot infer a term for this placeholder. (refine)

      There is a hole in the term you gave whose type cannot be inferred. Put a
      cast around it.

   .. tacv:: simple refine @term
      :name: simple refine

      This tactic behaves like refine, but it does not shelve any subgoal. It does
      not perform any beta-reduction either.

   .. tacv:: notypeclasses refine @term
      :name: notypeclasses refine

      This tactic behaves like :tacn:`refine` except it performs type checking without
      resolution of typeclasses.

   .. tacv:: simple notypeclasses refine @term
      :name: simple notypeclasses refine

      This tactic behaves like :tacn:`simple refine` except it performs type checking
      without resolution of typeclasses.

.. tacn:: apply @term
   :name: apply

   This tactic applies to any goal. The argument term is a term well-formed in
   the local context. The tactic :tacn:`apply` tries to match the current goal
   against the conclusion of the type of :token:`term`. If it succeeds, then
   the tactic returns as many subgoals as the number of non-dependent premises
   of the type of term. If the conclusion of the type of :token:`term` does
   not match the goal *and* the conclusion is an inductive type isomorphic to
   a tuple type, then each component of the tuple is recursively matched to
   the goal in the left-to-right order.

   The tactic :tacn:`apply` relies on first-order unification with dependent
   types unless the conclusion of the type of :token:`term` is of the form
   :n:`P (t__1 ... t__n)` with ``P`` to be instantiated. In the latter case,
   the behavior depends on the form of the goal. If the goal is of the form
   :n:`(fun x => Q) u__1 ... u__n` and the :n:`t__i` and :n:`u__i` unify,
   then :g:`P` is taken to be :g:`(fun x => Q)`. Otherwise, :tacn:`apply`
   tries to define :g:`P` by abstracting over :g:`t_1 ... t__n` in the goal.
   See :tacn:`pattern` to transform the goal so that it
   gets the form :n:`(fun x => Q) u__1 ... u__n`.

   .. exn:: Unable to unify @term with @term.

      The :tacn:`apply` tactic failed to match the conclusion of :token:`term`
      and the current goal. You can help the :tacn:`apply` tactic by
      transforming your goal with the :tacn:`change` or :tacn:`pattern`
      tactics.

   .. exn:: Unable to find an instance for the variables {+ @ident}.

      This occurs when some instantiations of the premises of :token:`term` are not deducible
      from the unification. This is the case, for instance, when you want to apply a
      transitivity property. In this case, you have to use one of the variants below:

   .. tacv:: apply @term with {+ @term}

      Provides apply with explicit instantiations for all dependent premises of the
      type of term that do not occur in the conclusion and consequently cannot be
      found by unification. Notice that the collection :n:`{+ @term}` must be given
      according to the order of these dependent premises of the type of term.

      .. exn:: Not the right number of missing arguments.
         :undocumented:

   .. tacv:: apply @term with @bindings_list

      This also provides apply with values for instantiating premises. Here, variables
      are referred by names and non-dependent products by increasing numbers (see
      :ref:`bindings list <bindingslist>`).

   .. tacv:: apply {+, @term}

      This is a shortcut for :n:`apply @term__1; [.. | ... ; [ .. | apply @term__n] ... ]`,
      i.e. for the successive applications of :n:`@term`:sub:`i+1` on the last subgoal
      generated by :n:`apply @term__i` , starting from the application of :n:`@term__1`.

   .. tacv:: eapply @term
      :name: eapply

      The tactic :tacn:`eapply` behaves like :tacn:`apply` but it does not fail when no
      instantiations are deducible for some variables in the premises. Rather, it
      turns these variables into existential variables which are variables still to
      instantiate (see :ref:`Existential-Variables`). The instantiation is
      intended to be found later in the proof.

   .. tacv:: simple apply @term.

      This behaves like :tacn:`apply` but it reasons modulo conversion only on subterms
      that contain no variables to instantiate. For instance, the following example
      does not succeed because it would require the conversion of ``id ?foo`` and
      :g:`O`.

      .. example::

         .. coqtop:: all

            Definition id (x : nat) := x.
            Parameter H : forall y, id y = y.
            Goal O = O.
            Fail simple apply H.

      Because it reasons modulo a limited amount of conversion, :tacn:`simple apply` fails
      quicker than :tacn:`apply` and it is then well-suited for uses in user-defined
      tactics that backtrack often. Moreover, it does not traverse tuples as :tacn:`apply`
      does.

   .. tacv:: {? simple} apply {+, @term {? with @bindings_list}}
             {? simple} eapply {+, @term {? with @bindings_list}}
      :name: simple apply; simple eapply

      This summarizes the different syntaxes for :tacn:`apply` and :tacn:`eapply`.

   .. tacv:: lapply @term
      :name: lapply

      This tactic applies to any goal, say :g:`G`. The argument term has to be
      well-formed in the current context, its type being reducible to a non-dependent
      product :g:`A -> B` with :g:`B` possibly containing products. Then it generates
      two subgoals :g:`B->G` and :g:`A`. Applying ``lapply H`` (where :g:`H` has type
      :g:`A->B` and :g:`B` does not start with a product) does the same as giving the
      sequence ``cut B. 2:apply H.`` where ``cut`` is described below.

      .. warn:: When @term contains more than one non dependent product the tactic lapply only takes into account the first product.
         :undocumented:

.. example::

   Assume we have a transitive relation ``R`` on ``nat``:

   .. coqtop:: reset in

      Variable R : nat -> nat -> Prop.

      Hypothesis Rtrans : forall x y z:nat, R x y -> R y z -> R x z.

      Variables n m p : nat.

      Hypothesis Rnm : R n m.

      Hypothesis Rmp : R m p.

   Consider the goal ``(R n p)`` provable using the transitivity of ``R``:

   .. coqtop:: in

      Goal R n p.

   The direct application of ``Rtrans`` with ``apply`` fails because no value
   for ``y`` in ``Rtrans`` is found by ``apply``:

   .. coqtop:: all

      Fail apply Rtrans.

   A solution is to ``apply (Rtrans n m p)`` or ``(Rtrans n m)``.

   .. coqtop:: all undo

      apply (Rtrans n m p).

   Note that ``n`` can be inferred from the goal, so the following would work
   too.

   .. coqtop:: in undo

      apply (Rtrans _ m).

   More elegantly, ``apply Rtrans with (y:=m)`` allows only mentioning the
   unknown m:

   .. coqtop:: in undo

      apply Rtrans with (y := m).

   Another solution is to mention the proof of ``(R x y)`` in ``Rtrans``

   .. coqtop:: all undo

      apply Rtrans with (1 := Rnm).

   ... or the proof of ``(R y z)``.

   .. coqtop:: all undo

      apply Rtrans with (2 := Rmp).

   On the opposite, one can use ``eapply`` which postpones the problem of
   finding ``m``. Then one can apply the hypotheses ``Rnm`` and ``Rmp``. This
   instantiates the existential variable and completes the proof.

   .. coqtop:: all

      eapply Rtrans.

      apply Rnm.

      apply Rmp.

.. note::
   When the conclusion of the type of the term to ``apply`` is an inductive
   type isomorphic to a tuple type and ``apply`` looks recursively whether a
   component of the tuple matches the goal, it excludes components whose
   statement would result in applying an universal lemma of the form
   ``forall A, ... -> A``. Excluding this kind of lemma can be avoided by
   setting the following option:

.. flag:: Universal Lemma Under Conjunction

   This option, which preserves compatibility with versions of Coq prior to
   8.4 is also available for :n:`apply @term in @ident` (see :tacn:`apply ... in`).

.. tacn:: apply @term in @ident
   :name: apply ... in

   This tactic applies to any goal. The argument :token:`term` is a term
   well-formed in the local context and the argument :token:`ident` is an
   hypothesis of the context.
   The tactic :n:`apply @term in @ident` tries to match the conclusion of the
   type of :token:`ident` against a non-dependent premise of the type
   of :token:`term`, trying them from right to left. If it succeeds, the
   statement of hypothesis :token:`ident` is replaced by the conclusion of
   the type of :token:`term`. The tactic also returns as many subgoals as the
   number of other non-dependent premises in the type of :token:`term` and of
   the non-dependent premises of the type of :token:`ident`. If the conclusion
   of the type of :token:`term` does not match the goal *and* the conclusion
   is an inductive type isomorphic to a tuple type, then
   the tuple is (recursively) decomposed and the first component of the tuple
   of which a non-dependent premise matches the conclusion of the type of
   :token:`ident`. Tuples are decomposed in a width-first left-to-right order
   (for instance if the type of :g:`H1` is :g:`A <-> B` and the type of
   :g:`H2` is :g:`A` then :g:`apply H1 in H2` transforms the type of :g:`H2`
   into :g:`B`). The tactic :tacn:`apply` relies on first-order pattern matching
   with dependent types.

   .. exn:: Statement without assumptions.

      This happens if the type of :token:`term` has no non-dependent premise.

   .. exn:: Unable to apply.

      This happens if the conclusion of :token:`ident` does not match any of
      the non-dependent premises of the type of :token:`term`.

   .. tacv:: apply {+, @term} in @ident

      This applies each :token:`term` in sequence in :token:`ident`.

   .. tacv:: apply {+, @term with @bindings_list} in @ident

      This does the same but uses the bindings in each :n:`(@ident := @term)` to
      instantiate the parameters of the corresponding type of :token:`term`
      (see :ref:`bindings list <bindingslist>`).

   .. tacv:: eapply {+, @term {? with @bindings_list } } in @ident

      This works as :tacn:`apply ... in` but turns unresolved bindings into
      existential variables, if any, instead of failing.

   .. tacv:: apply {+, @term {? with @bindings_list } } in @ident as @intro_pattern
      :name: apply ... in ... as

      This works as :tacn:`apply ... in` then applies the :token:`intro_pattern`
      to the hypothesis :token:`ident`.

   .. tacv:: simple apply @term in @ident

      This behaves like :tacn:`apply ... in` but it reasons modulo conversion
      only on subterms that contain no variables to instantiate. For instance,
      if :g:`id := fun x:nat => x` and :g:`H: forall y, id y = y -> True` and
      :g:`H0 : O = O` then :g:`simple apply H in H0` does not succeed because it
      would require the conversion of :g:`id ?x` and :g:`O` where :g:`?x` is
      an existential variable to instantiate.
      Tactic :n:`simple apply @term in @ident` does not
      either traverse tuples as :n:`apply @term in @ident` does.

   .. tacv:: {? simple} apply {+, @term {? with @bindings_list}} in @ident {? as @intro_pattern}
             {? simple} eapply {+, @term {? with @bindings_list}} in @ident {? as @intro_pattern}

      This summarizes the different syntactic variants of :n:`apply @term in @ident`
      and :n:`eapply @term in @ident`.

.. tacn:: constructor @num
   :name: constructor

   This tactic applies to a goal such that its conclusion is an inductive
   type (say :g:`I`). The argument :token:`num` must be less or equal to the
   numbers of constructor(s) of :g:`I`. Let :n:`c__i` be the i-th
   constructor of :g:`I`, then :g:`constructor i` is equivalent to
   :n:`intros; apply c__i`.

   .. exn:: Not an inductive product.
      :undocumented:

   .. exn:: Not enough constructors.
      :undocumented:

   .. tacv:: constructor

      This tries :g:`constructor 1` then :g:`constructor 2`, ..., then
      :g:`constructor n` where ``n`` is the number of constructors of the head
      of the goal.

   .. tacv:: constructor @num with @bindings_list

      Let ``c`` be the i-th constructor of :g:`I`, then
      :n:`constructor i with @bindings_list` is equivalent to
      :n:`intros; apply c with @bindings_list`.

      .. warning::

         The terms in the :token:`bindings_list` are checked in the context
         where constructor is executed and not in the context where :tacn:`apply`
         is executed (the introductions are not taken into account).

   .. tacv:: split {? with @bindings_list }
      :name: split

      This applies only if :g:`I` has a single constructor. It is then
      equivalent to :n:`constructor 1 {? with @bindings_list }`. It is
      typically used in the case of a conjunction :math:`A \wedge B`.

      .. tacv:: exists @bindings_list
         :name: exists

         This applies only if :g:`I` has a single constructor. It is then equivalent
         to :n:`intros; constructor 1 with @bindings_list.` It is typically used in
         the case of an existential quantification :math:`\exists x, P(x).`

      .. tacv:: exists {+, @bindings_list }

         This iteratively applies :n:`exists @bindings_list`.

      .. exn:: Not an inductive goal with 1 constructor.
         :undocumented:

   .. tacv:: left {? with @bindings_list }
             right {? with @bindings_list }
      :name: left; right

      These tactics apply only if :g:`I` has two constructors, for
      instance in the case of a disjunction :math:`A \vee B`.
      Then, they are respectively equivalent to
      :n:`constructor 1 {? with @bindings_list }` and
      :n:`constructor 2 {? with @bindings_list }`.

      .. exn:: Not an inductive goal with 2 constructors.
         :undocumented:

   .. tacv:: econstructor
             eexists
             esplit
             eleft
             eright
      :name: econstructor; eexists; esplit; eleft; eright

      These tactics and their variants behave like :tacn:`constructor`,
      :tacn:`exists`, :tacn:`split`, :tacn:`left`, :tacn:`right` and their
      variants but they introduce existential variables instead of failing
      when the instantiation of a variable cannot be found
      (cf. :tacn:`eapply` and :tacn:`apply`).


.. _managingthelocalcontext:

Managing the local context
------------------------------

.. tacn:: intro
   :name: intro

   This tactic applies to a goal that is either a product or starts with a
   let-binder. If the goal is a product, the tactic implements the "Lam" rule
   given in :ref:`Typing-rules` [1]_. If the goal starts with a let-binder,
   then the tactic implements a mix of the "Let" and "Conv".

   If the current goal is a dependent product :g:`forall x:T, U`
   (resp :g:`let x:=t in U`) then :tacn:`intro` puts :g:`x:T` (resp :g:`x:=t`)
   in the local context. The new subgoal is :g:`U`.

   If the goal is a non-dependent product :math:`T \rightarrow U`, then it
   puts in the local context either :g:`Hn:T` (if :g:`T` is of type :g:`Set`
   or :g:`Prop`) or :g:`Xn:T` (if the type of :g:`T` is :g:`Type`).
   The optional index ``n`` is such that ``Hn`` or ``Xn`` is a fresh
   identifier. In both cases, the new subgoal is :g:`U`.

   If the goal is an existential variable, :tacn:`intro` forces the resolution
   of the existential variable into a dependent product :math:`\forall`\ :g:`x:?X, ?Y`,
   puts :g:`x:?X` in the local context and leaves :g:`?Y` as a new subgoal
   allowed to depend on :g:`x`.

   The tactic :tacn:`intro` applies the tactic :tacn:`hnf`
   until :tacn:`intro` can be applied or the goal is not head-reducible.

   .. exn:: No product even after head-reduction.
      :undocumented:

   .. tacv:: intro @ident

      This applies :tacn:`intro` but forces :token:`ident` to be the name of
      the introduced hypothesis.

      .. exn:: @ident is already used.
         :undocumented:

   .. note::

      If a name used by intro hides the base name of a global constant then
      the latter can still be referred to by a qualified name
      (see :ref:`Qualified-names`).

   .. tacv:: intros
      :name: intros

      This repeats :tacn:`intro` until it meets the head-constant. It never
      reduces head-constants and it never fails.

   .. tacv:: intros {+ @ident}.

      This is equivalent to the composed tactic :n:`intro @ident; ... ; intro @ident`.

   .. tacv:: intros until @ident

      This repeats intro until it meets a premise of the goal having the
      form :n:`(@ident : @type)` and discharges the variable
      named :token:`ident` of the current goal.

      .. exn:: No such hypothesis in current goal.
         :undocumented:

   .. tacv:: intros until @num

      This repeats :tacn:`intro` until the :token:`num`\-th non-dependent
      product.

      .. example::

         On the subgoal :g:`forall x y : nat, x = y -> y = x` the
         tactic :n:`intros until 1` is equivalent to :n:`intros x y H`,
         as :g:`x = y -> y = x` is the first non-dependent product.

         On the subgoal :g:`forall x y z : nat, x = y -> y = x` the
         tactic :n:`intros until 1` is equivalent to :n:`intros x y z`
         as the product on :g:`z` can be rewritten as a non-dependent
         product: :g:`forall x y : nat, nat -> x = y -> y = x`.

      .. exn:: No such hypothesis in current goal.

         This happens when :token:`num` is 0 or is greater than the number of
         non-dependent products of the goal.

   .. tacv:: intro {? @ident__1 } after @ident__2
             intro {? @ident__1 } before @ident__2
             intro {? @ident__1 } at top
             intro {? @ident__1 } at bottom

      These tactics apply :n:`intro {? @ident__1}` and move the freshly
      introduced hypothesis respectively after the hypothesis :n:`@ident__2`,
      before the hypothesis :n:`@ident__2`, at the top of the local context,
      or at the bottom of the local context. All hypotheses on which the new
      hypothesis depends are moved too so as to respect the order of
      dependencies between hypotheses. It is equivalent to :n:`intro {? @ident__1 }`
      followed by the appropriate call to :tacn:`move ... after ...`,
      :tacn:`move ... before ...`, :tacn:`move ... at top`,
      or :tacn:`move ... at bottom`.

      .. note::

         :n:`intro at bottom` is a synonym for :n:`intro` with no argument.

      .. exn:: No such hypothesis: @ident.
         :undocumented:

.. tacn:: intros @intro_pattern_list
   :name: intros ...

   This extension of the tactic :n:`intros` allows to apply tactics on the fly
   on the variables or hypotheses which have been introduced. An
   *introduction pattern list* :n:`@intro_pattern_list` is a list of
   introduction patterns possibly containing the filling introduction
   patterns `*` and `**`. An *introduction pattern* is either:

   + a *naming introduction pattern*, i.e. either one of:

     + the pattern :n:`?`

     + the pattern :n:`?ident`

     + an identifier

   + an *action introduction pattern* which itself classifies into:

     + a *disjunctive/conjunctive introduction pattern*, i.e. either one of

       + a disjunction of lists of patterns
         :n:`[@intro_pattern_list | ... | @intro_pattern_list]`

       + a conjunction of patterns: :n:`({+, p})`

       + a list of patterns
         :n:`({+& p})`
         for sequence of right-associative binary constructs

     + an *equality introduction pattern*, i.e. either one of:

       + a pattern for decomposing an equality: :n:`[= {+ p}]`
       + the rewriting orientations: :n:`->` or :n:`<-`

     + the on-the-fly application of lemmas: :n:`p{+ %term}` where :n:`p`
       itself is not a pattern for on-the-fly application of lemmas (note:
       syntax is in experimental stage)

   + the wildcard: :n:`_`


   Assuming a goal of type :g:`Q → P` (non-dependent product), or of type
   :g:`forall x:T, P` (dependent product), the behavior of
   :n:`intros p` is defined inductively over the structure of the introduction
   pattern :n:`p`:

   Introduction on :n:`?` performs the introduction, and lets Coq choose a fresh
   name for the variable;

   Introduction on :n:`?@ident` performs the introduction, and lets Coq choose a
   fresh name for the variable based on :n:`@ident`;

   Introduction on :n:`@ident` behaves as described in :tacn:`intro`

   Introduction over a disjunction of list of patterns
   :n:`[@intro_pattern_list | ... | @intro_pattern_list ]` expects the product
   to be over an inductive type whose number of constructors is `n` (or more
   generally over a type of conclusion an inductive type built from `n`
   constructors, e.g. :g:`C -> A\/B` with `n=2` since :g:`A\/B` has `2`
   constructors): it destructs the introduced hypothesis as :n:`destruct` (see
   :tacn:`destruct`) would and applies on each generated subgoal the
   corresponding tactic;

   The introduction patterns in :n:`@intro_pattern_list` are expected to consume
   no more than the number of arguments of the `i`-th constructor. If it
   consumes less, then Coq completes the pattern so that all the arguments of
   the constructors of the inductive type are introduced (for instance, the
   list of patterns :n:`[ | ] H` applied on goal :g:`forall x:nat, x=0 -> 0=x`
   behaves the same as the list of patterns :n:`[ | ? ] H`);

   Introduction over a conjunction of patterns :n:`({+, p})` expects
   the goal to be a product over an inductive type :g:`I` with a single
   constructor that itself has at least `n` arguments: It performs a case
   analysis over the hypothesis, as :n:`destruct` would, and applies the
   patterns :n:`{+ p}` to the arguments of the constructor of :g:`I` (observe
   that :n:`({+ p})` is an alternative notation for :n:`[{+ p}]`);

   Introduction via :n:`({+& p})` is a shortcut for introduction via
   :n:`(p,( ... ,( ..., p ) ... ))`; it expects the hypothesis to be a sequence of
   right-associative binary inductive constructors such as :g:`conj` or
   :g:`ex_intro`; for instance, a hypothesis with type
   :g:`A /\(exists x, B /\ C /\ D)` can be introduced via pattern
   :n:`(a & x & b & c & d)`;

   If the product is over an equality type, then a pattern of the form
   :n:`[= {+ p}]` applies either :tacn:`injection` or :tacn:`discriminate`
   instead of :tacn:`destruct`; if :tacn:`injection` is applicable, the patterns
   :n:`{+, p}` are used on the hypotheses generated by :tacn:`injection`; if the
   number of patterns is smaller than the number of hypotheses generated, the
   pattern :n:`?` is used to complete the list.

   Introduction over ``->`` (respectively over ``<-``)
   expects the hypothesis to be an equality and the right-hand-side
   (respectively the left-hand-side) is replaced by the left-hand-side
   (respectively the right-hand-side) in the conclusion of the goal;
   the hypothesis itself is erased; if the term to substitute is a variable, it
   is substituted also in the context of goal and the variable is removed too.

   Introduction over a pattern :n:`p{+ %term}` first applies :n:`{+ term}`
   on the hypothesis to be introduced (as in :n:`apply {+, term}`) prior to the
   application of the introduction pattern :n:`p`;

   Introduction on the wildcard depends on whether the product is dependent or not:
   in the non-dependent case, it erases the corresponding hypothesis (i.e. it
   behaves as an :tacn:`intro` followed by a :tacn:`clear`) while in the
   dependent case, it succeeds and erases the variable only if the wildcard is part
   of a more complex list of introduction patterns that also erases the hypotheses
   depending on this variable;

   Introduction over :n:`*` introduces all forthcoming quantified variables
   appearing in a row; introduction over :n:`**` introduces all forthcoming
   quantified variables or hypotheses until the goal is not any more a
   quantification or an implication.

   .. example::

      .. coqtop:: reset all

         Goal forall A B C:Prop, A \/ B /\ C -> (A -> C) -> C.
           intros * [a | (_,c)] f.

.. note::

   :n:`intros {+ p}` is not equivalent to :n:`intros p; ... ; intros p`
   for the following reason: If one of the :n:`p` is a wildcard pattern, it
   might succeed in the first case because the further hypotheses it
   depends on are eventually erased too while it might fail in the second
   case because of dependencies in hypotheses which are not yet
   introduced (and a fortiori not yet erased).

.. note::

   In :n:`intros @intro_pattern_list`, if the last introduction pattern
   is a disjunctive or conjunctive pattern
   :n:`[{+| @intro_pattern_list}]`, the completion of :n:`@intro_pattern_list`
   so that all the arguments of the i-th constructors of the corresponding
   inductive type are introduced can be controlled with the following option:

   .. flag:: Bracketing Last Introduction Pattern

      Force completion, if needed, when the last introduction pattern is a
      disjunctive or conjunctive pattern (on by default).

.. tacn:: clear @ident
   :name: clear

   This tactic erases the hypothesis named :n:`@ident` in the local context of
   the current goal. As a consequence, :n:`@ident` is no more displayed and no
   more usable in the proof development.

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: @ident is used in the conclusion.
      :undocumented:

   .. exn:: @ident is used in the hypothesis @ident.
      :undocumented:

   .. tacv:: clear {+ @ident}

      This is equivalent to :n:`clear @ident. ... clear @ident.`

   .. tacv:: clear - {+ @ident}

      This variant clears all the hypotheses except the ones depending in the
      hypotheses named :n:`{+ @ident}` and in the goal.

   .. tacv:: clear

      This variants clears all the hypotheses except the ones the goal depends on.

   .. tacv:: clear dependent @ident

      This clears the hypothesis :token:`ident` and all the hypotheses that
      depend on it.

   .. tacv:: clearbody {+ @ident}
      :name: clearbody

      This tactic expects :n:`{+ @ident}` to be local definitions and clears
      their respective bodies.
      In other words, it turns the given definitions into assumptions.

      .. exn:: @ident is not a local definition.
         :undocumented:

.. tacn:: revert {+ @ident}
   :name: revert

   This applies to any goal with variables :n:`{+ @ident}`. It moves the hypotheses
   (possibly defined) to the goal, if this respects dependencies. This tactic is
   the inverse of :tacn:`intro`.

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: @ident__1 is used in the hypothesis @ident__2.
      :undocumented:

   .. tacv:: revert dependent @ident
      :name: revert dependent

      This moves to the goal the hypothesis :token:`ident` and all the
      hypotheses that depend on it.

.. tacn:: move @ident__1 after @ident__2
   :name: move ... after ...

   This moves the hypothesis named :n:`@ident__1` in the local context after
   the hypothesis named :n:`@ident__2`, where “after” is in reference to the
   direction of the move. The proof term is not changed.

   If :n:`@ident__1` comes before :n:`@ident__2` in the order of dependencies,
   then all the hypotheses between :n:`@ident__1` and :n:`@ident__2` that
   (possibly indirectly) depend on :n:`@ident__1` are moved too, and all of
   them are thus moved after :n:`@ident__2` in the order of dependencies.

   If :n:`@ident__1` comes after :n:`@ident__2` in the order of dependencies,
   then all the hypotheses between :n:`@ident__1` and :n:`@ident__2` that
   (possibly indirectly) occur in the type of :n:`@ident__1` are moved too,
   and all of them are thus moved before :n:`@ident__2` in the order of
   dependencies.

   .. tacv:: move @ident__1 before @ident__2
      :name: move ... before ...

      This moves :n:`@ident__1` towards and just before the hypothesis
      named :n:`@ident__2`.  As for :tacn:`move ... after ...`, dependencies
      over :n:`@ident__1` (when :n:`@ident__1` comes before :n:`@ident__2` in
      the order of dependencies) or in the type of :n:`@ident__1`
      (when :n:`@ident__1` comes after :n:`@ident__2` in the order of
      dependencies) are moved too.

   .. tacv:: move @ident at top
      :name: move ... at top

      This moves :token:`ident` at the top of the local context (at the beginning
      of the context).

   .. tacv:: move @ident at bottom
      :name: move ... at bottom

      This moves :token:`ident` at the bottom of the local context (at the end of
      the context).

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: Cannot move @ident__1 after @ident__2: it occurs in the type of @ident__2.
      :undocumented:

   .. exn:: Cannot move @ident__1 after @ident__2: it depends on @ident__2.
      :undocumented:

   .. example::

      .. coqtop:: reset all

         Goal forall x :nat, x = 0 -> forall z y:nat, y=y-> 0=x.
           intros x H z y H0.
           move x after H0.
           Undo.
           move x before H0.
           Undo.
           move H0 after H.
           Undo.
           move H0 before H.

.. tacn:: rename @ident__1 into @ident__2
   :name: rename

   This renames hypothesis :n:`@ident__1` into :n:`@ident__2` in the current
   context. The name of the hypothesis in the proof-term, however, is left
   unchanged.

   .. tacv:: rename {+, @ident__i into @ident__j}

      This renames the variables :n:`@ident__i` into :n:`@ident__j` in parallel.
      In particular, the target identifiers may contain identifiers that exist in
      the source context, as long as the latter are also renamed by the same
      tactic.

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: @ident is already used.
      :undocumented:

.. tacn:: set (@ident := @term)
   :name: set

   This replaces :token:`term` by :token:`ident` in the conclusion of the
   current goal and adds the new definition :n:`@ident := @term` to the
   local context.

   If :token:`term` has holes (i.e. subexpressions of the form “`_`”), the
   tactic first checks that all subterms matching the pattern are compatible
   before doing the replacement using the leftmost subterm matching the
   pattern.

   .. exn:: The variable @ident is already defined.
      :undocumented:

   .. tacv:: set (@ident := @term) in @goal_occurrences

      This notation allows specifying which occurrences of :token:`term` have
      to be substituted in the context. The :n:`in @goal_occurrences` clause
      is an occurrence clause whose syntax and behavior are described in
      :ref:`goal occurrences <occurrencessets>`.

   .. tacv:: set (@ident @binders := @term) {? in @goal_occurrences }

      This is equivalent to :n:`set (@ident := fun @binders => @term) {? in @goal_occurrences }`.

   .. tacv:: set @term {? in @goal_occurrences }

      This behaves as :n:`set (@ident := @term) {? in @goal_occurrences }`
      but :token:`ident` is generated by Coq.

   .. tacv:: eset (@ident {? @binders } := @term) {? in @goal_occurrences }
             eset @term {? in @goal_occurrences }
      :name: eset; _

      While the different variants of :tacn:`set` expect that no existential
      variables are generated by the tactic, :tacn:`eset` removes this
      constraint. In practice, this is relevant only when :tacn:`eset` is
      used as a synonym of :tacn:`epose`, i.e. when the :token:`term` does
      not occur in the goal.

.. tacn:: remember @term as @ident__1 {? eqn:@ident__2 }
   :name: remember

   This behaves as :n:`set (@ident__1 := @term) in *`, using a logical
   (Leibniz’s) equality instead of a local definition.
   If :n:`@ident__2` is provided, it will be the name of the new equation.

   .. tacv:: remember @term as @ident__1 {? eqn:@ident__2 } in @goal_occurrences

      This is a more general form of :tacn:`remember` that remembers the
      occurrences of :token:`term` specified by an occurrence set.

   .. tacv:: eremember @term as @ident__1 {? eqn:@ident__2 } {? in @goal_occurrences }
      :name: eremember

      While the different variants of :tacn:`remember` expect that no
      existential variables are generated by the tactic, :tacn:`eremember`
      removes this constraint.

.. tacn:: pose (@ident := @term)
   :name: pose

   This adds the local definition :n:`@ident := @term` to the current context
   without performing any replacement in the goal or in the hypotheses. It is
   equivalent to :n:`set (@ident := @term) in |-`.

   .. tacv:: pose (@ident @binders := @term)

      This is equivalent to :n:`pose (@ident := fun @binders => @term)`.

   .. tacv:: pose @term

      This behaves as :n:`pose (@ident := @term)` but :token:`ident` is
      generated by Coq.

   .. tacv:: epose (@ident {? @binders} := @term)
             epose @term
      :name: epose; _

      While the different variants of :tacn:`pose` expect that no
      existential variables are generated by the tactic, :tacn:`epose`
      removes this constraint.

.. tacn:: decompose [{+ @qualid}] @term
   :name: decompose

   This tactic recursively decomposes a complex proposition in order to
   obtain atomic ones.

   .. example::

      .. coqtop:: reset all

         Goal forall A B C:Prop, A /\ B /\ C \/ B /\ C \/ C /\ A -> C.
           intros A B C H; decompose [and or] H.
           all: assumption.
         Qed.

   .. note::

      :tacn:`decompose` does not work on right-hand sides of implications or
      products.

   .. tacv:: decompose sum @term

      This decomposes sum types (like :g:`or`).

   .. tacv:: decompose record @term

      This decomposes record types (inductive types with one constructor,
      like :g:`and` and :g:`exists` and those defined with the :cmd:`Record`
      command.


.. _controllingtheproofflow:

Controlling the proof flow
------------------------------

.. tacn:: assert (@ident : @type)
   :name: assert

   This tactic applies to any goal. :n:`assert (H : U)` adds a new hypothesis
   of name :n:`H` asserting :g:`U` to the current goal and opens a new subgoal
   :g:`U` [2]_. The subgoal :g:`U` comes first in the list of subgoals remaining to
   prove.

   .. exn:: Not a proposition or a type.

      Arises when the argument :token:`type` is neither of type :g:`Prop`,
      :g:`Set` nor :g:`Type`.

   .. tacv:: assert @type

      This behaves as :n:`assert (@ident : @type)` but :n:`@ident` is
      generated by Coq.

   .. tacv:: assert @type by @tactic

      This tactic behaves like :tacn:`assert` but applies tactic to solve the
      subgoals generated by assert.

      .. exn:: Proof is not complete.
         :name: Proof is not complete. (assert)
         :undocumented:

   .. tacv:: assert @type as @intro_pattern

      If :n:`intro_pattern` is a naming introduction pattern (see :tacn:`intro`),
      the hypothesis is named after this introduction pattern (in particular, if
      :n:`intro_pattern` is :n:`@ident`, the tactic behaves like
      :n:`assert (@ident : @type)`). If :n:`intro_pattern` is an action
      introduction pattern, the tactic behaves like :n:`assert @type` followed by
      the action done by this introduction pattern.

   .. tacv:: assert @type as @intro_pattern by @tactic

      This combines the two previous variants of :tacn:`assert`.

   .. tacv:: assert (@ident := @term)

      This behaves as :n:`assert (@ident : @type) by exact @term` where
      :token:`type` is the type of :token:`term`. This is equivalent to using
      :tacn:`pose proof`. If the head of term is :token:`ident`, the tactic
      behaves as :tacn:`specialize`.

      .. exn:: Variable @ident is already declared.
         :undocumented:

.. tacv:: eassert @type as @intro_pattern by @tactic
   :name: eassert

   While the different variants of :tacn:`assert` expect that no existential
   variables are generated by the tactic, :tacn:`eassert` removes this constraint.
   This allows not to specify the asserted statement completeley before starting
   to prove it.

.. tacv:: pose proof @term {? as @intro_pattern}
   :name: pose proof

   This tactic behaves like :n:`assert @type {? as @intro_pattern} by exact @term`
   where :token:`type` is the type of :token:`term`. In particular,
   :n:`pose proof @term as @ident` behaves as :n:`assert (@ident := @term)`
   and :n:`pose proof @term as @intro_pattern` is the same as applying the
   :token:`intro_pattern` to :token:`term`.

.. tacv:: epose proof @term {? as @intro_pattern}
   :name: epose proof

   While :tacn:`pose proof` expects that no existential variables are generated by
   the tactic, :tacn:`epose proof` removes this constraint.

.. tacv:: enough (@ident : @type)
   :name: enough

   This adds a new hypothesis of name :token:`ident` asserting :token:`type` to the
   goal the tactic :tacn:`enough` is applied to. A new subgoal stating :token:`type` is
   inserted after the initial goal rather than before it as :tacn:`assert` would do.

.. tacv:: enough @type

   This behaves like :n:`enough (@ident : @type)` with the name :token:`ident` of
   the hypothesis generated by Coq.

.. tacv:: enough @type as @intro_pattern

   This behaves like :n:`enough @type` using :token:`intro_pattern` to name or
   destruct the new hypothesis.

.. tacv:: enough (@ident : @type) by @tactic
          enough @type {? as @intro_pattern } by @tactic

   This behaves as above but with :token:`tactic` expected to solve the initial goal
   after the extra assumption :token:`type` is added and possibly destructed. If the
   :n:`as @intro_pattern` clause generates more than one subgoal, :token:`tactic` is
   applied to all of them.

.. tacv:: eenough @type {? as @intro_pattern } {? by @tactic }
          eenough (@ident : @type) {? by @tactic }
   :name: eenough; _

   While the different variants of :tacn:`enough` expect that no existential
   variables are generated by the tactic, :tacn:`eenough` removes this constraint.

.. tacv:: cut @type
   :name: cut

   This tactic applies to any goal. It implements the non-dependent case of
   the “App” rule given in :ref:`typing-rules`. (This is Modus Ponens inference
   rule.) :n:`cut U` transforms the current goal :g:`T` into the two following
   subgoals: :g:`U -> T` and :g:`U`. The subgoal :g:`U -> T` comes first in the
   list of remaining subgoal to prove.

.. tacv:: specialize (@ident {* @term}) {? as @intro_pattern}
          specialize @ident with @bindings_list {? as @intro_pattern}
   :name: specialize; _

   This tactic works on local hypothesis :n:`@ident`. The
   premises of this hypothesis (either universal quantifications or
   non-dependent implications) are instantiated by concrete terms coming either
   from arguments :n:`{* @term}` or from a :ref:`bindings list <bindingslist>`.
   In the first form the application to :n:`{* @term}`  can be partial. The
   first form is equivalent to :n:`assert (@ident := @ident {* @term})`. In the
   second form, instantiation elements can also be partial. In this case the
   uninstantiated arguments are inferred by unification if possible or left
   quantified in the hypothesis otherwise. With the :n:`as` clause, the local
   hypothesis :n:`@ident` is left unchanged and instead, the modified hypothesis
   is introduced as specified by the :token:`intro_pattern`. The name :n:`@ident`
   can also refer to a global lemma or hypothesis. In this case, for
   compatibility reasons, the behavior of :tacn:`specialize` is close to that of
   :tacn:`generalize`: the instantiated statement becomes an additional premise of
   the goal. The ``as`` clause is especially useful in this case to immediately
   introduce the instantiated statement as a local hypothesis.

   .. exn:: @ident is used in hypothesis @ident.
      :undocumented:

   .. exn:: @ident is used in conclusion.
      :undocumented:

.. tacn:: generalize @term
   :name: generalize

   This tactic applies to any goal. It generalizes the conclusion with
   respect to some term.

.. example::

   .. coqtop:: reset none

      Goal forall x y:nat, 0 <= x + y + y.
      Proof. intros *.

   .. coqtop:: all

      Show.
      generalize (x + y + y).

If the goal is :g:`G` and :g:`t` is a subterm of type :g:`T` in the goal,
then :n:`generalize t` replaces the goal by :g:`forall (x:T), G′` where :g:`G′`
is obtained from :g:`G` by replacing all occurrences of :g:`t` by :g:`x`. The
name of the variable (here :g:`n`) is chosen based on :g:`T`.

.. tacv:: generalize {+ @term}

   This is equivalent to :n:`generalize @term; ... ; generalize @term`.
   Note that the sequence of term :sub:`i` 's are processed from n to 1.

.. tacv:: generalize @term at {+ @num}

   This is equivalent to :n:`generalize @term` but it generalizes only over the
   specified occurrences of :n:`@term` (counting from left to right on the
   expression printed using option :flag:`Printing All`).

.. tacv:: generalize @term as @ident

   This is equivalent to :n:`generalize @term` but it uses :n:`@ident` to name
   the generalized hypothesis.

.. tacv:: generalize {+, @term at {+ @num} as @ident}

   This is the most general form of :n:`generalize` that combines the previous
   behaviors.

.. tacv:: generalize dependent @term

   This generalizes term but also *all* hypotheses that depend on :n:`@term`. It
   clears the generalized hypotheses.

.. tacn:: evar (@ident : @term)
   :name: evar

   The :n:`evar` tactic creates a new local definition named :n:`@ident` with type
   :n:`@term` in the context. The body of this binding is a fresh existential
   variable.

.. tacn:: instantiate (@ident := @term )
   :name: instantiate

   The instantiate tactic refines (see :tacn:`refine`) an existential variable
   :n:`@ident` with the term :n:`@term`. It is equivalent to only [ident]:
   :n:`refine @term` (preferred alternative).

   .. note:: To be able to refer to an existential variable by name, the user
             must have given the name explicitly (see :ref:`Existential-Variables`).

   .. note:: When you are referring to hypotheses which you did not name
             explicitly, be aware that Coq may make a different decision on how to
             name the variable in the current goal and in the context of the
             existential variable. This can lead to surprising behaviors.

.. tacv:: instantiate (@num := @term)

   This variant allows to refer to an existential variable which was not named
   by the user. The :n:`@num` argument is the position of the existential variable
   from right to left in the goal. Because this variant is not robust to slight
   changes in the goal, its use is strongly discouraged.

.. tacv:: instantiate ( @num := @term ) in @ident
          instantiate ( @num := @term ) in ( Value of @ident )
          instantiate ( @num := @term ) in ( Type of @ident )

   These allow to refer respectively to existential variables occurring in a
   hypothesis or in the body or the type of a local definition.

.. tacv:: instantiate

   Without argument, the instantiate tactic tries to solve as many existential
   variables as possible, using information gathered from other tactics in the
   same tactical. This is automatically done after each complete tactic (i.e.
   after a dot in proof mode), but not, for example, between each tactic when
   they are sequenced by semicolons.

.. tacn:: admit
   :name: admit

   This tactic allows temporarily skipping a subgoal so as to
   progress further in the rest of the proof. A proof containing admitted
   goals cannot be closed with :cmd:`Qed` but only with :cmd:`Admitted`.

.. tacv:: give_up

   Synonym of :tacn:`admit`.

.. tacn:: absurd @term
   :name: absurd

   This tactic applies to any goal. The argument term is any proposition
   :g:`P` of type :g:`Prop`. This tactic applies False elimination, that is it
   deduces the current goal from False, and generates as subgoals :g:`∼P` and
   :g:`P`. It is very useful in proofs by cases, where some cases are
   impossible. In most cases, :g:`P` or :g:`∼P` is one of the hypotheses of the
   local context.

.. tacn:: contradiction
   :name: contradiction

   This tactic applies to any goal. The contradiction tactic attempts to
   find in the current context (after all intros) a hypothesis that is
   equivalent to an empty inductive type (e.g. :g:`False`), to the negation of
   a singleton inductive type (e.g. :g:`True` or :g:`x=x`), or two contradictory
   hypotheses.

   .. exn:: No such assumption.
      :undocumented:

.. tacv:: contradiction @ident

   The proof of False is searched in the hypothesis named :n:`@ident`.

.. tacn:: contradict @ident
   :name: contradict

   This tactic allows manipulating negated hypothesis and goals. The name
   :n:`@ident` should correspond to a hypothesis. With :n:`contradict H`, the
   current goal and context is transformed in the following way:

   + H:¬A ⊢ B becomes ⊢ A
   + H:¬A ⊢ ¬B becomes H: B ⊢ A
   + H: A ⊢ B becomes ⊢ ¬A
   + H: A ⊢ ¬B becomes H: B ⊢ ¬A

.. tacn:: exfalso
   :name: exfalso

   This tactic implements the “ex falso quodlibet” logical principle: an
   elimination of False is performed on the current goal, and the user is
   then required to prove that False is indeed provable in the current
   context. This tactic is a macro for :n:`elimtype False`.

.. _CaseAnalysisAndInduction:

Case analysis and induction
-------------------------------

The tactics presented in this section implement induction or case
analysis on inductive or co-inductive objects (see :ref:`inductive-definitions`).

.. tacn:: destruct @term
   :name: destruct

   This tactic applies to any goal. The argument :token:`term` must be of
   inductive or co-inductive type and the tactic generates subgoals, one
   for each possible form of :token:`term`, i.e. one for each constructor of the
   inductive or co-inductive type. Unlike :tacn:`induction`, no induction
   hypothesis is generated by :tacn:`destruct`.

   .. tacv:: destruct @ident

      If :token:`ident` denotes a quantified variable of the conclusion
      of the goal, then :n:`destruct @ident` behaves
      as :n:`intros until @ident; destruct @ident`. If :token:`ident` is not
      anymore dependent in the goal after application of :tacn:`destruct`, it
      is erased (to avoid erasure, use parentheses, as in :n:`destruct (@ident)`).

      If :token:`ident` is a hypothesis of the context, and :token:`ident`
      is not anymore dependent in the goal after application
      of :tacn:`destruct`, it is erased (to avoid erasure, use parentheses, as
      in :n:`destruct (@ident)`).

   .. tacv:: destruct @num

      :n:`destruct @num` behaves as :n:`intros until @num`
      followed by destruct applied to the last introduced hypothesis.

     .. note::
        For destruction of a numeral, use syntax :n:`destruct (@num)` (not
        very interesting anyway).

   .. tacv:: destruct @pattern

      The argument of :tacn:`destruct` can also be a pattern of which holes are
      denoted by “_”. In this case, the tactic checks that all subterms
      matching the pattern in the conclusion and the hypotheses are compatible
      and performs case analysis using this subterm.

   .. tacv:: destruct {+, @term}

      This is a shortcut for :n:`destruct @term; ...; destruct @term`.

   .. tacv:: destruct @term as @disj_conj_intro_pattern

      This behaves as :n:`destruct @term` but uses the names
      in :token:`disj_conj_intro_pattern` to name the variables introduced in the
      context. The :token:`disj_conj_intro_pattern` must have the
      form :n:`[p11 ... p1n | ... | pm1 ... pmn ]` with ``m`` being the
      number of constructors of the type of :token:`term`. Each variable
      introduced by :tacn:`destruct` in the context of the ``i``-th goal
      gets its name from the list :n:`pi1 ... pin` in order. If there are not
      enough names, :tacn:`destruct` invents names for the remaining variables
      to introduce. More generally, the :n:`pij` can be any introduction
      pattern (see :tacn:`intros`). This provides a concise notation for
      chaining destruction of a hypothesis.

   .. tacv:: destruct @term eqn:@naming_intro_pattern
      :name: destruct ... eqn:

      This behaves as :n:`destruct @term` but adds an equation
      between :token:`term` and the value that it takes in each of the
      possible cases. The name of the equation is specified
      by :token:`naming_intro_pattern` (see :tacn:`intros`),
      in particular ``?`` can be used to let Coq generate a fresh name.

   .. tacv:: destruct @term with @bindings_list

      This behaves like :n:`destruct @term` providing explicit instances for
      the dependent premises of the type of :token:`term`.

   .. tacv:: edestruct @term
      :name: edestruct

      This tactic behaves like :n:`destruct @term` except that it does not
      fail if the instance of a dependent premises of the type
      of :token:`term` is not inferable. Instead, the unresolved instances
      are left as existential variables to be inferred later, in the same way
      as :tacn:`eapply` does.

   .. tacv:: destruct @term using @term {? with @bindings_list }

      This is synonym of :n:`induction @term using @term {? with @bindings_list }`.

   .. tacv:: destruct @term in @goal_occurrences

      This syntax is used for selecting which occurrences of :token:`term`
      the case analysis has to be done on. The :n:`in @goal_occurrences`
      clause is an occurrence clause whose syntax and behavior is described
      in :ref:`occurrences sets <occurrencessets>`.

   .. tacv:: destruct @term {? with @bindings_list } {? as @disj_conj_intro_pattern } {? eqn:@naming_intro_pattern } {? using @term {? with @bindings_list } } {? in @goal_occurrences }
             edestruct @term {? with @bindings_list } {? as @disj_conj_intro_pattern } {? eqn:@naming_intro_pattern } {? using @term {? with @bindings_list } } {? in @goal_occurrences }

      These are the general forms of :tacn:`destruct` and :tacn:`edestruct`.
      They combine the effects of the ``with``, ``as``, ``eqn:``, ``using``,
      and ``in`` clauses.

.. tacn:: case term
   :name: case

   The tactic :n:`case` is a more basic tactic to perform case analysis without
   recursion. It behaves as :n:`elim @term` but using a case-analysis
   elimination principle and not a recursive one.

.. tacv:: case @term with @bindings_list

   Analogous to :n:`elim @term with @bindings_list` above.

.. tacv:: ecase @term {? with @bindings_list }
   :name: ecase

   In case the type of :n:`@term` has dependent premises, or dependent premises
   whose values are not inferable from the :n:`with @bindings_list` clause,
   :n:`ecase` turns them into existential variables to be resolved later on.

.. tacv:: simple destruct @ident
   :name: simple destruct

   This tactic behaves as :n:`intros until @ident; case @ident` when :n:`@ident`
   is a quantified variable of the goal.

.. tacv:: simple destruct @num

   This tactic behaves as :n:`intros until @num; case @ident` where :n:`@ident`
   is the name given by :n:`intros until @num` to the :n:`@num` -th
   non-dependent premise of the goal.

.. tacv:: case_eq @term

   The tactic :n:`case_eq` is a variant of the :n:`case` tactic that allows to
   perform case analysis on a term without completely forgetting its original
   form. This is done by generating equalities between the original form of the
   term and the outcomes of the case analysis.

.. tacn:: induction @term
   :name: induction

   This tactic applies to any goal. The argument :n:`@term` must be of
   inductive type and the tactic :n:`induction` generates subgoals, one for
   each possible form of :n:`@term`, i.e. one for each constructor of the
   inductive type.

   If the argument is dependent in either the conclusion or some
   hypotheses of the goal, the argument is replaced by the appropriate
   constructor form in each of the resulting subgoals and induction
   hypotheses are added to the local context using names whose prefix
   is **IH**.

   There are particular cases:

   + If term is an identifier :n:`@ident` denoting a quantified variable of the
     conclusion of the goal, then inductionident behaves as :n:`intros until
     @ident; induction @ident`. If :n:`@ident` is not anymore dependent in the
     goal after application of :n:`induction`, it is erased (to avoid erasure,
     use parentheses, as in :n:`induction (@ident)`).
   + If :n:`@term` is a :n:`@num`, then :n:`induction @num` behaves as
     :n:`intros until @num` followed by :n:`induction` applied to the last
     introduced hypothesis.

     .. note::
        For simple induction on a numeral, use syntax induction (num)
        (not very interesting anyway).

   + In case term is a hypothesis :n:`@ident` of the context, and :n:`@ident`
     is not anymore dependent in the goal after application of :n:`induction`,
     it is erased (to avoid erasure, use parentheses, as in
     :n:`induction (@ident)`).
   + The argument :n:`@term` can also be a pattern of which holes are denoted
     by “_”. In this case, the tactic checks that all subterms matching the
     pattern in the conclusion and the hypotheses are compatible and
     performs induction using this subterm.

.. example::

   .. coqtop:: reset all

      Lemma induction_test : forall n:nat, n = n -> n <= n.
      intros n H.
      induction n.

.. exn:: Not an inductive product.
   :undocumented:

.. exn:: Unable to find an instance for the variables @ident ... @ident.

   Use in this case the variant :tacn:`elim ... with` below.

.. tacv:: induction @term as @disj_conj_intro_pattern

   This behaves as :tacn:`induction` but uses the names in
   :n:`@disj_conj_intro_pattern` to name the variables introduced in the
   context. The :n:`@disj_conj_intro_pattern` must typically be of the form
   :n:`[ p` :sub:`11` :n:`... p` :sub:`1n` :n:`| ... | p`:sub:`m1` :n:`... p`:sub:`mn` :n:`]`
   with :n:`m` being the number of constructors of the type of :n:`@term`. Each
   variable introduced by induction in the context of the i-th goal gets its
   name from the list :n:`p`:sub:`i1` :n:`... p`:sub:`in` in order. If there are
   not enough names, induction invents names for the remaining variables to
   introduce. More generally, the :n:`p`:sub:`ij` can be any
   disjunctive/conjunctive introduction pattern (see :tacn:`intros ...`). For
   instance, for an inductive type with  one constructor, the pattern notation
   :n:`(p`:sub:`1` :n:`, ... , p`:sub:`n` :n:`)` can be used instead of
   :n:`[ p`:sub:`1` :n:`... p`:sub:`n` :n:`]`.

.. tacv:: induction @term with @bindings_list

   This behaves like :tacn:`induction` providing explicit instances for the
   premises of the type of :n:`term` (see :ref:`bindings list <bindingslist>`).

.. tacv:: einduction @term
   :name: einduction

   This tactic behaves like :tacn:`induction` except that it does not fail if
   some dependent premise of the type of :n:`@term` is not inferable. Instead,
   the unresolved premises are posed as existential variables to be inferred
   later, in the same way as :tacn:`eapply` does.

.. tacv:: induction @term using @term
   :name: induction ... using ...

   This behaves as :tacn:`induction`  but using :n:`@term` as induction scheme.
   It does not expect the conclusion of the type of the first :n:`@term` to be
   inductive.

.. tacv:: induction @term using @term with @bindings_list

   This behaves as :tacn:`induction ... using ...` but also providing instances
   for the premises of the type of the second :n:`@term`.

.. tacv:: induction {+, @term} using @qualid

   This syntax is used for the case :n:`@qualid` denotes an induction principle
   with complex predicates as the induction principles generated by
   ``Function`` or ``Functional Scheme`` may be.

.. tacv:: induction @term in @goal_occurrences

   This syntax is used for selecting which occurrences of :n:`@term` the
   induction has to be carried on. The :n:`in @goal_occurrences` clause is an
   occurrence clause whose syntax and behavior is described in
   :ref:`occurrences sets <occurrencessets>`. If variables or hypotheses not
   mentioning :n:`@term` in their type are listed in :n:`@goal_occurrences`,
   those are generalized as well in the statement to prove.

   .. example::

      .. coqtop:: reset all

         Lemma comm x y : x + y = y + x.
         induction y in x |-   *.
         Show 2.

.. tacv:: induction @term with @bindings_list as @disj_conj_intro_pattern using @term with @bindings_list in @goal_occurrences
          einduction @term with @bindings_list as @disj_conj_intro_pattern using @term with @bindings_list in @goal_occurrences

   These are the most general forms of :tacn:`induction` and :tacn:`einduction`. It combines the
   effects of the with, as, using, and in clauses.

.. tacv:: elim @term
   :name: elim

   This is a more basic induction tactic. Again, the type of the argument
   :n:`@term` must be an inductive type. Then, according to the type of the
   goal, the tactic ``elim`` chooses the appropriate destructor and applies it
   as the tactic :tacn:`apply` would do. For instance, if the proof context
   contains :g:`n:nat` and the current goal is :g:`T` of type :g:`Prop`, then
   :n:`elim n` is equivalent to :n:`apply nat_ind with (n:=n)`. The tactic
   ``elim`` does not modify the context of the goal, neither introduces the
   induction loading into the context of hypotheses. More generally,
   :n:`elim @term` also works when the type of :n:`@term` is a statement
   with premises and whose conclusion is inductive. In that case the tactic
   performs induction on the conclusion of the type of :n:`@term` and leaves the
   non-dependent premises of the type as subgoals. In the case of dependent
   products, the tactic tries to find an instance for which the elimination
   lemma applies and fails otherwise.

.. tacv:: elim @term with @bindings_list
   :name: elim ... with

   Allows to give explicit instances to the premises of the type of :n:`@term`
   (see :ref:`bindings list <bindingslist>`).

.. tacv:: eelim @term
   :name: eelim

   In case the type of :n:`@term` has dependent premises, this turns them into
   existential variables to be resolved later on.

.. tacv:: elim @term using @term
          elim @term using @term with @bindings_list

   Allows the user to give explicitly an induction principle :n:`@term` that
   is not the standard one for the underlying inductive type of :n:`@term`. The
   :n:`@bindings_list` clause allows instantiating premises of the type of
   :n:`@term`.

.. tacv:: elim @term with @bindings_list using @term with @bindings_list
          eelim @term with @bindings_list using @term with @bindings_list

   These are the most general forms of :tacn:`elim` and :tacn:`eelim`. It combines the
   effects of the ``using`` clause and of the two uses of the ``with`` clause.

.. tacv:: elimtype @type
   :name: elimtype

   The argument :token:`type` must be inductively defined. :n:`elimtype I` is
   equivalent to :n:`cut I. intro Hn; elim Hn; clear Hn.` Therefore the
   hypothesis :g:`Hn` will not appear in the context(s) of the subgoal(s).
   Conversely, if :g:`t` is a :n:`@term` of (inductive) type :g:`I` that does
   not occur in the goal, then :n:`elim t` is equivalent to
   :n:`elimtype I; 2:exact t.`

.. tacv:: simple induction @ident
   :name: simple induction

   This tactic behaves as :n:`intros until @ident; elim @ident` when
   :n:`@ident` is a quantified variable of the goal.

.. tacv:: simple induction @num

   This tactic behaves as :n:`intros until @num; elim @ident` where :n:`@ident`
   is the name given by :n:`intros until @num` to the :n:`@num`-th non-dependent
   premise of the goal.

.. tacn:: double induction @ident @ident
   :name: double induction

   This tactic is deprecated and should be replaced by
   :n:`induction @ident; induction @ident` (or
   :n:`induction @ident ; destruct @ident` depending on the exact needs).

.. tacv:: double induction num1 num2

   This tactic is deprecated and should be replaced by
   :n:`induction num1; induction num3` where :n:`num3` is the result
   of :n:`num2 - num1`

.. tacn:: dependent induction @ident
   :name: dependent induction

   The *experimental* tactic dependent induction performs induction-
   inversion on an instantiated inductive predicate. One needs to first
   require the Coq.Program.Equality module to use this tactic. The tactic
   is based on the BasicElim tactic by Conor McBride
   :cite:`DBLP:conf/types/McBride00` and the work of Cristina Cornes around
   inversion :cite:`DBLP:conf/types/CornesT95`. From an instantiated
   inductive predicate and a goal, it generates an equivalent goal where
   the hypothesis has been generalized over its indexes which are then
   constrained by equalities to be the right instances. This permits to
   state lemmas without resorting to manually adding these equalities and
   still get enough information in the proofs.

.. example::

   .. coqtop:: reset all

      Lemma le_minus : forall n:nat, n < 1 -> n = 0.
      intros n H ; induction H.

   Here we did not get any information on the indexes to help fulfill
   this proof. The problem is that, when we use the ``induction`` tactic, we
   lose information on the hypothesis instance, notably that the second
   argument is 1 here. Dependent induction solves this problem by adding
   the corresponding equality to the context.

   .. coqtop:: reset all

      Require Import Coq.Program.Equality.
      Lemma le_minus : forall n:nat, n < 1 -> n = 0.
      intros n H ; dependent induction H.

   The subgoal is cleaned up as the tactic tries to automatically
   simplify the subgoals with respect to the generated equalities. In
   this enriched context, it becomes possible to solve this subgoal.

   .. coqtop:: all

      reflexivity.

   Now we are in a contradictory context and the proof can be solved.

   .. coqtop:: all

      inversion H.

   This technique works with any inductive predicate. In fact, the
   ``dependent induction`` tactic is just a wrapper around the ``induction``
   tactic. One can make its own variant by just writing a new tactic
   based on the definition found in ``Coq.Program.Equality``.

.. tacv:: dependent induction @ident generalizing {+ @ident}

   This performs dependent induction on the hypothesis :n:`@ident` but first
   generalizes the goal by the given variables so that they are universally
   quantified in the goal. This is generally what one wants to do with the
   variables that are inside some constructors in the induction hypothesis. The
   other ones need not be further generalized.

.. tacv:: dependent destruction @ident
   :name: dependent destruction

   This performs the generalization of the instance :n:`@ident` but uses
   ``destruct`` instead of induction on the generalized hypothesis. This gives
   results equivalent to ``inversion`` or ``dependent inversion`` if the
   hypothesis is dependent.

See also the larger example of :tacn:`dependent induction`
and an explanation of the underlying technique.

.. tacn:: function induction (@qualid {+ @term})
   :name: function induction

   The tactic functional induction performs case analysis and induction
   following the definition of a function. It makes use of a principle
   generated by ``Function`` (see :ref:`advanced-recursive-functions`) or
   ``Functional Scheme`` (see :ref:`functional-scheme`).
   Note that this tactic is only available after a ``Require Import FunInd``.

.. example::

   .. coqtop:: reset all

      Require Import FunInd.
      Functional Scheme minus_ind := Induction for minus Sort Prop.
      Check minus_ind.
      Lemma le_minus (n m:nat) : n - m <= n.
      functional induction (minus n m) using minus_ind; simpl; auto.
      Qed.

.. note::
   :n:`(@qualid {+ @term})` must be a correct full application
   of :n:`@qualid`. In particular, the rules for implicit arguments are the
   same as usual. For example use :n:`@qualid` if you want to write implicit
   arguments explicitly.

.. note::
   Parentheses around :n:`@qualid {+ @term}` are not mandatory and can be skipped.

.. note::
   :n:`functional induction (f x1 x2 x3)` is actually a wrapper for
   :n:`induction x1, x2, x3, (f x1 x2 x3) using @qualid` followed by a cleaning
   phase, where :n:`@qualid` is the induction principle registered for :g:`f`
   (by the ``Function`` (see :ref:`advanced-recursive-functions`) or
   ``Functional Scheme`` (see :ref:`functional-scheme`)
   command) corresponding to the sort of the goal. Therefore
   ``functional induction`` may fail if the induction scheme :n:`@qualid` is not
   defined. See also :ref:`advanced-recursive-functions` for the function
   terms accepted by ``Function``.

.. note::
   There is a difference between obtaining an induction scheme
   for a function by using :g:`Function` (see :ref:`advanced-recursive-functions`)
   and by using :g:`Functional Scheme` after a normal definition using
   :g:`Fixpoint` or :g:`Definition`. See :ref:`advanced-recursive-functions`
   for details.

.. seealso:: :ref:`advanced-recursive-functions`, :ref:`functional-scheme` and :tacn:`inversion`

.. exn:: Cannot find induction information on @qualid.
   :undocumented:

.. exn:: Not the right number of induction arguments.
   :undocumented:

.. tacv:: functional induction (@qualid {+ @term}) as @disj_conj_intro_pattern using @term with @bindings_list

   Similarly to :tacn:`induction` and :tacn:`elim`, this allows giving
   explicitly the name of the introduced variables, the induction principle, and
   the values of dependent premises of the elimination scheme, including
   *predicates* for mutual induction when :n:`@qualid` is part of a mutually
   recursive definition.

.. tacn:: discriminate @term
   :name: discriminate

   This tactic proves any goal from an assumption stating that two
   structurally different :n:`@terms` of an inductive set are equal. For
   example, from :g:`(S (S O))=(S O)` we can derive by absurdity any
   proposition.

   The argument :n:`@term` is assumed to be a proof of a statement of
   conclusion :n:`@term = @term` with the two terms being elements of an
   inductive set. To build the proof, the tactic traverses the normal forms
   [3]_ of the terms looking for a couple of subterms :g:`u` and :g:`w` (:g:`u`
   subterm of the normal form of :n:`@term` and :g:`w` subterm of the normal
   form of :n:`@term`), placed at the same positions and whose head symbols are
   two different constructors. If such a couple of subterms exists, then the
   proof of the current goal is completed, otherwise the tactic fails.

.. note::
   The syntax :n:`discriminate @ident` can be used to refer to a hypothesis
   quantified in the goal. In this case, the quantified hypothesis whose name is
   :n:`@ident` is first introduced in the local context using
   :n:`intros until @ident`.

.. exn:: No primitive equality found.
   :undocumented:

.. exn:: Not a discriminable equality.
   :undocumented:

.. tacv:: discriminate @num

   This does the same thing as :n:`intros until @num` followed by
   :n:`discriminate @ident` where :n:`@ident` is the identifier for the last
   introduced hypothesis.

.. tacv:: discriminate @term with @bindings_list

   This does the same thing as :n:`discriminate @term` but using the given
   bindings to instantiate parameters or hypotheses of :n:`@term`.

.. tacv:: ediscriminate @num
          ediscriminate @term {? with @bindings_list}
   :name: ediscriminate; _

   This works the same as :tacn:`discriminate` but if the type of :token:`term`, or the
   type of the hypothesis referred to by :token:`num`, has uninstantiated
   parameters, these parameters are left as existential variables.

.. tacv:: discriminate

   This behaves like :n:`discriminate @ident` if ident is the name of an
   hypothesis to which ``discriminate`` is applicable; if the current goal is of
   the form :n:`@term <> @term`, this behaves as
   :n:`intro @ident; discriminate @ident`.

   .. exn:: No discriminable equalities.
      :undocumented:

.. tacn:: injection @term
   :name: injection

   The injection tactic exploits the property that constructors of
   inductive types are injective, i.e. that if :g:`c` is a constructor of an
   inductive type and :g:`c t`:sub:`1` and :g:`c t`:sub:`2` are equal then
   :g:`t`:sub:`1` and :g:`t`:sub:`2` are equal too.

   If :n:`@term` is a proof of a statement of conclusion :n:`@term = @term`,
   then :tacn:`injection` applies the injectivity of constructors as deep as
   possible to derive the equality of all the subterms of :n:`@term` and
   :n:`@term` at positions where the terms start to differ. For example, from
   :g:`(S p, S n) = (q, S (S m))` we may derive :g:`S p = q` and
   :g:`n = S m`. For this tactic to work, the terms should be typed with an
   inductive type and they should be neither convertible, nor having a different
   head constructor. If these conditions are satisfied, the tactic derives the
   equality of all the subterms at positions where they differ and adds them as
   antecedents to the conclusion of the current goal.

   .. example::

      Consider the following goal:

      .. coqtop:: in

         Inductive list : Set :=
         | nil : list
         | cons : nat -> list -> list.
         Parameter P : list -> Prop.
         Goal forall l n, P nil -> cons n l = cons 0 nil -> P l.

      .. coqtop:: all

         intros.
         injection H0.

   Beware that injection yields an equality in a sigma type whenever the
   injected object has a dependent type :g:`P` with its two instances in
   different types :g:`(P t`:sub:`1` :g:`... t`:sub:`n` :g:`)` and
   :g:`(P u`:sub:`1` :g:`... u`:sub:`n` :sub:`)`. If :g:`t`:sub:`1` and
   :g:`u`:sub:`1` are the same and have for type an inductive type for which a decidable
   equality has been declared using the command :cmd:`Scheme Equality`
   (see :ref:`proofschemes-induction-principles`),
   the use of a sigma type is avoided.

   .. note::
      If some quantified hypothesis of the goal is named :n:`@ident`,
      then :n:`injection @ident` first introduces the hypothesis in the local
      context using :n:`intros until @ident`.

   .. exn:: Not a projectable equality but a discriminable one.
      :undocumented:

   .. exn:: Nothing to do, it is an equality between convertible terms.
      :undocumented:

   .. exn:: Not a primitive equality.
      :undocumented:

   .. exn:: Nothing to inject.
      :undocumented:

   .. tacv:: injection @num

      This does the same thing as :n:`intros until @num` followed by
      :n:`injection @ident` where :n:`@ident` is the identifier for the last
      introduced hypothesis.

   .. tacv:: injection @term with @bindings_list

      This does the same as :n:`injection @term` but using the given bindings to
      instantiate parameters or hypotheses of :n:`@term`.

   .. tacv:: einjection @num
             einjection @term {? with @bindings_list}
      :name: einjection; _

      This works the same as :n:`injection` but if the type of :n:`@term`, or the
      type of the hypothesis referred to by :n:`@num`, has uninstantiated
      parameters, these parameters are left as existential variables.

   .. tacv:: injection

      If the current goal is of the form :n:`@term <> @term` , this behaves as
      :n:`intro @ident; injection @ident`.

      .. exn:: goal does not satisfy the expected preconditions.
         :undocumented:

   .. tacv:: injection @term {? with @bindings_list} as {+ @intro_pattern}
             injection @num as {+ intro_pattern}
             injection as {+ intro_pattern}
             einjection @term {? with @bindings_list} as {+ intro_pattern}
             einjection @num as {+ intro_pattern}
             einjection as {+ intro_pattern}

      These variants apply :n:`intros {+ @intro_pattern}` after the call to
      :tacn:`injection` or :tacn:`einjection` so that all equalities generated are moved in
      the context of hypotheses. The number of :n:`@intro_pattern` must not exceed
      the number of equalities newly generated. If it is smaller, fresh
      names are automatically generated to adjust the list of :n:`@intro_pattern`
      to the number of new equalities. The original equality is erased if it
      corresponds to a hypothesis.

   .. flag:: Structural Injection

      This option ensure that :n:`injection @term` erases the original hypothesis
      and leaves the generated equalities in the context rather than putting them
      as antecedents of the current goal, as if giving :n:`injection @term as`
      (with an empty list of names). This option is off by default.

   .. flag:: Keep Proof Equalities

      By default, :tacn:`injection` only creates new equalities between :n:`@terms`
      whose type is in sort :g:`Type` or :g:`Set`, thus implementing a special
      behavior for objects that are proofs of a statement in :g:`Prop`. This option
      controls this behavior.

.. tacn:: inversion @ident
   :name: inversion

   Let the type of :n:`@ident` in the local context be :g:`(I t)`, where :g:`I`
   is a (co)inductive predicate. Then, ``inversion`` applied to :n:`@ident`
   derives for each possible constructor :g:`c i` of :g:`(I t)`, all the
   necessary conditions that should hold for the instance :g:`(I t)` to be
   proved by :g:`c i`.

.. note::
   If :n:`@ident` does not denote a hypothesis in the local context but
   refers to a hypothesis quantified in the goal, then the latter is
   first introduced in the local context using :n:`intros until @ident`.

.. note::
   As ``inversion`` proofs may be large in size, we recommend the
   user to stock the lemmas whenever the same instance needs to be
   inverted several times. See :ref:`derive-inversion`.

.. note::
   Part of the behavior of the ``inversion`` tactic is to generate
   equalities between expressions that appeared in the hypothesis that is
   being processed. By default, no equalities are generated if they
   relate two proofs (i.e. equalities between :n:`@terms` whose type is in sort
   :g:`Prop`). This behavior can be turned off by using the option
   :flag`Keep Proof Equalities`.

.. tacv:: inversion @num

   This does the same thing as :n:`intros until @num` then :n:`inversion @ident`
   where :n:`@ident` is the identifier for the last introduced hypothesis.

.. tacv:: inversion_clear @ident

   This behaves as :n:`inversion` and then erases :n:`@ident` from the context.

.. tacv:: inversion @ident as @intro_pattern

   This generally behaves as inversion but using names in :n:`@intro_pattern`
   for naming hypotheses. The :n:`@intro_pattern` must have the form
   :n:`[p`:sub:`11` :n:`... p`:sub:`1n` :n:`| ... | p`:sub:`m1` :n:`... p`:sub:`mn` :n:`]`
   with `m` being the number of constructors of the type of :n:`@ident`. Be
   careful that the list must be of length `m` even if ``inversion`` discards
   some cases (which is precisely one of its roles): for the discarded
   cases, just use an empty list (i.e. `n = 0`).The arguments of the i-th
   constructor and the equalities that ``inversion`` introduces in the
   context of the goal corresponding to the i-th constructor, if it
   exists, get their names from the list :n:`p`:sub:`i1` :n:`... p`:sub:`in` in
   order. If there are not enough names, ``inversion`` invents names for the
   remaining variables to introduce. In case an equation splits into several
   equations (because ``inversion`` applies ``injection`` on the equalities it
   generates), the corresponding name :n:`p`:sub:`ij` in the list must be
   replaced by a sublist of the form :n:`[p`:sub:`ij1` :n:`... p`:sub:`ijq` :n:`]`
   (or, equivalently, :n:`(p`:sub:`ij1` :n:`, ..., p`:sub:`ijq` :n:`)`) where
   `q` is the number of subequalities obtained from splitting the original
   equation. Here is an example. The ``inversion ... as`` variant of
   ``inversion`` generally behaves in a slightly more expectable way than
   ``inversion`` (no artificial duplication of some hypotheses referring to
   other hypotheses). To take benefit of these improvements, it is enough to use
   ``inversion ... as []``, letting the names being finally chosen by Coq.

   .. example::

      .. coqtop:: reset all

         Inductive contains0 : list nat -> Prop :=
         | in_hd : forall l, contains0 (0 :: l)
         | in_tl : forall l b, contains0 l -> contains0 (b :: l).
         Goal forall l:list nat, contains0 (1 :: l) -> contains0 l.
         intros l H; inversion H as [ | l' p Hl' [Heqp Heql'] ].

.. tacv:: inversion @num as @intro_pattern

   This allows naming the hypotheses introduced by :n:`inversion @num` in the
   context.

.. tacv:: inversion_clear @ident as @intro_pattern

   This allows naming the hypotheses introduced by ``inversion_clear`` in the
   context. Notice that hypothesis names can be provided as if ``inversion``
   were called, even though the ``inversion_clear`` will eventually erase the
   hypotheses.

.. tacv:: inversion @ident in {+ @ident}

   Let :n:`{+ @ident}` be identifiers in the local context. This tactic behaves as
   generalizing :n:`{+ @ident}`, and then performing ``inversion``.

.. tacv:: inversion @ident as @intro_pattern in {+ @ident}

   This allows naming the hypotheses introduced in the context by
   :n:`inversion @ident in {+ @ident}`.

.. tacv:: inversion_clear @ident in {+ @ident}

   Let :n:`{+ @ident}` be identifiers in the local context. This tactic behaves
   as generalizing :n:`{+ @ident}`, and then performing ``inversion_clear``.

.. tacv:: inversion_clear @ident as @intro_pattern in {+ @ident}

   This allows naming the hypotheses introduced in the context by
   :n:`inversion_clear @ident in {+ @ident}`.

.. tacv:: dependent inversion @ident
   :name: dependent inversion

   That must be used when :n:`@ident` appears in the current goal. It acts like
   ``inversion`` and then substitutes :n:`@ident` for the corresponding
   :n:`@@term` in the goal.

.. tacv:: dependent inversion @ident as @intro_pattern

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion @ident`.

.. tacv:: dependent inversion_clear @ident

   Like ``dependent inversion``, except that :n:`@ident` is cleared from the
   local context.

.. tacv:: dependent inversion_clear @ident as @intro_pattern

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion_clear @ident`.

.. tacv:: dependent inversion @ident with @term
   :name: dependent inversion ... with ...

   This variant allows you to specify the generalization of the goal. It is
   useful when the system fails to generalize the goal automatically. If
   :n:`@ident` has type :g:`(I t)` and :g:`I` has type :g:`forall (x:T), s`,
   then :n:`@term` must be of type :g:`I:forall (x:T), I x -> s'` where
   :g:`s'` is the type of the goal.

.. tacv:: dependent inversion @ident as @intro_pattern with @term

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion @ident with @term`.

.. tacv:: dependent inversion_clear @ident with @term

   Like :tacn:`dependent inversion ... with ...` with but clears :n:`@ident` from the
   local context.

.. tacv:: dependent inversion_clear @ident as @intro_pattern with @term

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion_clear @ident with @term`.

.. tacv:: simple inversion @ident
   :name: simple inversion

   It is a very primitive inversion tactic that derives all the necessary
   equalities but it does not simplify the constraints as ``inversion`` does.

.. tacv:: simple inversion @ident as @intro_pattern

   This allows naming the hypotheses introduced in the context by
   ``simple inversion``.

.. tacv:: inversion @ident using @ident

   Let :n:`@ident` have type :g:`(I t)` (:g:`I` an inductive predicate) in the
   local context, and :n:`@ident` be a (dependent) inversion lemma. Then, this
   tactic refines the current goal with the specified lemma.

.. tacv:: inversion @ident using @ident in {+ @ident}

   This tactic behaves as generalizing :n:`{+ @ident}`, then doing
   :n:`inversion @ident using @ident`.

.. tacv:: inversion_sigma
   :name: inversion_sigma

   This tactic turns equalities of dependent pairs (e.g.,
   :g:`existT P x p = existT P y q`, frequently left over by inversion on
   a dependent type family) into pairs of equalities (e.g., a hypothesis
   :g:`H : x = y` and a hypothesis of type :g:`rew H in p = q`); these
   hypotheses can subsequently be simplified using :tacn:`subst`, without ever
   invoking any kind of axiom asserting uniqueness of identity proofs. If you
   want to explicitly specify the hypothesis to be inverted, or name the
   generated hypotheses, you can invoke
   :n:`induction H as [H1 H2] using eq_sigT_rect.` This tactic also works for
   :g:`sig`, :g:`sigT2`, and :g:`sig2`, and there are similar :g:`eq_sig`
   :g:`***_rect` induction lemmas.

.. example::

   *Non-dependent inversion*.

   Let us consider the relation Le over natural numbers and the following
   variables:

   .. coqtop:: all

      Inductive Le : nat -> nat -> Set :=
      | LeO : forall n:nat, Le 0 n
      | LeS : forall n m:nat, Le n m -> Le (S n) (S m).
      Variable P : nat -> nat -> Prop.
      Variable Q : forall n m:nat, Le n m -> Prop.

   Let us consider the following goal:

   .. coqtop:: none

      Goal forall n m, Le (S n) m -> P n m.
      intros.

   .. coqtop:: all

      Show.

   To prove the goal, we may need to reason by cases on H and to derive
   that m is necessarily of the form (S m 0 ) for certain m 0 and that
   (Le n m 0 ). Deriving these conditions corresponds to proving that the
   only possible constructor of (Le (S n) m) isLeS and that we can invert
   the-> in the type of LeS. This inversion is possible because Le is the
   smallest set closed by the constructors LeO and LeS.

   .. coqtop:: undo all

      inversion_clear H.

   Note that m has been substituted in the goal for (S m0) and that the
   hypothesis (Le n m0) has been added to the context.

   Sometimes it is interesting to have the equality m=(S m0) in the
   context to use it after. In that case we can use inversion that does
   not clear the equalities:

   .. coqtop:: undo all

      inversion H.

.. example::

   *Dependent inversion.*

   Let us consider the following goal:

   .. coqtop:: reset none

      Inductive Le : nat -> nat -> Set :=
      | LeO : forall n:nat, Le 0 n
      | LeS : forall n m:nat, Le n m -> Le (S n) (S m).
      Variable P : nat -> nat -> Prop.
      Variable Q : forall n m:nat, Le n m -> Prop.
      Goal forall n m (H:Le (S n) m), Q (S n) m H.
      intros.

   .. coqtop:: all

      Show.

   As H occurs in the goal, we may want to reason by cases on its
   structure and so, we would like inversion tactics to substitute H by
   the corresponding @term in constructor form. Neither :tacn:`inversion` nor
   :n:`inversion_clear` do such a substitution. To have such a behavior we
   use the dependent inversion tactics:

   .. coqtop:: all

      dependent inversion_clear H.

   Note that H has been substituted by (LeS n m0 l) andm by (S m0).

.. example::

   *Using inversion_sigma.*

   Let us consider the following inductive type of
   length-indexed lists, and a lemma about inverting equality of cons:

   .. coqtop:: reset all

      Require Import Coq.Logic.Eqdep_dec.

      Inductive vec A : nat -> Type :=
      | nil : vec A O
      | cons {n} (x : A) (xs : vec A n) : vec A (S n).

      Lemma invert_cons : forall A n x xs y ys,
               @cons A n x xs = @cons A n y ys
               -> xs = ys.

      Proof.
      intros A n x xs y ys H.

   After performing inversion, we are left with an equality of existTs:

   .. coqtop:: all

      inversion H.

   We can turn this equality into a usable form with inversion_sigma:

   .. coqtop:: all

      inversion_sigma.

   To finish cleaning up the proof, we will need to use the fact that
   that all proofs of n = n for n a nat are eq_refl:

   .. coqtop:: all

      let H := match goal with H : n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
      simpl in *.

   Finally, we can finish the proof:

   .. coqtop:: all

      assumption.
      Qed.

.. tacn:: fix @ident @num
   :name: fix

   This tactic is a primitive tactic to start a proof by induction. In
   general, it is easier to rely on higher-level induction tactics such
   as the ones described in :tacn:`induction`.

   In the syntax of the tactic, the identifier :n:`@ident` is the name given to
   the induction hypothesis. The natural number :n:`@num` tells on which
   premise of the current goal the induction acts, starting from 1,
   counting both dependent and non dependent products, but skipping local
   definitions. Especially, the current lemma must be composed of at
   least :n:`@num` products.

   Like in a fix expression, the induction hypotheses have to be used on
   structurally smaller arguments. The verification that inductive proof
   arguments are correct is done only at the time of registering the
   lemma in the environment. To know if the use of induction hypotheses
   is correct at some time of the interactive development of a proof, use
   the command ``Guarded`` (see Section :ref:`requestinginformation`).

.. tacv:: fix @ident @num with {+ (ident {+ @binder} [{struct @ident}] : @type)}

   This starts a proof by mutual induction. The statements to be simultaneously
   proved are respectively :g:`forall binder ... binder, type`.
   The identifiers :n:`@ident` are the names of the induction hypotheses. The identifiers
   :n:`@ident` are the respective names of the premises on which the induction
   is performed in the statements to be simultaneously proved (if not given, the
   system tries to guess itself what they are).

.. tacn:: cofix @ident
   :name: cofix

   This tactic starts a proof by coinduction. The identifier :n:`@ident` is the
   name given to the coinduction hypothesis. Like in a cofix expression,
   the use of induction hypotheses have to guarded by a constructor. The
   verification that the use of co-inductive hypotheses is correct is
   done only at the time of registering the lemma in the environment. To
   know if the use of coinduction hypotheses is correct at some time of
   the interactive development of a proof, use the command ``Guarded``
   (see Section :ref:`requestinginformation`).

.. tacv:: cofix @ident with {+ (@ident {+ @binder} : @type)}

   This starts a proof by mutual coinduction. The statements to be
   simultaneously proved are respectively :g:`forall binder ... binder, type`
   The identifiers :n:`@ident` are the names of the coinduction hypotheses.

.. _rewritingexpressions:

Rewriting expressions
---------------------

These tactics use the equality :g:`eq:forall A:Type, A->A->Prop` defined in
file ``Logic.v`` (see :ref:`coq-library-logic`). The notation for :g:`eq T t u` is
simply :g:`t=u` dropping the implicit type of :g:`t` and :g:`u`.

.. tacn:: rewrite @term
   :name: rewrite

   This tactic applies to any goal. The type of :token:`term` must have the form

   ``forall (x``:sub:`1` ``:A``:sub:`1` ``) ... (x``:sub:`n` ``:A``:sub:`n` ``). eq term``:sub:`1` ``term``:sub:`2` ``.``

   where :g:`eq` is the Leibniz equality or a registered setoid equality.

   Then :n:`rewrite @term` finds the first subterm matching `term`\ :sub:`1` in the goal,
   resulting in instances `term`:sub:`1`' and `term`:sub:`2`' and then
   replaces every occurrence of `term`:subscript:`1`' by `term`:subscript:`2`'.
   Hence, some of the variables :g:`x`\ :sub:`i` are solved by unification,
   and some of the types :g:`A`\ :sub:`1`:g:`, ..., A`\ :sub:`n` become new
   subgoals.

   .. exn:: The @term provided does not end with an equation.
      :undocumented:

   .. exn:: Tactic generated a subgoal identical to the original goal. This happens if @term does not occur in the goal.
      :undocumented:

   .. tacv:: rewrite -> @term

      Is equivalent to :n:`rewrite @term`

   .. tacv:: rewrite <- @term

      Uses the equality :n:`@term`:sub:`1` :n:`= @term` :sub:`2` from right to left

   .. tacv:: rewrite @term in clause

      Analogous to :n:`rewrite @term` but rewriting is done following clause
      (similarly to :ref:`performing computations <performingcomputations>`). For instance:

      + :n:`rewrite H in H`:sub:`1` will rewrite `H` in the hypothesis
        `H`:sub:`1` instead of the current goal.
      + :n:`rewrite H in H`:sub:`1` :g:`at 1, H`:sub:`2` :g:`at - 2 |- *` means
        :n:`rewrite H; rewrite H in H`:sub:`1` :g:`at 1; rewrite H in H`:sub:`2` :g:`at - 2.`
        In particular a failure will happen if any of these three simpler tactics
        fails.
      + :n:`rewrite H in * |-` will do :n:`rewrite H in H`:sub:`i` for all hypotheses
        :g:`H`:sub:`i` different from :g:`H`.
        A success will happen as soon as at least one of these simpler tactics succeeds.
      + :n:`rewrite H in *` is a combination of :n:`rewrite H` and :n:`rewrite H in * |-`
        that succeeds if at least one of these two tactics succeeds.

      Orientation :g:`->` or :g:`<-` can be inserted before the :token:`term` to rewrite.

   .. tacv:: rewrite @term at occurrences

      Rewrite only the given occurrences of :token:`term`. Occurrences are
      specified from left to right as for pattern (:tacn:`pattern`). The rewrite is
      always performed using setoid rewriting, even for Leibniz’s equality, so one
      has to ``Import Setoid`` to use this variant.

   .. tacv:: rewrite @term by tactic

      Use tactic to completely solve the side-conditions arising from the
      :tacn:`rewrite`.

   .. tacv:: rewrite {+, @term}

      Is equivalent to the `n` successive tactics :n:`{+; rewrite @term}`, each one
      working on the first subgoal generated by the previous one. Orientation
      :g:`->` or :g:`<-` can be inserted before each :token:`term` to rewrite.  One
      unique clause can be added at the end after the keyword in; it will then
      affect all rewrite operations.

   In all forms of rewrite described above, a :token:`term` to rewrite can be
   immediately prefixed by one of the following modifiers:

   + `?` : the tactic :n:`rewrite ?@term` performs the rewrite of :token:`term` as many
     times as possible (perhaps zero time). This form never fails.
   + :n:`@num?` : works similarly, except that it will do at most :token:`num` rewrites.
   + `!` : works as `?`, except that at least one rewrite should succeed, otherwise
     the tactic fails.
   + :n:`@num!` (or simply :n:`@num`) : precisely :token:`num` rewrites of :token:`term` will be done,
     leading to failure if these :token:`num` rewrites are not possible.

   .. tacv:: erewrite @term
      :name: erewrite

      This tactic works as :n:`rewrite @term` but turning
      unresolved bindings into existential variables, if any, instead of
      failing. It has the same variants as :tacn:`rewrite` has.

.. tacn:: replace @term with @term’
   :name: replace

   This tactic applies to any goal. It replaces all free occurrences of :n:`@term`
   in the current goal with :n:`@term’` and generates an equality :n:`@term = @term’`
   as a subgoal. This equality is automatically solved if it occurs among
   the assumptions, or if its symmetric form occurs. It is equivalent to
   :n:`cut @term = @term’; [intro H`:sub:`n` :n:`; rewrite <- H`:sub:`n` :n:`; clear H`:sub:`n`:n:`|| assumption || symmetry; try assumption]`.

   .. exn:: Terms do not have convertible types.
      :undocumented:

   .. tacv:: replace @term with @term’ by @tactic

      This acts as :n:`replace @term with @term’` but applies :token:`tactic` to solve the generated
      subgoal :n:`@term = @term’`.

   .. tacv:: replace @term

      Replaces :n:`@term` with :n:`@term’` using the first assumption whose type has
      the form :n:`@term = @term’` or :n:`@term’ = @term`.

   .. tacv:: replace -> @term

      Replaces :n:`@term` with :n:`@term’` using the first assumption whose type has
      the form :n:`@term = @term’`

   .. tacv:: replace <- @term

      Replaces :n:`@term` with :n:`@term’` using the first assumption whose type has
      the form :n:`@term’ = @term`

   .. tacv:: replace @term {? with @term} in clause {? by @tactic}
             replace -> @term in clause
             replace <- @term in clause

      Acts as before but the replacements take place in the specified clause (see
      :ref:`performingcomputations`) and not only in the conclusion of the goal. The
      clause argument must not contain any ``type of`` nor ``value of``.

   .. tacv:: cutrewrite <- (@term = @term’)
      :name: cutrewrite

      This tactic is deprecated. It can be replaced by :n:`enough (@term = @term’) as <-`.

   .. tacv:: cutrewrite -> (@term = @term’)

      This tactic is deprecated. It can be replaced by :n:`enough (@term = @term’) as ->`.


.. tacn:: subst @ident
   :name: subst

   This tactic applies to a goal that has :n:`@ident` in its context and (at
   least) one hypothesis, say :g:`H`, of type :n:`@ident = t` or :n:`t = @ident`
   with :n:`@ident` not occurring in :g:`t`. Then it replaces :n:`@ident` by
   :g:`t` everywhere in the goal (in the hypotheses and in the conclusion) and
   clears :n:`@ident` and :g:`H` from the context.

   If :n:`@ident` is a local definition of the form :n:`@ident := t`, it is also
   unfolded and cleared.

   .. note::
      + When several hypotheses have the form :n:`@ident = t` or :n:`t = @ident`, the
        first one is used.

      + If :g:`H` is itself dependent in the goal, it is replaced by the proof of
        reflexivity of equality.

   .. tacv:: subst {+ @ident}

      This is equivalent to :n:`subst @ident`:sub:`1`:n:`; ...; subst @ident`:sub:`n`.

   .. tacv:: subst

      This applies subst repeatedly from top to bottom to all identifiers of the
      context for which an equality of the form :n:`@ident = t` or :n:`t = @ident`
      or :n:`@ident := t` exists, with :n:`@ident` not occurring in ``t``.

   .. flag:: Regular Subst Tactic

      This option controls the behavior of :tacn:`subst`. When it is
      activated (it is by default), :tacn:`subst` also deals with the following corner cases:

      + A context with ordered hypotheses :n:`@ident`:sub:`1` :n:`= @ident`:sub:`2`
        and :n:`@ident`:sub:`1` :n:`= t`, or :n:`t′ = @ident`:sub:`1`` with `t′` not
        a variable, and no other hypotheses of the form :n:`@ident`:sub:`2` :n:`= u`
        or :n:`u = @ident`:sub:`2`; without the option, a second call to
        subst would be necessary to replace :n:`@ident`:sub:`2` by `t` or
        `t′` respectively.
      + The presence of a recursive equation which without the option would
        be a cause of failure of :tacn:`subst`.
      + A context with cyclic dependencies as with hypotheses :n:`@ident`:sub:`1` :n:`= f @ident`:sub:`2`
        and :n:`@ident`:sub:`2` :n:`= g @ident`:sub:`1` which without the
        option would be a cause of failure of :tacn:`subst`.

      Additionally, it prevents a local definition such as :n:`@ident := t` to be
      unfolded which otherwise it would exceptionally unfold in configurations
      containing hypotheses of the form :n:`@ident = u`, or :n:`u′ = @ident`
      with `u′` not a variable. Finally, it preserves the initial order of
      hypotheses, which without the option it may break.
      default.


.. tacn:: stepl @term
   :name: stepl

   This tactic is for chaining rewriting steps. It assumes a goal of the
   form :n:`R @term @term` where ``R`` is a binary relation and relies on a
   database of lemmas of the form :g:`forall x y z, R x y -> eq x z -> R z y`
   where `eq` is typically a setoid equality. The application of :n:`stepl @term`
   then replaces the goal by :n:`R @term @term` and adds a new goal stating
   :n:`eq @term @term`.

   .. cmd:: Declare Left Step @term

      Adds :n:`@term` to the database used by :tacn:`stepl`.

   This tactic is especially useful for parametric setoids which are not accepted
   as regular setoids for :tacn:`rewrite` and :tacn:`setoid_replace` (see
   :ref:`Generalizedrewriting`).

   .. tacv:: stepl @term by @tactic

      This applies :n:`stepl @term` then applies :token:`tactic` to the second goal.

   .. tacv:: stepr @term stepr @term by tactic
      :name: stepr

      This behaves as :tacn:`stepl` but on the right-hand-side of the binary
      relation. Lemmas are expected to be of the form
      :g:`forall x y z, R x y -> eq y z -> R x z`.

   .. cmd:: Declare Right Step @term

       Adds :n:`@term` to the database used by :tacn:`stepr`.


.. tacn:: change @term
   :name: change

   This tactic applies to any goal. It implements the rule ``Conv`` given in
   :ref:`subtyping-rules`. :g:`change U` replaces the current goal `T`
   with `U` providing that `U` is well-formed and that `T` and `U` are
   convertible.

   .. exn:: Not convertible.
      :undocumented:

   .. tacv:: change @term with @term’

      This replaces the occurrences of :n:`@term` by :n:`@term’` in the current goal.
      The term :n:`@term` and :n:`@term’` must be convertible.

   .. tacv:: change @term at {+ @num} with @term’

      This replaces the occurrences numbered :n:`{+ @num}` of :n:`@term` by :n:`@term’`
      in the current goal. The terms :n:`@term` and :n:`@term’` must be convertible.

      .. exn:: Too few occurrences.
         :undocumented:

   .. tacv:: change @term {? {? at {+ @num}} with @term} in @ident

      This applies the :tacn:`change` tactic not to the goal but to the hypothesis :n:`@ident`.

   .. seealso:: :ref:`Performing computations <performingcomputations>`

.. _performingcomputations:

Performing computations
---------------------------

This set of tactics implements different specialized usages of the
tactic :tacn:`change`.

All conversion tactics (including :tacn:`change`) can be parameterized by the
parts of the goal where the conversion can occur. This is done using
*goal clauses* which consists in a list of hypotheses and, optionally,
of a reference to the conclusion of the goal. For defined hypothesis
it is possible to specify if the conversion should occur on the type
part, the body part or both (default).

Goal clauses are written after a conversion tactic (tactics :tacn:`set`,
:tacn:`rewrite`, :tacn:`replace` and :tacn:`autorewrite` also use goal
clauses) and are introduced by the keyword `in`. If no goal clause is
provided, the default is to perform the conversion only in the
conclusion.

The syntax and description of the various goal clauses is the
following:

+ :n:`in {+ @ident} |-`  only in hypotheses :n:`{+ @ident}`
+ :n:`in {+ @ident} |- *` in hypotheses :n:`{+ @ident}` and in the
  conclusion
+ :n:`in * |-` in every hypothesis
+ :n:`in *` (equivalent to in :n:`* |- *`) everywhere
+ :n:`in (type of @ident) (value of @ident) ... |-` in type part of
  :n:`@ident`, in the value part of :n:`@ident`, etc.

For backward compatibility, the notation :n:`in {+ @ident}` performs
the conversion in hypotheses :n:`{+ @ident}`.

.. tacn:: cbv {* @flag}
          lazy {* @flag}
   :name: cbv; lazy

   These parameterized reduction tactics apply to any goal and perform
   the normalization of the goal according to the specified flags. In
   correspondence with the kinds of reduction considered in Coq namely
   :math:`\beta` (reduction of functional application), :math:`\delta`
   (unfolding of transparent constants, see :ref:`vernac-controlling-the-reduction-strategies`),
   :math:`\iota` (reduction of
   pattern matching over a constructed term, and unfolding of :g:`fix` and
   :g:`cofix` expressions) and :math:`\zeta` (contraction of local definitions), the
   flags are either ``beta``, ``delta``, ``match``, ``fix``, ``cofix``,
   ``iota`` or ``zeta``. The ``iota`` flag is a shorthand for ``match``, ``fix``
   and ``cofix``. The ``delta`` flag itself can be refined into
   :n:`delta {+ @qualid}` or :n:`delta -{+ @qualid}`, restricting in the first
   case the constants to unfold to the constants listed, and restricting in the
   second case the constant to unfold to all but the ones explicitly mentioned.
   Notice that the ``delta`` flag does not apply to variables bound by a let-in
   construction inside the :n:`@term` itself (use here the ``zeta`` flag). In
   any cases, opaque constants are not unfolded (see :ref:`vernac-controlling-the-reduction-strategies`).

   Normalization according to the flags is done by first evaluating the
   head of the expression into a *weak-head* normal form, i.e. until the
   evaluation is blocked by a variable (or an opaque constant, or an
   axiom), as e.g. in :g:`x u1 ... un` , or :g:`match x with ... end`, or
   :g:`(fix f x {struct x} := ...) x`, or is a constructed form (a
   :math:`\lambda`-expression, a constructor, a cofixpoint, an inductive type, a
   product type, a sort), or is a redex that the flags prevent to reduce. Once a
   weak-head normal form is obtained, subterms are recursively reduced using the
   same strategy.

   Reduction to weak-head normal form can be done using two strategies:
   *lazy* (``lazy`` tactic), or *call-by-value* (``cbv`` tactic). The lazy
   strategy is a call-by-need strategy, with sharing of reductions: the
   arguments of a function call are weakly evaluated only when necessary,
   and if an argument is used several times then it is weakly computed
   only once. This reduction is efficient for reducing expressions with
   dead code. For instance, the proofs of a proposition :g:`exists x. P(x)`
   reduce to a pair of a witness :g:`t`, and a proof that :g:`t` satisfies the
   predicate :g:`P`. Most of the time, :g:`t` may be computed without computing
   the proof of :g:`P(t)`, thanks to the lazy strategy.

   The call-by-value strategy is the one used in ML languages: the
   arguments of a function call are systematically weakly evaluated
   first. Despite the lazy strategy always performs fewer reductions than
   the call-by-value strategy, the latter is generally more efficient for
   evaluating purely computational expressions (i.e. with little dead code).

.. tacv:: compute
          cbv
   :name: compute; _

   These are synonyms for ``cbv beta delta iota zeta``.

.. tacv:: lazy

   This is a synonym for ``lazy beta delta iota zeta``.

.. tacv:: compute {+ @qualid}
          cbv {+ @qualid}

   These are synonyms of :n:`cbv beta delta {+ @qualid} iota zeta`.

.. tacv:: compute -{+ @qualid}
          cbv -{+ @qualid}

   These are synonyms of :n:`cbv beta delta -{+ @qualid} iota zeta`.

.. tacv:: lazy {+ @qualid}
          lazy -{+ @qualid}

   These are respectively synonyms of :n:`lazy beta delta {+ @qualid} iota zeta`
   and :n:`lazy beta delta -{+ @qualid} iota zeta`.

.. tacv:: vm_compute
   :name: vm_compute

   This tactic evaluates the goal using the optimized call-by-value evaluation
   bytecode-based virtual machine described in :cite:`CompiledStrongReduction`.
   This algorithm is dramatically more efficient than the algorithm used for the
   ``cbv`` tactic, but it cannot be fine-tuned. It is specially interesting for
   full evaluation of algebraic objects. This includes the case of
   reflection-based tactics.

.. tacv:: native_compute
   :name: native_compute

   This tactic evaluates the goal by compilation to Objective Caml as described
   in :cite:`FullReduction`. If Coq is running in native code, it can be
   typically two to five times faster than ``vm_compute``. Note however that the
   compilation cost is higher, so it is worth using only for intensive
   computations.

   .. flag:: NativeCompute Profiling

      On Linux, if you have the ``perf`` profiler installed, this option makes
      it possible to profile ``native_compute`` evaluations.

   .. opt:: NativeCompute Profile Filename @string
      :name: NativeCompute Profile Filename

      This option specifies the profile output; the default is
      ``native_compute_profile.data``. The actual filename used
      will contain extra characters to avoid overwriting an existing file; that
      filename is reported to the user.
      That means you can individually profile multiple uses of
      ``native_compute`` in a script. From the Linux command line, run ``perf report``
      on the profile file to see the results. Consult the ``perf`` documentation
      for more details.

.. flag:: Debug Cbv

   This option makes :tacn:`cbv` (and its derivative :tacn:`compute`) print
   information about the constants it encounters and the unfolding decisions it
   makes.

.. tacn:: red
   :name: red

   This tactic applies to a goal that has the form::

     forall (x:T1) ... (xk:Tk), T

   with :g:`T` :math:`\beta`:math:`\iota`:math:`\zeta`-reducing to :g:`c t`:sub:`1` :g:`... t`:sub:`n` and :g:`c` a
   constant. If :g:`c` is transparent then it replaces :g:`c` with its
   definition (say :g:`t`) and then reduces
   :g:`(t t`:sub:`1` :g:`... t`:sub:`n` :g:`)` according to :math:`\beta`:math:`\iota`:math:`\zeta`-reduction rules.

.. exn:: Not reducible.
   :undocumented:

.. exn:: No head constant to reduce.
   :undocumented:

.. tacn:: hnf
   :name: hnf

   This tactic applies to any goal. It replaces the current goal with its
   head normal form according to the :math:`\beta`:math:`\delta`:math:`\iota`:math:`\zeta`-reduction rules, i.e. it
   reduces the head of the goal until it becomes a product or an
   irreducible term. All inner :math:`\beta`:math:`\iota`-redexes are also reduced.

   Example: The term :g:`fun n : nat => S n + S n` is not reduced by :n:`hnf`.

.. note::
 The :math:`\delta` rule only applies to transparent constants (see :ref:`vernac-controlling-the-reduction-strategies`
 on transparency and opacity).

.. tacn:: cbn
          simpl
   :name: cbn; simpl

   These tactics apply to any goal. They try to reduce a term to
   something still readable instead of fully normalizing it. They perform
   a sort of strong normalization with two key differences:

   + They unfold a constant if and only if it leads to a :math:`\iota`-reduction,
     i.e. reducing a match or unfolding a fixpoint.
   + While reducing a constant unfolding to (co)fixpoints, the tactics
     use the name of the constant the (co)fixpoint comes from instead of
     the (co)fixpoint definition in recursive calls.

   The ``cbn`` tactic is claimed to be a more principled, faster and more
   predictable replacement for ``simpl``.

   The ``cbn`` tactic accepts the same flags as ``cbv`` and ``lazy``. The
   behavior of both ``simpl`` and ``cbn`` can be tuned using the
   Arguments vernacular command as follows:

   + A constant can be marked to be never unfolded by ``cbn`` or ``simpl``:

     .. example::

        .. coqtop:: all

           Arguments minus n m : simpl never.

     After that command an expression like :g:`(minus (S x) y)` is left
     untouched by the tactics ``cbn`` and ``simpl``.

   + A constant can be marked to be unfolded only if applied to enough
     arguments. The number of arguments required can be specified using the
     ``/`` symbol in the argument list of the :cmd:`Arguments` vernacular command.

     .. example::

        .. coqtop:: all

           Definition fcomp A B C f (g : A -> B) (x : A) : C := f (g x).
           Arguments fcomp {A B C} f g x /.
           Notation "f \o g" := (fcomp f g) (at level 50).

     After that command the expression :g:`(f \o g)` is left untouched by
     ``simpl`` while :g:`((f \o g) t)` is reduced to :g:`(f (g t))`.
     The same mechanism can be used to make a constant volatile, i.e.
     always unfolded.

     .. example::

        .. coqtop:: all

           Definition volatile := fun x : nat => x.
           Arguments volatile / x.

   + A constant can be marked to be unfolded only if an entire set of
     arguments evaluates to a constructor. The ``!`` symbol can be used to mark
     such arguments.

     .. example::

        .. coqtop:: all

           Arguments minus !n !m.

     After that command, the expression :g:`(minus (S x) y)` is left untouched
     by ``simpl``, while :g:`(minus (S x) (S y))` is reduced to :g:`(minus x y)`.

   + A special heuristic to determine if a constant has to be unfolded
     can be activated with the following command:

     .. example::

        .. coqtop:: all

           Arguments minus n m : simpl nomatch.

     The heuristic avoids to perform a simplification step that would expose a
     match construct in head position. For example the expression
     :g:`(minus (S (S x)) (S y))` is simplified to :g:`(minus (S x) y)`
     even if an extra simplification is possible.

   In detail, the tactic ``simpl`` first applies :math:`\beta`:math:`\iota`-reduction. Then, it
   expands transparent constants and tries to reduce further using :math:`\beta`:math:`\iota`-
   reduction. But, when no :math:`\iota` rule is applied after unfolding then
   :math:`\delta`-reductions are not applied. For instance trying to use ``simpl`` on
   :g:`(plus n O) = n` changes nothing.

   Notice that only transparent constants whose name can be reused in the
   recursive calls are possibly unfolded by ``simpl``. For instance a
   constant defined by :g:`plus' := plus` is possibly unfolded and reused in
   the recursive calls, but a constant such as :g:`succ := plus (S O)` is
   never unfolded. This is the main difference between ``simpl`` and ``cbn``.
   The tactic ``cbn`` reduces whenever it will be able to reuse it or not:
   :g:`succ t` is reduced to :g:`S t`.

.. tacv:: cbn {+ @qualid}
          cbn -{+ @qualid}

   These are respectively synonyms of :n:`cbn beta delta {+ @qualid} iota zeta`
   and :n:`cbn beta delta -{+ @qualid} iota zeta` (see :tacn:`cbn`).

.. tacv:: simpl @pattern

   This applies ``simpl`` only to the subterms matching :n:`@pattern` in the
   current goal.

.. tacv:: simpl @pattern at {+ @num}

   This applies ``simpl`` only to the :n:`{+ @num}` occurrences of the subterms
   matching :n:`@pattern` in the current goal.

   .. exn:: Too few occurrences.
      :undocumented:

.. tacv:: simpl @qualid
          simpl @string

   This applies :tacn:`simpl` only to the applicative subterms whose head occurrence
   is the unfoldable constant :n:`@qualid` (the constant can be referred to by
   its notation using :n:`@string` if such a notation exists).

.. tacv:: simpl @qualid at {+ @num}
          simpl @string at {+ @num}

   This applies ``simpl`` only to the :n:`{+ @num}` applicative subterms whose
   head occurrence is :n:`@qualid` (or :n:`@string`).

.. flag:: Debug RAKAM

   This option makes :tacn:`cbn` print various debugging information.
   ``RAKAM`` is the Refolding Algebraic Krivine Abstract Machine.

.. tacn:: unfold @qualid
   :name: unfold

   This tactic applies to any goal. The argument qualid must denote a
   defined transparent constant or local definition (see
   :ref:`gallina-definitions` and :ref:`vernac-controlling-the-reduction-strategies`). The tactic
   ``unfold`` applies the :math:`\delta` rule to each occurrence of the constant to which
   :n:`@qualid` refers in the current goal and then replaces it with its
   :math:`\beta`:math:`\iota`-normal form.

.. exn:: @qualid does not denote an evaluable constant.
   :undocumented:

.. tacv:: unfold @qualid in @ident

   Replaces :n:`@qualid` in hypothesis :n:`@ident` with its definition
   and replaces the hypothesis with its :math:`\beta`:math:`\iota` normal form.

.. tacv:: unfold {+, @qualid}

   Replaces *simultaneously* :n:`{+, @qualid}` with their definitions and
   replaces the current goal with its :math:`\beta`:math:`\iota` normal form.

.. tacv:: unfold {+, @qualid at {+, @num }}

   The lists :n:`{+, @num}` specify the occurrences of :n:`@qualid` to be
   unfolded. Occurrences are located from left to right.

   .. exn:: Bad occurrence number of @qualid.
      :undocumented:

   .. exn:: @qualid does not occur.
      :undocumented:

.. tacv:: unfold @string

   If :n:`@string` denotes the discriminating symbol of a notation (e.g. "+") or
   an expression defining a notation (e.g. `"_ + _"`), and this notation refers to an unfoldable constant, then the
   tactic unfolds it.

.. tacv:: unfold @string%key

   This is variant of :n:`unfold @string` where :n:`@string` gets its
   interpretation from the scope bound to the delimiting key :n:`key`
   instead of its default interpretation (see :ref:`Localinterpretationrulesfornotations`).
.. tacv:: unfold {+, qualid_or_string at {+, @num}}

   This is the most general form, where :n:`qualid_or_string` is either a
   :n:`@qualid` or a :n:`@string` referring to a notation.

.. tacn:: fold @term
   :name: fold

   This tactic applies to any goal. The term :n:`@term` is reduced using the
   ``red`` tactic. Every occurrence of the resulting :n:`@term` in the goal is
   then replaced by :n:`@term`.

.. tacv:: fold {+ @term}

   Equivalent to :n:`fold @term ; ... ; fold @term`.

.. tacn:: pattern @term
   :name: pattern

   This command applies to any goal. The argument :n:`@term` must be a free
   subterm of the current goal. The command pattern performs :math:`\beta`-expansion
   (the inverse of :math:`\beta`-reduction) of the current goal (say :g:`T`) by

   + replacing all occurrences of :n:`@term` in :g:`T` with a fresh variable
   + abstracting this variable
   + applying the abstracted goal to :n:`@term`

   For instance, if the current goal :g:`T` is expressible as
   :math:`\varphi`:g:`(t)` where the notation captures all the instances of :g:`t`
   in :math:`\varphi`:g:`(t)`, then :n:`pattern t` transforms it into
   :g:`(fun x:A =>` :math:`\varphi`:g:`(x)) t`. This tactic can be used, for
   instance, when the tactic ``apply`` fails on matching.

.. tacv:: pattern @term at {+ @num}

   Only the occurrences :n:`{+ @num}` of :n:`@term` are considered for
   :math:`\beta`-expansion. Occurrences are located from left to right.

.. tacv:: pattern @term at - {+ @num}

   All occurrences except the occurrences of indexes :n:`{+ @num }`
   of :n:`@term` are considered for :math:`\beta`-expansion. Occurrences are located from
   left to right.

.. tacv:: pattern {+, @term}

   Starting from a goal :math:`\varphi`:g:`(t`:sub:`1` :g:`... t`:sub:`m`:g:`)`,
   the tactic :n:`pattern t`:sub:`1`:n:`, ..., t`:sub:`m` generates the
   equivalent goal
   :g:`(fun (x`:sub:`1`:g:`:A`:sub:`1`:g:`) ... (x`:sub:`m` :g:`:A`:sub:`m` :g:`) =>`:math:`\varphi`:g:`(x`:sub:`1` :g:`... x`:sub:`m` :g:`)) t`:sub:`1` :g:`... t`:sub:`m`.
   If :g:`t`:sub:`i` occurs in one of the generated types :g:`A`:sub:`j` these
   occurrences will also be considered and possibly abstracted.

.. tacv:: pattern {+, @term at {+ @num}}

   This behaves as above but processing only the occurrences :n:`{+ @num}` of
   :n:`@term` starting from :n:`@term`.

.. tacv:: pattern {+, @term {? at {? -} {+, @num}}}

   This is the most general syntax that combines the different variants.

Conversion tactics applied to hypotheses
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: conv_tactic in {+, @ident}

   Applies the conversion tactic :n:`conv_tactic` to the hypotheses
   :n:`{+ @ident}`. The tactic :n:`conv_tactic` is any of the conversion tactics
   listed in this section.

   If :n:`@ident` is a local definition, then :n:`@ident` can be replaced by
   (type of :n:`@ident`) to address not the body but the type of the local
   definition.

   Example: :n:`unfold not in (type of H1) (type of H3)`.

.. exn:: No such hypothesis: @ident.
   :undocumented:


.. _automation:

Automation
----------

.. tacn:: auto
   :name: auto

   This tactic implements a Prolog-like resolution procedure to solve the
   current goal. It first tries to solve the goal using the assumption
   tactic, then it reduces the goal to an atomic one using intros and
   introduces the newly generated hypotheses as hints. Then it looks at
   the list of tactics associated to the head symbol of the goal and
   tries to apply one of them (starting from the tactics with lower
   cost). This process is recursively applied to the generated subgoals.

   By default, auto only uses the hypotheses of the current goal and the
   hints of the database named core.

.. tacv:: auto @num

   Forces the search depth to be :token:`num`. The maximal search depth
   is 5 by default.

.. tacv:: auto with {+ @ident}

   Uses the hint databases :n:`{+ @ident}` in addition to the database core.

   .. seealso::
      :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>` for the list of
      pre-defined databases and the way to create or extend a database.

.. tacv:: auto with *

   Uses all existing hint databases.

   .. seealso:: :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>`

.. tacv:: auto using {+ @ident__i} {? with {+ @ident } }

   Uses lemmas :n:`@ident__i` in addition to hints. If :n:`@ident` is an
   inductive type, it is the collection of its constructors which are added
   as hints.

.. tacv:: info_auto

   Behaves like auto but shows the tactics it uses to solve the goal. This
   variant is very useful for getting a better understanding of automation, or
   to know what lemmas/assumptions were used.

.. tacv:: debug auto
   :name: debug auto

   Behaves like :tacn:`auto` but shows the tactics it tries to solve the goal,
   including failing paths.

.. tacv:: {? info_}auto {? @num} {? using {+ @lemma}} {? with {+ @ident}}

  This is the most general form, combining the various options.

.. tacv:: trivial
   :name: trivial

   This tactic is a restriction of auto that is not recursive
   and tries only hints that cost `0`. Typically it solves trivial
   equalities like :g:`X=X`.

.. tacv:: trivial with {+ @ident}
   :undocumented:

.. tacv:: trivial with *
   :undocumented:

.. tacv:: trivial using {+ @lemma}
   :undocumented:

.. tacv:: debug trivial
   :name: debug trivial
   :undocumented:

.. tacv:: info_trivial
   :name: info_trivial
   :undocumented:

.. tacv:: {? info_}trivial {? using {+ @lemma}} {? with {+ @ident}}
   :undocumented:

.. note::
  :tacn:`auto` either solves completely the goal or else leaves it
  intact. :tacn:`auto` and :tacn:`trivial` never fail.

The following options enable printing of informative or debug information for
the :tacn:`auto` and :tacn:`trivial` tactics:

.. flag:: Info Auto
          Debug Auto
          Info Trivial
          Debug Trivial
   :undocumented:

.. seealso:: :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>`

.. tacn:: eauto
   :name: eauto

   This tactic generalizes :tacn:`auto`. While :tacn:`auto` does not try
   resolution hints which would leave existential variables in the goal,
   :tacn:`eauto` does try them (informally speaking, it usessimple :tacn:`eapply`
   where :tacn:`auto` uses simple :tacn:`apply`). As a consequence, :tacn:`eauto`
   can solve such a goal:

   .. example::

      .. coqtop:: all

         Hint Resolve ex_intro.
         Goal forall P:nat -> Prop, P 0 -> exists n, P n.
         eauto.

      Note that ``ex_intro`` should be declared as a hint.


.. tacv:: {? info_}eauto {? @num} {? using {+ @lemma}} {? with {+ @ident}}

   The various options for :tacn:`eauto` are the same as for :tacn:`auto`.

:tacn:`eauto` also obeys the following options:

.. flag:: Info Eauto
          Debug Eauto
          :undocumented:

.. seealso:: :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>`


.. tacn:: autounfold with {+ @ident}
   :name: autounfold

   This tactic unfolds constants that were declared through a :cmd:`Hint Unfold`
   in the given databases.

.. tacv:: autounfold with {+ @ident} in clause

   Performs the unfolding in the given clause.

.. tacv:: autounfold with *

   Uses the unfold hints declared in all the hint databases.

.. tacn:: autorewrite with {+ @ident}
   :name: autorewrite

   This tactic [4]_ carries out rewritings according to the rewriting rule
   bases :n:`{+ @ident}`.

   Each rewriting rule from the base :n:`@ident` is applied to the main subgoal until
   it fails. Once all the rules have been processed, if the main subgoal has
   progressed (e.g., if it is distinct from the initial main goal) then the rules
   of this base are processed again. If the main subgoal has not progressed then
   the next base is processed. For the bases, the behavior is exactly similar to
   the processing of the rewriting rules.

   The rewriting rule bases are built with the :cmd:`Hint Rewrite`
   command.

.. warning::

   This tactic may loop if you build non terminating rewriting systems.

.. tacv:: autorewrite with {+ @ident} using @tactic

  Performs, in the same way, all the rewritings of the bases :n:`{+ @ident}`
  applying tactic to the main subgoal after each rewriting step.

.. tacv:: autorewrite with {+ @ident} in @qualid

   Performs all the rewritings in hypothesis :n:`@qualid`.

.. tacv:: autorewrite with {+ @ident} in @qualid using @tactic

  Performs all the rewritings in hypothesis :n:`@qualid` applying :n:`@tactic`
  to the main subgoal after each rewriting step.

.. tacv:: autorewrite with {+ @ident} in @clause

  Performs all the rewriting in the clause :n:`@clause`. The clause argument
  must not contain any ``type of`` nor ``value of``.

.. seealso::

   :ref:`Hint-Rewrite <hintrewrite>` for feeding the database of lemmas used by
   :tacn:`autorewrite` and :tacn:`autorewrite` for examples showing the use of this tactic.

.. tacn:: easy
   :name: easy

   This tactic tries to solve the current goal by a number of standard closing steps.
   In particular, it tries to close the current goal using the closing tactics
   :tacn:`trivial`, :tacn:`reflexivity`, :tacn:`symmetry`, :tacn:`contradiction`
   and :tacn:`inversion` of hypothesis.
   If this fails, it tries introducing variables and splitting and-hypotheses,
   using the closing tactics afterwards, and splitting the goal using
   :tacn:`split` and recursing.

   This tactic solves goals that belong to many common classes; in particular, many cases of
   unsatisfiable hypotheses, and simple equality goals are usually solved by this tactic.

.. tacv:: now @tactic
   :name: now

   Run :n:`@tactic` followed by :tacn:`easy`. This is a notation for :n:`@tactic; easy`.

Controlling automation
--------------------------

.. _thehintsdatabasesforautoandeauto:

The hints databases for auto and eauto
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The hints for :tacn:`auto` and :tacn:`eauto` are stored in databases. Each database
maps head symbols to a list of hints.

.. cmd:: Print Hint @ident

   Use this command
   to display the hints associated to the head symbol :n:`@ident`
   (see :ref:`Print Hint <printhint>`). Each hint has a cost that is a nonnegative
   integer, and an optional pattern. The hints with lower cost are tried first. A
   hint is tried by :tacn:`auto` when the conclusion of the current goal matches its
   pattern or when it has no pattern.

Creating Hint databases
```````````````````````

One can optionally declare a hint database using the command
:cmd:`Create HintDb`. If a hint is added to an unknown database, it will be
automatically created.

.. cmd:: Create HintDb @ident {? discriminated}

   This command creates a new database named :n:`@ident`. The database is
   implemented by a Discrimination Tree (DT) that serves as an index of
   all the lemmas. The DT can use transparency information to decide if a
   constant should be indexed or not
   (c.f. :ref:`The hints databases for auto and eauto <thehintsdatabasesforautoandeauto>`),
   making the retrieval more efficient. The legacy implementation (the default one
   for new databases) uses the DT only on goals without existentials (i.e., :tacn:`auto`
   goals), for non-Immediate hints and does not make use of transparency
   hints, putting more work on the unification that is run after
   retrieval (it keeps a list of the lemmas in case the DT is not used).
   The new implementation enabled by the discriminated option makes use
   of DTs in all cases and takes transparency information into account.
   However, the order in which hints are retrieved from the DT may differ
   from the order in which they were inserted, making this implementation
   observationally different from the legacy one.

The general command to add a hint to some databases :n:`{+ @ident}` is

.. cmd:: Hint @hint_definition : {+ @ident}

   .. cmdv:: Hint @hint_definition

      No database name is given: the hint is registered in the core database.

   .. cmdv:: Local Hint @hint_definition : {+ @ident}

      This is used to declare hints that must not be exported to the other modules
      that require and import the current module. Inside a section, the option
      Local is useless since hints do not survive anyway to the closure of
      sections.

   .. cmdv:: Local Hint @hint_definition

      Idem for the core database.

   .. cmdv:: Hint Resolve @term {? | {? @num} {? @pattern}}
      :name: Hint Resolve

      This command adds :n:`simple apply @term` to the hint list with the head
      symbol of the type of :n:`@term`. The cost of that hint is the number of
      subgoals generated by :n:`simple apply @term` or :n:`@num` if specified. The
      associated :n:`@pattern` is inferred from the conclusion of the type of
      :n:`@term` or the given :n:`@pattern` if specified. In case the inferred type
      of :n:`@term` does not start with a product the tactic added in the hint list
      is :n:`exact @term`. In case this type can however be reduced to a type
      starting with a product, the tactic :n:`simple apply @term` is also stored in
      the hints list. If the inferred type of :n:`@term` contains a dependent
      quantification on a variable which occurs only in the premisses of the type
      and not in its conclusion, no instance could be inferred for the variable by
      unification with the goal. In this case, the hint is added to the hint list
      of :tacn:`eauto` instead of the hint list of auto and a warning is printed. A
      typical example of a hint that is used only by :tacn:`eauto` is a transitivity
      lemma.

   .. exn:: @term cannot be used as a hint

      The head symbol of the type of :n:`@term` is a bound variable such that
      this tactic cannot be associated to a constant.

   .. cmdv:: Hint Resolve {+ @term}

      Adds each :n:`Hint Resolve @term`.

   .. cmdv:: Hint Resolve -> @term

      Adds the left-to-right implication of an equivalence as a hint (informally
      the hint will be used as :n:`apply <- @term`, although as mentionned
      before, the tactic actually used is a restricted version of
      :tacn:`apply`).

   .. cmdv:: Resolve <- @term

      Adds the right-to-left implication of an equivalence  as a hint.

   .. cmdv:: Hint Immediate @term
      :name: Hint Immediate

      This command adds :n:`simple apply @term; trivial` to the hint list associated
      with the head symbol of the type of :n:`@ident` in the given database. This
      tactic will fail if all the subgoals generated by :n:`simple apply @term` are
      not solved immediately by the :tacn:`trivial` tactic (which only tries tactics
      with cost 0).This command is useful for theorems such as the symmetry of
      equality or :g:`n+1=m+1 -> n=m` that we may like to introduce with a limited
      use in order to avoid useless proof-search. The cost of this tactic (which
      never generates subgoals) is always 1, so that it is not used by :tacn:`trivial`
      itself.

   .. exn:: @term cannot be used as a hint
      :undocumented:

   .. cmdv:: Immediate {+ @term}

      Adds each :n:`Hint Immediate @term`.

   .. cmdv:: Hint Constructors @ident
      :name: Hint Constructors

      If :n:`@ident` is an inductive type, this command adds all its constructors as
      hints of type ``Resolve``. Then, when the conclusion of current goal has the form
      :n:`(@ident ...)`, :tacn:`auto` will try to apply each constructor.

   .. exn:: @ident is not an inductive type
      :undocumented:

   .. cmdv:: Hint Constructors {+ @ident}

      Adds each :n:`Hint Constructors @ident`.

   .. cmdv:: Hint Unfold @qualid
      :name: Hint Unfold

      This adds the tactic :n:`unfold @qualid` to the hint list that will only be
      used when the head constant of the goal is :n:`@ident`.
      Its cost is 4.

   .. cmdv:: Hint Unfold {+ @ident}

      Adds each :n:`Hint Unfold @ident`.

   .. cmdv:: Hint Transparent {+ @qualid}
             Hint Opaque {+ @qualid}
      :name: Hint Transparent; Hint Opaque

      This adds transparency hints to the database, making :n:`@qualid`
      transparent or opaque constants during resolution. This information is used
      during unification of the goal with any lemma in the database and inside the
      discrimination network to relax or constrain it in the case of discriminated
      databases.

   .. cmdv:: Hint Variables %( Transparent %| Opaque %)
             Hint Constants %( Transparent %| Opaque %)
      :name: Hint Variables; Hint Constants

      This sets the transparency flag used during unification of
      hints in the database for all constants or all variables,
      overwritting the existing settings of opacity. It is advised
      to use this just after a :cmd:`Create HintDb` command.

   .. cmdv:: Hint Extern @num {? @pattern} => @tactic
      :name: Hint Extern

      This hint type is to extend :tacn:`auto` with tactics other than :tacn:`apply` and
      :tacn:`unfold`. For that, we must specify a cost, an optional :n:`@pattern` and a
      :n:`@tactic` to execute.

      .. example::

         .. coqtop:: in

            Hint Extern 4 (~(_ = _)) => discriminate.

         Now, when the head of the goal is a disequality, ``auto`` will try
         discriminate if it does not manage to solve the goal with hints with a
         cost less than 4.

      One can even use some sub-patterns of the pattern in
      the tactic script. A sub-pattern is a question mark followed by an
      identifier, like ``?X1`` or ``?X2``. Here is an example:

      .. example::

         .. coqtop:: reset all

            Require Import List.
            Hint Extern 5 ({?X1 = ?X2} + {?X1 <> ?X2}) => generalize  X1, X2; decide equality : eqdec.
            Goal forall a b:list (nat * nat), {a = b} + {a <> b}.
            Info 1 auto with eqdec.

   .. cmdv:: Hint Cut @regexp
      :name: Hint Cut

      .. warning::

         These hints currently only apply to typeclass proof search and the
         :tacn:`typeclasses eauto` tactic.

      This command can be used to cut the proof-search tree according to a regular
      expression matching paths to be cut. The grammar for regular expressions is
      the following. Beware, there is no operator precedence during parsing, one can
      check with :cmd:`Print HintDb` to verify the current cut expression:

      .. productionlist:: `regexp`
          e : ident      hint or instance identifier
            :| _         any hint
            :| e\|e′     disjunction
            :| e e′      sequence
            :| e *       Kleene star
            :| emp       empty
            :| eps       epsilon
            :| ( e  )

      The `emp` regexp does not match any search path while `eps`
      matches the empty path. During proof search, the path of
      successive successful hints on a search branch is recorded, as a
      list of identifiers for the hints (note that Hint Extern’s do not have
      an associated identifier).
      Before applying any hint :n:`@ident` the current path `p` extended with
      :n:`@ident` is matched against the current cut expression `c` associated to
      the hint database. If matching succeeds, the hint is *not* applied. The
      semantics of ``Hint Cut e`` is to set the cut expression to ``c | e``, the
      initial cut expression being `emp`.

   .. cmdv:: Hint Mode @qualid {* (+ | ! | -)}
      :name: Hint Mode

      This sets an optional mode of use of the identifier :n:`@qualid`. When
      proof-search faces a goal that ends in an application of :n:`@qualid` to
      arguments :n:`@term ... @term`, the mode tells if the hints associated to
      :n:`@qualid` can be applied or not. A mode specification is a list of n ``+``,
      ``!`` or ``-`` items that specify if an argument of the identifier is to be
      treated as an input (``+``), if its head only is an input (``!``) or an output
      (``-``) of the identifier. For a mode to match a list of arguments, input
      terms and input heads *must not* contain existential variables or be
      existential variables respectively, while outputs can be any term. Multiple
      modes can be declared for a single identifier, in that case only one mode
      needs to match the arguments for the hints to be applied.The head of a term
      is understood here as the applicative head, or the match or projection
      scrutinee’s head, recursively, casts being ignored. ``Hint Mode`` is
      especially useful for typeclasses, when one does not want to support default
      instances and avoid ambiguity in general. Setting a parameter of a class as an
      input forces proof-search to be driven by that index of the class, with ``!``
      giving more flexibility by allowing existentials to still appear deeper in the
      index but not at its head.

   .. note::

      One can use an ``Extern`` hint with no pattern to do pattern matching on
      hypotheses using ``match goal`` with inside the tactic.


Hint databases defined in the Coq standard library
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Several hint databases are defined in the Coq standard library. The
actual content of a database is the collection of hints declared
to belong to this database in each of the various modules currently
loaded. Especially, requiring new modules may extend the database.
At Coq startup, only the core database is nonempty and can be used.

:core: This special database is automatically used by ``auto``, except when
       pseudo-database ``nocore`` is given to ``auto``. The core database
       contains only basic lemmas about negation, conjunction, and so on.
       Most of the hints in this database come from the Init and Logic directories.

:arith: This database contains all lemmas about Peano’s arithmetic proved in the
        directories Init and Arith.

:zarith: contains lemmas about binary signed integers from the directories
         theories/ZArith. When required, the module Omega also extends the
         database zarith with a high-cost hint that calls ``omega`` on equations
         and inequalities in ``nat`` or ``Z``.

:bool: contains lemmas about booleans, mostly from directory theories/Bool.

:datatypes: is for lemmas about lists, streams and so on that are mainly proved
            in the Lists subdirectory.

:sets: contains lemmas about sets and relations from the directories Sets and
       Relations.

:typeclass_instances: contains all the typeclass instances declared in the
                      environment, including those used for ``setoid_rewrite``,
                      from the Classes directory.

You are advised not to put your own hints in the core database, but
use one or several databases specific to your development.

.. _removehints:

.. cmd:: Remove Hints {+ @term} : {+ @ident}

   This command removes the hints associated to terms :n:`{+ @term}` in databases
   :n:`{+ @ident}`.

.. _printhint:

.. cmd:: Print Hint

   This command displays all hints that apply to the current goal. It
   fails if no proof is being edited, while the two variants can be used
   at every moment.

**Variants:**


.. cmd:: Print Hint @ident

   This command displays only tactics associated with :n:`@ident` in the hints
   list. This is independent of the goal being edited, so this command will not
   fail if no goal is being edited.

.. cmd:: Print Hint *

   This command displays all declared hints.

.. cmd:: Print HintDb @ident

   This command displays all hints from database :n:`@ident`.

.. _hintrewrite:

.. cmd:: Hint Rewrite {+ @term} : {+ @ident}

   This vernacular command adds the terms :n:`{+ @term}` (their types must be
   equalities) in the rewriting bases :n:`{+ @ident}` with the default orientation
   (left to right). Notice that the rewriting bases are distinct from the ``auto``
   hint bases and thatauto does not take them into account.

   This command is synchronous with the section mechanism (see :ref:`section-mechanism`):
   when closing a section, all aliases created by ``Hint Rewrite`` in that
   section are lost. Conversely, when loading a module, all ``Hint Rewrite``
   declarations at the global level of that module are loaded.

**Variants:**

.. cmd:: Hint Rewrite -> {+ @term} : {+ @ident}

   This is strictly equivalent to the command above (we only make explicit the
   orientation which otherwise defaults to ->).

.. cmd:: Hint Rewrite <- {+ @term} : {+ @ident}

   Adds the rewriting rules :n:`{+ @term}` with a right-to-left orientation in
   the bases :n:`{+ @ident}`.

.. cmd:: Hint Rewrite {+ @term} using tactic : {+ @ident}

   When the rewriting rules :n:`{+ @term}` in :n:`{+ @ident}` will be used, the
   tactic ``tactic`` will be applied to the generated subgoals, the main subgoal
   excluded.

.. cmd:: Print Rewrite HintDb @ident

   This command displays all rewrite hints contained in :n:`@ident`.

Hint locality
~~~~~~~~~~~~~

Hints provided by the ``Hint`` commands are erased when closing a section.
Conversely, all hints of a module ``A`` that are not defined inside a
section (and not defined with option ``Local``) become available when the
module ``A`` is imported (using e.g. ``Require Import A.``).

As of today, hints only have a binary behavior regarding locality, as
described above: either they disappear at the end of a section scope,
or they remain global forever. This causes a scalability issue,
because hints coming from an unrelated part of the code may badly
influence another development. It can be mitigated to some extent
thanks to the :cmd:`Remove Hints` command,
but this is a mere workaround and has some limitations (for instance, external
hints cannot be removed).

A proper way to fix this issue is to bind the hints to their module scope, as
for most of the other objects Coq uses. Hints should only be made available when
the module they are defined in is imported, not just required. It is very
difficult to change the historical behavior, as it would break a lot of scripts.
We propose a smooth transitional path by providing the :opt:`Loose Hint Behavior`
option which accepts three flags allowing for a fine-grained handling of
non-imported hints.

.. opt:: Loose Hint Behavior %( "Lax" %| "Warn" %| "Strict" %)
   :name: Loose Hint Behavior

   This option accepts three values, which control the behavior of hints w.r.t.
   :cmd:`Import`:

   - "Lax": this is the default, and corresponds to the historical behavior,
     that is, hints defined outside of a section have a global scope.

   - "Warn": outputs a warning when a non-imported hint is used. Note that this
     is an over-approximation, because a hint may be triggered by a run that
     will eventually fail and backtrack, resulting in the hint not being
     actually useful for the proof.

   - "Strict": changes the behavior of an unloaded hint to a immediate fail
     tactic, allowing to emulate an import-scoped hint mechanism.

.. _tactics-implicit-automation:

Setting implicit automation tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Proof with @tactic

   This command may be used to start a proof. It defines a default tactic
   to be used each time a tactic command ``tactic``:sub:`1` is ended by ``...``.
   In this case the tactic command typed by the user is equivalent to
   ``tactic``:sub:`1` ``;tactic``.

   .. seealso:: :cmd:`Proof` in :ref:`proof-editing-mode`.


   .. cmdv:: Proof with tactic using {+ @ident}

      Combines in a single line ``Proof with`` and ``Proof using``, see :ref:`proof-editing-mode`

   .. cmdv:: Proof using {+ @ident} with @tactic

      Combines in a single line ``Proof with`` and ``Proof using``, see :ref:`proof-editing-mode`

   .. cmd:: Declare Implicit Tactic @tactic

      This command declares a tactic to be used to solve implicit arguments
      that Coq does not know how to solve by unification. It is used every
      time the term argument of a tactic has one of its holes not fully
      resolved.

      .. deprecated:: 8.9

         This command is deprecated. Use :ref:`typeclasses <typeclasses>` or
         :ref:`tactics-in-terms <tactics-in-terms>` instead.

      .. example::

         .. coqtop:: reset all

            Parameter quo : nat -> forall n:nat, n<>0 -> nat.
            Notation "x // y" := (quo x y _) (at level 40).
            Declare Implicit Tactic assumption.
            Goal forall n m, m<>0 -> { q:nat & { r | q * m + r = n } }.
            intros.
            exists (n // m).

         The tactic ``exists (n // m)`` did not fail. The hole was solved
         by ``assumption`` so that it behaved as ``exists (quo n m H)``.

.. _decisionprocedures:

Decision procedures
-------------------

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
   to be unfolded. This option is on by default.

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
   :g:`auto with *`, it can be reset locally or globally using this option.

   .. cmd:: Print Firstorder Solver

      Prints the default tactic used by :tacn:`firstorder` when no rule applies.

.. tacv:: firstorder @tactic

   Tries to solve the goal with :n:`@tactic` when no logical rule may apply.

.. tacv:: firstorder using {+ @qualid}

  Adds lemmas :n:`{+ @qualid}` to the proof-search environment. If :n:`@qualid`
  refers to an inductive type, it is the collection of its constructors which are
  added to the proof-search environment.

.. tacv:: firstorder with {+ @ident}

  Adds lemmas from :tacn:`auto` hint bases :n:`{+ @ident}` to the proof-search
  environment.

.. tacv:: firstorder tactic using {+ @qualid} with {+ @ident}

  This combines the effects of the different variants of :tacn:`firstorder`.

.. opt:: Firstorder Depth @num
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

.. tacv:: congruence n

  Tries to add at most `n` instances of hypotheses stating quantified equalities
  to the problem in order to solve it. A bigger value of `n` does not make
  success slower, only failure. You might consider adding some lemmas as
  hypotheses using assert in order for :tacn:`congruence` to use them.

.. tacv:: congruence with {+ @term}
   :name: congruence with

   Adds :n:`{+ @term}` to the pool of terms used by :tacn:`congruence`. This helps
   in case you have partially applied constructors in your goal.

.. exn:: I don’t know how to handle dependent equality.

  The decision procedure managed to find a proof of the goal or of a
  discriminable equality but this proof could not be built in Coq because of
  dependently-typed functions.

.. exn:: Goal is solvable by congruence but some arguments are missing. Try congruence with {+ @term}, replacing metavariables by arbitrary terms.

  The decision procedure could solve the goal with the provision that additional
  arguments are supplied for some partially applied constructors. Any term of an
  appropriate type will allow the tactic to successfully solve the goal. Those
  additional arguments can be given to congruence by filling in the holes in the
  terms given in the error message, using the :tacn:`congruence with` variant described above.

.. flag:: Congruence Verbose

  This option makes :tacn:`congruence` print debug information.


Checking properties of terms
----------------------------

Each of the following tactics acts as the identity if the check
succeeds, and results in an error otherwise.

.. tacn:: constr_eq @term @term
   :name: constr_eq

   This tactic checks whether its arguments are equal modulo alpha
   conversion, casts and universe constraints. It may unify universes.

.. exn:: Not equal.
   :undocumented:

.. exn:: Not equal (due to universes).
   :undocumented:

.. tacn:: constr_eq_strict @term @term
   :name: constr_eq_strict

   This tactic checks whether its arguments are equal modulo alpha
   conversion, casts and universe constraints. It does not add new
   constraints.

.. exn:: Not equal.
   :undocumented:

.. exn:: Not equal (due to universes).
   :undocumented:

.. tacn:: unify @term @term
   :name: unify

   This tactic checks whether its arguments are unifiable, potentially
   instantiating existential variables.

.. exn:: Unable to unify @term with @term.
   :undocumented:

.. tacv:: unify @term @term with @ident

   Unification takes the transparency information defined in the hint database
   :n:`@ident` into account (see :ref:`the hints databases for auto and eauto <thehintsdatabasesforautoandeauto>`).

.. tacn:: is_evar @term
   :name: is_evar

   This tactic checks whether its argument is a current existential
   variable. Existential variables are uninstantiated variables generated
   by :tacn:`eapply` and some other tactics.

.. exn:: Not an evar.
   :undocumented:

.. tacn:: has_evar @term
   :name: has_evar

   This tactic checks whether its argument has an existential variable as
   a subterm. Unlike context patterns combined with ``is_evar``, this tactic
   scans all subterms, including those under binders.

.. exn:: No evars.
   :undocumented:

.. tacn:: is_var @term
   :name: is_var

   This tactic checks whether its argument is a variable or hypothesis in
   the current goal context or in the opened sections.

.. exn:: Not a variable or hypothesis.
   :undocumented:


.. _equality:

Equality
--------


.. tacn:: f_equal
   :name: f_equal

   This tactic applies to a goal of the form :g:`f a`:sub:`1` :g:`... a`:sub:`n`
   :g:`= f′a′`:sub:`1` :g:`... a′`:sub:`n`.  Using :tacn:`f_equal` on such a goal
   leads to subgoals :g:`f=f′` and :g:`a`:sub:`1` = :g:`a′`:sub:`1` and so on up
   to :g:`a`:sub:`n` :g:`= a′`:sub:`n`. Amongst these subgoals, the simple ones
   (e.g. provable by :tacn:`reflexivity` or :tacn:`congruence`) are automatically
   solved by :tacn:`f_equal`.


.. tacn:: reflexivity
   :name: reflexivity

   This tactic applies to a goal that has the form :g:`t=u`. It checks that `t`
   and `u` are convertible and then solves the goal. It is equivalent to
   ``apply refl_equal``.

   .. exn:: The conclusion is not a substitutive equation.
      :undocumented:

   .. exn:: Unable to unify ... with ...
      :undocumented:


.. tacn:: symmetry
   :name: symmetry

   This tactic applies to a goal that has the form :g:`t=u` and changes it into
   :g:`u=t`.


.. tacv:: symmetry in @ident

   If the statement of the hypothesis ident has the form :g:`t=u`, the tactic
   changes it to :g:`u=t`.


.. tacn:: transitivity @term
   :name: transitivity

   This tactic applies to a goal that has the form :g:`t=u` and transforms it
   into the two subgoals :n:`t=@term` and :n:`@term=u`.


Equality and inductive sets
---------------------------

We describe in this section some special purpose tactics dealing with
equality and inductive sets or types. These tactics use the
equality :g:`eq:forall (A:Type), A->A->Prop`, simply written with the infix
symbol :g:`=`.

.. tacn:: decide equality
   :name: decide equality

   This tactic solves a goal of the form :g:`forall x y : R, {x = y} + {~ x = y}`,
   where :g:`R` is an inductive type such that its constructors do not take
   proofs or functions as arguments, nor objects in dependent types. It
   solves goals of the form :g:`{x = y} + {~ x = y}` as well.

.. tacn:: compare @term @term
   :name: compare

   This tactic compares two given objects :n:`@term` and :n:`@term` of an
   inductive datatype. If :g:`G` is the current goal, it leaves the sub-
   goals :n:`@term =@term -> G` and :n:`~ @term = @term -> G`. The type of
   :n:`@term` and :n:`@term` must satisfy the same restrictions as in the
   tactic ``decide equality``.

.. tacn:: simplify_eq @term
   :name: simplify_eq

   Let :n:`@term` be the proof of a statement of conclusion :n:`@term = @term`.
   If :n:`@term` and :n:`@term` are structurally different (in the sense
   described for the tactic :tacn:`discriminate`), then the tactic
   ``simplify_eq`` behaves as :n:`discriminate @term`, otherwise it behaves as
   :n:`injection @term`.

.. note::
   If some quantified hypothesis of the goal is named :n:`@ident`,
   then :n:`simplify_eq @ident` first introduces the hypothesis in the local
   context using :n:`intros until @ident`.

.. tacv:: simplify_eq @num

   This does the same thing as :n:`intros until @num` then
   :n:`simplify_eq @ident` where :n:`@ident` is the identifier for the last
   introduced hypothesis.

.. tacv:: simplify_eq @term with @bindings_list

   This does the same as :n:`simplify_eq @term` but using the given bindings to
   instantiate parameters or hypotheses of :n:`@term`.

.. tacv:: esimplify_eq @num
          esimplify_eq @term {? with @bindings_list}
   :name: esimplify_eq; _

   This works the same as :tacn:`simplify_eq` but if the type of :n:`@term`, or the
   type of the hypothesis referred to by :n:`@num`, has uninstantiated
   parameters, these parameters are left as existential variables.

.. tacv:: simplify_eq

   If the current goal has form :g:`t1 <> t2`, it behaves as
   :n:`intro @ident; simplify_eq @ident`.

.. tacn:: dependent rewrite -> @ident
   :name: dependent rewrite ->

   This tactic applies to any goal. If :n:`@ident` has type
   :g:`(existT B a b)=(existT B a' b')` in the local context (i.e. each
   :n:`@term` of the equality has a sigma type :g:`{ a:A & (B a)}`) this tactic
   rewrites :g:`a` into :g:`a'` and :g:`b` into :g:`b'` in the current goal.
   This tactic works even if :g:`B` is also a sigma type. This kind of
   equalities between dependent pairs may be derived by the
   :tacn:`injection` and :tacn:`inversion` tactics.

.. tacv:: dependent rewrite <- @ident
   :name: dependent rewrite <-

   Analogous to :tacn:`dependent rewrite ->` but uses the equality from right to
   left.

Inversion
---------

.. tacn:: functional inversion @ident
   :name: functional inversion

   :tacn:`functional inversion` is a tactic that performs inversion on hypothesis
   :n:`@ident` of the form :n:`@qualid {+ @term} = @term` or :n:`@term = @qualid
   {+ @term}` where :n:`@qualid` must have been defined using Function (see
   :ref:`advanced-recursive-functions`). Note that this tactic is only
   available after a ``Require Import FunInd``.

   .. exn:: Hypothesis @ident must contain at least one Function.
      :undocumented:

   .. exn:: Cannot find inversion information for hypothesis @ident.

      This error may be raised when some inversion lemma failed to be generated by
      Function.


   .. tacv:: functional inversion @num

      This does the same thing as :n:`intros until @num` folowed by
      :n:`functional inversion @ident` where :token:`ident` is the
      identifier for the last introduced hypothesis.

   .. tacv:: functional inversion @ident @qualid
             functional inversion @num @qualid

      If the hypothesis :token:`ident` (or :token:`num`) has a type of the form
      :n:`@qualid__1 {+ @term__i } = @qualid__2 {+ @term__j }` where
      :n:`@qualid__1` and :n:`@qualid__2` are valid candidates to
      functional inversion, this variant allows choosing which :token:`qualid`
      is inverted.

.. tacn:: quote @ident
   :name: quote

This kind of inversion has nothing to do with the tactic :tacn:`inversion`
above. This tactic does :g:`change (@ident t)`, where `t` is a term built in
order to ensure the convertibility. In other words, it does inversion of the
function :n:`@ident`. This function must be a fixpoint on a simple recursive
datatype: see :ref:`quote` for the full details.


.. exn:: quote: not a simple fixpoint.

  Happens when quote is not able to perform inversion properly.


.. tacv::  quote @ident {* @ident}

  All terms that are built only with :n:`{* @ident}` will be considered by quote
  as constants rather than variables.

Classical tactics
-----------------

In order to ease the proving process, when the Classical module is
loaded. A few more tactics are available. Make sure to load the module
using the ``Require Import`` command.

.. tacn:: classical_left
          classical_right
   :name: classical_left; classical_right

   These tactics are the analog of :tacn:`left` and :tacn:`right`
   but using classical logic. They can only be used for
   disjunctions. Use :tacn:`classical_left` to prove the left part of the
   disjunction with the assumption that the negation of right part holds.
   Use :tacn:`classical_right` to prove the right part of the disjunction with
   the assumption that the negation of left part holds.

.. _tactics-automating:

Automating
------------


.. tacn:: btauto
   :name: btauto

   The tactic :tacn:`btauto` implements a reflexive solver for boolean
   tautologies. It solves goals of the form :g:`t = u` where `t` and `u` are
   constructed over the following grammar:

   .. _btauto_grammar:

   .. productionlist:: `sentence`
      t : x
        :∣ true
        :∣ false
        :∣ orb t1 t2
        :∣ andb t1 t2
        :∣ xorb t1 t2
        :∣ negb t
        :∣ if t1 then t2 else t3

   Whenever the formula supplied is not a tautology, it also provides a
   counter-example.

   Internally, it uses a system very similar to the one of the ring
   tactic.

   Note that this tactic is only available after a ``Require Import Btauto``.

   .. exn:: Cannot recognize a boolean equality.

      The goal is not of the form :g:`t = u`. Especially note that :tacn:`btauto`
      doesn't introduce variables into the context on its own.

.. tacn:: omega
   :name: omega

   The tactic :tacn:`omega`, due to Pierre Crégut, is an automatic decision
   procedure for Presburger arithmetic. It solves quantifier-free
   formulas built with `~`, `\/`, `/\`, `->` on top of equalities,
   inequalities and disequalities on both the type :g:`nat` of natural numbers
   and :g:`Z` of binary integers. This tactic must be loaded by the command
   ``Require Import Omega``. See the additional documentation about omega
   (see Chapter :ref:`omega`).


.. tacn:: ring
   :name: ring

   This tactic solves equations upon polynomial expressions of a ring
   (or semiring) structure. It proceeds by normalizing both hand sides
   of the equation (w.r.t. associativity, commutativity and
   distributivity, constant propagation) and comparing syntactically the
   results.

.. tacn:: ring_simplify {+ @term}
   :name: ring_simplify

   This tactic applies the normalization procedure described above to
   the given terms. The tactic then replaces all occurrences of the terms
   given in the conclusion of the goal by their normal forms. If no term
   is given, then the conclusion should be an equation and both hand
   sides are normalized.

See :ref:`Theringandfieldtacticfamilies` for more information on
the tactic and how to declare new ring structures. All declared field structures
can be printed with the ``Print Rings`` command.

.. tacn:: field
          field_simplify {+ @term}
          field_simplify_eq
   :name: field; field_simplify; field_simplify_eq

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

   File plugins/setoid_ring/RealField.v for an example of instantiation,
   theory theories/Reals for many examples of use of field.

Non-logical tactics
------------------------


.. tacn:: cycle @num
   :name: cycle

   This tactic puts the :n:`@num` first goals at the end of the list of goals.
   If :n:`@num` is negative, it will put the last :math:`|num|` goals at the
   beginning of the list.

.. example::

   .. coqtop:: all reset

      Parameter P : nat -> Prop.
      Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
      repeat split.
      all: cycle 2.
      all: cycle -3.

.. tacn:: swap @num @num
   :name: swap

   This tactic switches the position of the goals of indices :n:`@num` and
   :n:`@num`. If either :n:`@num` or :n:`@num` is negative then goals are
   counted from the end of the focused goal list. Goals are indexed from 1,
   there is no goal with position 0.

.. example::

   .. coqtop:: reset all

      Parameter P : nat -> Prop.
      Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
      repeat split.
      all: swap 1 3.
      all: swap 1 -1.

.. tacn:: revgoals
   :name: revgoals

   This tactics reverses the list of the focused goals.

   .. example::

      .. coqtop:: all reset

         Parameter P : nat -> Prop.
         Goal P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5.
         repeat split.
         all: revgoals.

.. tacn:: shelve
   :name: shelve

   This tactic moves all goals under focus to a shelf. While on the
   shelf, goals will not be focused on. They can be solved by
   unification, or they can be called back into focus with the command
   :cmd:`Unshelve`.

   .. tacv:: shelve_unifiable
      :name: shelve_unifiable

      Shelves only the goals under focus that are mentioned in other goals.
      Goals that appear in the type of other goals can be solved by unification.

      .. example::

         .. coqtop:: all reset

            Goal exists n, n=0.
            refine (ex_intro _ _ _).
            all: shelve_unifiable.
            reflexivity.

.. cmd:: Unshelve

   This command moves all the goals on the shelf (see :tacn:`shelve`)
   from the shelf into focus, by appending them to the end of the current
   list of focused goals.

.. tacn:: give_up
   :name: give_up

   This tactic removes the focused goals from the proof. They are not
   solved, and cannot be solved later in the proof. As the goals are not
   solved, the proof cannot be closed.

   The ``give_up`` tactic can be used while editing a proof, to choose to
   write the proof script in a non-sequential order.

Simple tactic macros
-------------------------

A simple example has more value than a long explanation:

.. example::

   .. coqtop:: reset all

      Ltac Solve := simpl; intros; auto.

      Ltac ElimBoolRewrite b H1 H2 :=
      elim b; [ intros; rewrite H1; eauto | intros; rewrite H2; eauto ].

The tactics macros are synchronous with the Coq section mechanism: a
tactic definition is deleted from the current environment when you
close the section (see also :ref:`section-mechanism`) where it was
defined. If you want that a tactic macro defined in a module is usable in the
modules that require it, you should put it outside of any section.

:ref:`ltac` gives examples of more complex
user-defined tactics.

.. [1] Actually, only the second subgoal will be generated since the
  other one can be automatically checked.
.. [2] This corresponds to the cut rule of sequent calculus.
.. [3] Reminder: opaque constants will not be expanded by δ reductions.
.. [4] The behavior of this tactic has changed a lot compared to the
  versions available in the previous distributions (V6). This may cause
  significant changes in your theories to obtain the same result. As a
  drawback of the re-engineering of the code, this tactic has also been
  completely revised to get a very compact and readable version.
