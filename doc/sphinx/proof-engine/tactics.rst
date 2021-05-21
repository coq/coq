.. tacn:: constructor @natural
   :name: constructor

   This tactic applies to a goal such that its conclusion is an inductive
   type (say :g:`I`). The argument :token:`natural` must be less or equal to the
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

   .. tacv:: constructor @natural with @bindings

      Let ``c`` be the i-th constructor of :g:`I`, then
      :n:`constructor i with @bindings` is equivalent to
      :n:`intros; apply c with @bindings`.

      .. warning::

         The terms in :token:`bindings` are checked in the context
         where constructor is executed and not in the context where :tacn:`apply`
         is executed (the introductions are not taken into account).

   .. tacv:: split {? with @bindings }
      :name: split

      This applies only if :g:`I` has a single constructor. It is then
      equivalent to :n:`constructor 1 {? with @bindings }`. It is
      typically used in the case of a conjunction :math:`A \wedge B`.

      .. tacv:: exists @bindings
         :name: exists

         This applies only if :g:`I` has a single constructor. It is then equivalent
         to :n:`intros; constructor 1 with @bindings.` It is typically used in
         the case of an existential quantification :math:`\exists x, P(x).`

      .. tacv:: exists {+, @bindings }

         This iteratively applies :n:`exists @bindings`.

      .. exn:: Not an inductive goal with 1 constructor.
         :undocumented:

   .. tacv:: left {? with @bindings }
             right {? with @bindings }
      :name: left; right

      These tactics apply only if :g:`I` has two constructors, for
      instance in the case of a disjunction :math:`A \vee B`.
      Then, they are respectively equivalent to
      :n:`constructor 1 {? with @bindings }` and
      :n:`constructor 2 {? with @bindings }`.

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

:opt:`Debug` ``"tactic-unification"`` enables printing traces of
unification steps in tactic unification. Tactic unification is used in
tactics such as :tacn:`apply` and :tacn:`rewrite`.

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

   .. tacv:: intros until @natural

      This repeats :tacn:`intro` until the :token:`natural`\-th non-dependent
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

         This happens when :token:`natural` is 0 or is greater than the number of
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
      followed by the appropriate call to :tacn:`move`,
      :tacn:`move … before …`, :tacn:`move … at top`,
      or :tacn:`move … at bottom`.

      .. note::

         :n:`intro at bottom` is a synonym for :n:`intro` with no argument.

      .. exn:: No such hypothesis: @ident.
         :undocumented:

.. tacn:: intros @intropattern_list
   :name: intros …

   Introduces one or more variables or hypotheses from the goal by matching the
   intro patterns.  See the description in :ref:`intropatterns`.

.. tacn:: eintros @intropattern_list
   :name: eintros

   Works just like :tacn:`intros …` except that it creates existential variables
   for any unresolved variables rather than failing.

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
      :name: move … before …

      This moves :n:`@ident__1` towards and just before the hypothesis
      named :n:`@ident__2`.  As for :tacn:`move`, dependencies
      over :n:`@ident__1` (when :n:`@ident__1` comes before :n:`@ident__2` in
      the order of dependencies) or in the type of :n:`@ident__1`
      (when :n:`@ident__1` comes after :n:`@ident__2` in the order of
      dependencies) are moved too.

   .. tacv:: move @ident at top
      :name: move … at top

      This moves :token:`ident` at the top of the local context (at the beginning
      of the context).

   .. tacv:: move @ident at bottom
      :name: move … at bottom

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

   .. tacv:: set (@ident {* @binder } := @term) {? in @goal_occurrences }

      This is equivalent to :n:`set (@ident := fun {* @binder } => @term) {? in @goal_occurrences }`.

   .. tacv:: set @term {? in @goal_occurrences }

      This behaves as :n:`set (@ident := @term) {? in @goal_occurrences }`
      but :token:`ident` is generated by Coq.

   .. tacv:: eset (@ident {* @binder } := @term) {? in @goal_occurrences }
             eset @term {? in @goal_occurrences }
      :name: eset; _

      While the different variants of :tacn:`set` expect that no existential
      variables are generated by the tactic, :tacn:`eset` removes this
      constraint. In practice, this is relevant only when :tacn:`eset` is
      used as a synonym of :tacn:`epose`, i.e. when the :token:`term` does
      not occur in the goal.

.. tacn:: remember @term as @ident__1 {? eqn:@naming_intropattern }
   :name: remember

   This behaves as :n:`set (@ident := @term) in *`, using a logical
   (Leibniz’s) equality instead of a local definition.
   Use :n:`@naming_intropattern` to name or split up the new equation.

   .. tacv:: remember @term as @ident__1 {? eqn:@naming_intropattern } in @goal_occurrences

      This is a more general form of :tacn:`remember` that remembers the
      occurrences of :token:`term` specified by an occurrence set.

   .. tacv:: eremember @term as @ident__1 {? eqn:@naming_intropattern } {? in @goal_occurrences }
      :name: eremember

      While the different variants of :tacn:`remember` expect that no
      existential variables are generated by the tactic, :tacn:`eremember`
      removes this constraint.

.. tacn:: pose (@ident := @term)
   :name: pose

   This adds the local definition :n:`@ident := @term` to the current context
   without performing any replacement in the goal or in the hypotheses. It is
   equivalent to :n:`set (@ident := @term) in |-`.

   .. tacv:: pose (@ident {* @binder } := @term)

      This is equivalent to :n:`pose (@ident := fun {* @binder } => @term)`.

   .. tacv:: pose @term

      This behaves as :n:`pose (@ident := @term)` but :token:`ident` is
      generated by Coq.

   .. tacv:: epose (@ident {* @binder } := @term)
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

   .. tacv:: assert @type as @simple_intropattern

      If :n:`simple_intropattern` is an intro pattern (see :ref:`intropatterns`),
      the hypothesis is named after this introduction pattern (in particular, if
      :n:`simple_intropattern` is :n:`@ident`, the tactic behaves like
      :n:`assert (@ident : @type)`). If :n:`simple_intropattern` is an action
      introduction pattern, the tactic behaves like :n:`assert @type` followed by
      the action done by this introduction pattern.

   .. tacv:: assert @type as @simple_intropattern by @tactic

      This combines the two previous variants of :tacn:`assert`.

   .. tacv:: assert (@ident := @term)

      This behaves as :n:`assert (@ident : @type) by exact @term` where
      :token:`type` is the type of :token:`term`. This is equivalent to using
      :tacn:`pose proof`. If the head of term is :token:`ident`, the tactic
      behaves as :tacn:`specialize`.

      .. exn:: Variable @ident is already declared.
         :undocumented:

.. tacv:: eassert @type as @simple_intropattern by @tactic
   :name: eassert

   While the different variants of :tacn:`assert` expect that no existential
   variables are generated by the tactic, :tacn:`eassert` removes this constraint.
   This lets you avoid specifying the asserted statement completely before starting
   to prove it.

.. tacv:: pose proof @term {? as @simple_intropattern}
   :name: pose proof

   This tactic behaves like :n:`assert @type {? as @simple_intropattern} by exact @term`
   where :token:`type` is the type of :token:`term`. In particular,
   :n:`pose proof @term as @ident` behaves as :n:`assert (@ident := @term)`
   and :n:`pose proof @term as @simple_intropattern` is the same as applying the
   :token:`simple_intropattern` to :token:`term`.

.. tacv:: epose proof @term {? as @simple_intropattern}
   :name: epose proof

   While :tacn:`pose proof` expects that no existential variables are generated by
   the tactic, :tacn:`epose proof` removes this constraint.

.. tacv:: pose proof (@ident := @term)

   This is an alternative syntax for :n:`assert (@ident := @term)` and
   :n:`pose proof @term as @ident`, following the model of :n:`pose
   (@ident := @term)` but dropping the value of :token:`ident`.

.. tacv:: epose proof (@ident := @term)

   This is an alternative syntax for :n:`eassert (@ident := @term)`
   and :n:`epose proof @term as @ident`, following the model of
   :n:`epose (@ident := @term)` but dropping the value of
   :token:`ident`.

.. tacv:: enough (@ident : @type)
   :name: enough

   This adds a new hypothesis of name :token:`ident` asserting :token:`type` to the
   goal the tactic :tacn:`enough` is applied to. A new subgoal stating :token:`type` is
   inserted after the initial goal rather than before it as :tacn:`assert` would do.

.. tacv:: enough @type

   This behaves like :n:`enough (@ident : @type)` with the name :token:`ident` of
   the hypothesis generated by Coq.

.. tacv:: enough @type as @simple_intropattern

   This behaves like :n:`enough @type` using :token:`simple_intropattern` to name or
   destruct the new hypothesis.

.. tacv:: enough (@ident : @type) by @tactic
          enough @type {? as @simple_intropattern } by @tactic

   This behaves as above but with :token:`tactic` expected to solve the initial goal
   after the extra assumption :token:`type` is added and possibly destructed. If the
   :n:`as @simple_intropattern` clause generates more than one subgoal, :token:`tactic` is
   applied to all of them.

.. tacv:: eenough @type {? as @simple_intropattern } {? by @tactic }
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

.. tacv:: specialize (@ident {* @term}) {? as @simple_intropattern}
          specialize @ident with @bindings {? as @simple_intropattern}
   :name: specialize; _

   This tactic works on local hypothesis :n:`@ident`. The
   premises of this hypothesis (either universal quantifications or
   non-dependent implications) are instantiated by concrete terms coming either
   from arguments :n:`{* @term}` or from :ref:`bindings`.
   In the first form the application to :n:`{* @term}`  can be partial. The
   first form is equivalent to :n:`assert (@ident := @ident {* @term})`. In the
   second form, instantiation elements can also be partial. In this case the
   uninstantiated arguments are inferred by unification if possible or left
   quantified in the hypothesis otherwise. With the :n:`as` clause, the local
   hypothesis :n:`@ident` is left unchanged and instead, the modified hypothesis
   is introduced as specified by the :token:`simple_intropattern`. The name :n:`@ident`
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

.. tacv:: generalize @term at {+ @natural}

   This is equivalent to :n:`generalize @term` but it generalizes only over the
   specified occurrences of :n:`@term` (counting from left to right on the
   expression printed using the :flag:`Printing All` flag).

.. tacv:: generalize @term as @ident

   This is equivalent to :n:`generalize @term` but it uses :n:`@ident` to name
   the generalized hypothesis.

.. tacv:: generalize {+, @term at {+ @natural} as @ident}

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
   :n:`@ident` with the term :n:`@term`. It is equivalent to
   :n:`only [ident]: refine @term` (preferred alternative).

   .. note:: To be able to refer to an existential variable by name, the user
             must have given the name explicitly (see :ref:`Existential-Variables`).

   .. note:: When you are referring to hypotheses which you did not name
             explicitly, be aware that Coq may make a different decision on how to
             name the variable in the current goal and in the context of the
             existential variable. This can lead to surprising behaviors.

.. tacv:: instantiate (@natural := @term)

   This variant selects an existential variable by its position.  The
   :n:`@natural` argument is the position of the existential variable
   *from right to left* in the conclusion of the goal.  (Use one of
   the variants below to select an existential variable in a
   hypothesis.)  Counting starts at 1 and multiple occurrences of the
   same existential variable are counted multiple times.  Because this
   variant is not robust to slight changes in the goal, its use is
   strongly discouraged.

.. tacv:: instantiate ( @natural := @term ) in @ident
          instantiate ( @natural := @term ) in ( value of @ident )
          instantiate ( @natural := @term ) in ( type of @ident )

   These allow to refer respectively to existential variables occurring in a
   hypothesis or in the body or the type of a local definition (named :n:`@ident`).

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

   .. tacv:: destruct @natural

      :n:`destruct @natural` behaves as :n:`intros until @natural`
      followed by destruct applied to the last introduced hypothesis.

     .. note::
        For destruction of a number, use syntax :n:`destruct (@natural)` (not
        very interesting anyway).

   .. tacv:: destruct @pattern

      The argument of :tacn:`destruct` can also be a pattern of which holes are
      denoted by “_”. In this case, the tactic checks that all subterms
      matching the pattern in the conclusion and the hypotheses are compatible
      and performs case analysis using this subterm.

   .. tacv:: destruct {+, @term}

      This is a shortcut for :n:`destruct @term; ...; destruct @term`.

   .. tacv:: destruct @term as @or_and_intropattern_loc

      This behaves as :n:`destruct @term` but uses the names
      in :token:`or_and_intropattern_loc` to name the variables introduced in the
      context. The :token:`or_and_intropattern_loc` must have the
      form :n:`[p11 ... p1n | ... | pm1 ... pmn ]` with ``m`` being the
      number of constructors of the type of :token:`term`. Each variable
      introduced by :tacn:`destruct` in the context of the ``i``-th goal
      gets its name from the list :n:`pi1 ... pin` in order. If there are not
      enough names, :tacn:`destruct` invents names for the remaining variables
      to introduce. More generally, the :n:`pij` can be any introduction
      pattern (see :tacn:`intros`). This provides a concise notation for
      chaining destruction of a hypothesis.

   .. tacv:: destruct @term eqn:@naming_intropattern
      :name: destruct … eqn:

      This behaves as :n:`destruct @term` but adds an equation
      between :token:`term` and the value that it takes in each of the
      possible cases. The name of the equation is specified
      by :token:`naming_intropattern` (see :tacn:`intros`),
      in particular ``?`` can be used to let Coq generate a fresh name.

   .. tacv:: destruct @term with @bindings

      This behaves like :n:`destruct @term` providing explicit instances for
      the dependent premises of the type of :token:`term`.

   .. tacv:: edestruct @term
      :name: edestruct

      This tactic behaves like :n:`destruct @term` except that it does not
      fail if the instance of a dependent premises of the type
      of :token:`term` is not inferable. Instead, the unresolved instances
      are left as existential variables to be inferred later, in the same way
      as :tacn:`eapply` does.

   .. tacv:: destruct @term using @term {? with @bindings }

      This is synonym of :n:`induction @term using @term {? with @bindings }`.

   .. tacv:: destruct @term in @goal_occurrences

      This syntax is used for selecting which occurrences of :token:`term`
      the case analysis has to be done on. The :n:`in @goal_occurrences`
      clause is an occurrence clause whose syntax and behavior is described
      in :ref:`occurrences sets <occurrencessets>`.

   .. tacv:: destruct @term {? with @bindings } {? as @or_and_intropattern_loc } {? eqn:@naming_intropattern } {? using @term {? with @bindings } } {? in @goal_occurrences }
             edestruct @term {? with @bindings } {? as @or_and_intropattern_loc } {? eqn:@naming_intropattern } {? using @term {? with @bindings } } {? in @goal_occurrences }

      These are the general forms of :tacn:`destruct` and :tacn:`edestruct`.
      They combine the effects of the ``with``, ``as``, ``eqn:``, ``using``,
      and ``in`` clauses.

.. tacn:: case @term
   :name: case

   The tactic :n:`case` is a more basic tactic to perform case analysis without
   recursion. It behaves as :n:`elim @term` but using a case-analysis
   elimination principle and not a recursive one.

.. tacv:: case @term with @bindings

   Analogous to :n:`elim @term with @bindings` above.

.. tacv:: ecase @term {? with @bindings }
   :name: ecase

   In case the type of :n:`@term` has dependent premises, or dependent premises
   whose values are not inferable from the :n:`with @bindings` clause,
   :n:`ecase` turns them into existential variables to be resolved later on.

.. tacv:: simple destruct @ident
   :name: simple destruct

   This tactic behaves as :n:`intros until @ident; case @ident` when :n:`@ident`
   is a quantified variable of the goal.

.. tacv:: simple destruct @natural

   This tactic behaves as :n:`intros until @natural; case @ident` where :n:`@ident`
   is the name given by :n:`intros until @natural` to the :n:`@natural` -th
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
   + If :n:`@term` is a :n:`@natural`, then :n:`induction @natural` behaves as
     :n:`intros until @natural` followed by :n:`induction` applied to the last
     introduced hypothesis.

     .. note::
        For simple induction on a number, use syntax induction (number)
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
      exact (le_n 0).

.. exn:: Not an inductive product.
   :undocumented:

.. exn:: Unable to find an instance for the variables @ident ... @ident.

   Use in this case the variant :tacn:`elim … with` below.

.. tacv:: induction @term as @or_and_intropattern_loc

   This behaves as :tacn:`induction` but uses the names in
   :n:`@or_and_intropattern_loc` to name the variables introduced in the
   context. The :n:`@or_and_intropattern_loc` must typically be of the form
   :n:`[ p` :sub:`11` :n:`... p` :sub:`1n` :n:`| ... | p`:sub:`m1` :n:`... p`:sub:`mn` :n:`]`
   with :n:`m` being the number of constructors of the type of :n:`@term`. Each
   variable introduced by induction in the context of the i-th goal gets its
   name from the list :n:`p`:sub:`i1` :n:`... p`:sub:`in` in order. If there are
   not enough names, induction invents names for the remaining variables to
   introduce. More generally, the :n:`p`:sub:`ij` can be any
   disjunctive/conjunctive introduction pattern (see :tacn:`intros …`). For
   instance, for an inductive type with  one constructor, the pattern notation
   :n:`(p`:sub:`1` :n:`, ... , p`:sub:`n` :n:`)` can be used instead of
   :n:`[ p`:sub:`1` :n:`... p`:sub:`n` :n:`]`.

.. tacv:: induction @term with @bindings

   This behaves like :tacn:`induction` providing explicit instances for the
   premises of the type of :n:`term` (see :ref:`bindings`).

.. tacv:: einduction @term
   :name: einduction

   This tactic behaves like :tacn:`induction` except that it does not fail if
   some dependent premise of the type of :n:`@term` is not inferable. Instead,
   the unresolved premises are posed as existential variables to be inferred
   later, in the same way as :tacn:`eapply` does.

.. tacv:: induction @term using @term
   :name: induction … using …

   This behaves as :tacn:`induction`  but using :n:`@term` as induction scheme.
   It does not expect the conclusion of the type of the first :n:`@term` to be
   inductive.

.. tacv:: induction @term using @term with @bindings

   This behaves as :tacn:`induction … using …` but also providing instances
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

.. tacv:: induction @term with @bindings as @or_and_intropattern_loc using @term with @bindings in @goal_occurrences
          einduction @term with @bindings as @or_and_intropattern_loc using @term with @bindings in @goal_occurrences

   These are the most general forms of :tacn:`induction` and :tacn:`einduction`. It combines the
   effects of the with, as, using, and in clauses.

.. tacv:: elim @term
   :name: elim

   This is a more basic induction tactic. Again, the type of the argument
   :n:`@term` must be an inductive type. Then, according to the type of the
   goal, the tactic ``elim`` chooses the appropriate destructor and applies it
   as the tactic :tacn:`apply` would do. For instance, if the local context
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

.. tacv:: elim @term with @bindings
   :name: elim … with

   Allows to give explicit instances to the premises of the type of :n:`@term`
   (see :ref:`bindings`).

.. tacv:: eelim @term
   :name: eelim

   In case the type of :n:`@term` has dependent premises, this turns them into
   existential variables to be resolved later on.

.. tacv:: elim @term using @term
          elim @term using @term with @bindings

   Allows the user to give explicitly an induction principle :n:`@term` that
   is not the standard one for the underlying inductive type of :n:`@term`. The
   :n:`@bindings` clause allows instantiating premises of the type of
   :n:`@term`.

.. tacv:: elim @term with @bindings using @term with @bindings
          eelim @term with @bindings using @term with @bindings

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

.. tacv:: simple induction @natural

   This tactic behaves as :n:`intros until @natural; elim @ident` where :n:`@ident`
   is the name given by :n:`intros until @natural` to the :n:`@natural`-th non-dependent
   premise of the goal.

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

      Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
      intros n H ; induction H.

   Here we did not get any information on the indexes to help fulfill
   this proof. The problem is that, when we use the ``induction`` tactic, we
   lose information on the hypothesis instance, notably that the second
   argument is 1 here. Dependent induction solves this problem by adding
   the corresponding equality to the context.

   .. coqtop:: reset all

      Require Import Coq.Program.Equality.
      Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
      intros n H ; dependent induction H.

   The subgoal is cleaned up as the tactic tries to automatically
   simplify the subgoals with respect to the generated equalities. In
   this enriched context, it becomes possible to solve this subgoal.

   .. coqtop:: all

      reflexivity.

   Now we are in a contradictory context and the proof can be solved.

   .. coqtop:: all abort

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

.. seealso:: :tacn:`functional induction`

.. tacn:: discriminate @term
   :name: discriminate

   This tactic proves any goal from an assumption stating that two
   structurally different :n:`@term`\s of an inductive set are equal. For
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

.. tacv:: discriminate @natural

   This does the same thing as :n:`intros until @natural` followed by
   :n:`discriminate @ident` where :n:`@ident` is the identifier for the last
   introduced hypothesis.

.. tacv:: discriminate @term with @bindings

   This does the same thing as :n:`discriminate @term` but using the given
   bindings to instantiate parameters or hypotheses of :n:`@term`.

.. tacv:: ediscriminate @natural
          ediscriminate @term {? with @bindings}
   :name: ediscriminate; _

   This works the same as :tacn:`discriminate` but if the type of :token:`term`, or the
   type of the hypothesis referred to by :token:`natural`, has uninstantiated
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
   equality has been declared using :cmd:`Scheme` :n:`Equality ...`
   (see :ref:`proofschemes-induction-principles`),
   the use of a sigma type is avoided.

   .. note::
      If some quantified hypothesis of the goal is named :n:`@ident`,
      then :n:`injection @ident` first introduces the hypothesis in the local
      context using :n:`intros until @ident`.

   .. exn:: Nothing to do, it is an equality between convertible terms.
      :undocumented:

   .. exn:: Not a primitive equality.
      :undocumented:

   .. exn:: Nothing to inject.

      This error is given when one side of the equality is not a constructor.

   .. tacv:: injection @natural

      This does the same thing as :n:`intros until @natural` followed by
      :n:`injection @ident` where :n:`@ident` is the identifier for the last
      introduced hypothesis.

   .. tacv:: injection @term with @bindings

      This does the same as :n:`injection @term` but using the given bindings to
      instantiate parameters or hypotheses of :n:`@term`.

   .. tacv:: einjection @natural
             einjection @term {? with @bindings}
      :name: einjection; _

      This works the same as :n:`injection` but if the type of :n:`@term`, or the
      type of the hypothesis referred to by :n:`@natural`, has uninstantiated
      parameters, these parameters are left as existential variables.

   .. tacv:: injection

      If the current goal is of the form :n:`@term <> @term` , this behaves as
      :n:`intro @ident; injection @ident`.

      .. exn:: goal does not satisfy the expected preconditions.
         :undocumented:

   .. tacv:: injection @term {? with @bindings} as {+ @simple_intropattern}
             injection @natural as {+ @simple_intropattern}
             injection as {+ @simple_intropattern}
             einjection @term {? with @bindings} as {+ @simple_intropattern}
             einjection @natural as {+ @simple_intropattern}
             einjection as {+ @simple_intropattern}

      These variants apply :n:`intros {+ @simple_intropattern}` after the call to
      :tacn:`injection` or :tacn:`einjection` so that all equalities generated are moved in
      the context of hypotheses. The number of :n:`@simple_intropattern` must not exceed
      the number of equalities newly generated. If it is smaller, fresh
      names are automatically generated to adjust the list of :n:`@simple_intropattern`
      to the number of new equalities. The original equality is erased if it
      corresponds to a hypothesis.

   .. tacv:: injection @term {? with @bindings} as @injection_intropattern
             injection @natural as @injection_intropattern
             injection as @injection_intropattern
             einjection @term {? with @bindings} as @injection_intropattern
             einjection @natural as @injection_intropattern
             einjection as @injection_intropattern

      These are equivalent to the previous variants but using instead the
      syntax :token:`injection_intropattern` which :tacn:`intros`
      uses. In particular :n:`as [= {+ @simple_intropattern}]` behaves
      the same as :n:`as {+ @simple_intropattern}`.

   .. flag:: Structural Injection

      This flag ensures that :n:`injection @term` erases the original hypothesis
      and leaves the generated equalities in the context rather than putting them
      as antecedents of the current goal, as if giving :n:`injection @term as`
      (with an empty list of names). This flag is off by default.

   .. flag:: Keep Proof Equalities

      By default, :tacn:`injection` only creates new equalities between :n:`@term`\s
      whose type is in sort :g:`Type` or :g:`Set`, thus implementing a special
      behavior for objects that are proofs of a statement in :g:`Prop`. This flag
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
   relate two proofs (i.e. equalities between :token:`term`\s whose type is in sort
   :g:`Prop`). This behavior can be turned off by using the
   :flag:`Keep Proof Equalities` setting.

.. tacv:: inversion @natural

   This does the same thing as :n:`intros until @natural` then :n:`inversion @ident`
   where :n:`@ident` is the identifier for the last introduced hypothesis.

.. tacv:: inversion_clear @ident
   :name: inversion_clear

   This behaves as :n:`inversion` and then erases :n:`@ident` from the context.

.. tacv:: inversion @ident as @or_and_intropattern_loc

   This generally behaves as inversion but using names in :n:`@or_and_intropattern_loc`
   for naming hypotheses. The :n:`@or_and_intropattern_loc` must have the form
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

.. tacv:: inversion @natural as @or_and_intropattern_loc

   This allows naming the hypotheses introduced by :n:`inversion @natural` in the
   context.

.. tacv:: inversion_clear @ident as @or_and_intropattern_loc

   This allows naming the hypotheses introduced by ``inversion_clear`` in the
   context. Notice that hypothesis names can be provided as if ``inversion``
   were called, even though the ``inversion_clear`` will eventually erase the
   hypotheses.

.. tacv:: inversion @ident in {+ @ident}

   Let :n:`{+ @ident}` be identifiers in the local context. This tactic behaves as
   generalizing :n:`{+ @ident}`, and then performing ``inversion``.

.. tacv:: inversion @ident as @or_and_intropattern_loc in {+ @ident}

   This allows naming the hypotheses introduced in the context by
   :n:`inversion @ident in {+ @ident}`.

.. tacv:: inversion_clear @ident in {+ @ident}

   Let :n:`{+ @ident}` be identifiers in the local context. This tactic behaves
   as generalizing :n:`{+ @ident}`, and then performing ``inversion_clear``.

.. tacv:: inversion_clear @ident as @or_and_intropattern_loc in {+ @ident}

   This allows naming the hypotheses introduced in the context by
   :n:`inversion_clear @ident in {+ @ident}`.

.. tacv:: dependent inversion @ident
   :name: dependent inversion

   That must be used when :n:`@ident` appears in the current goal. It acts like
   ``inversion`` and then substitutes :n:`@ident` for the corresponding
   :n:`@@term` in the goal.

.. tacv:: dependent inversion @ident as @or_and_intropattern_loc

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion @ident`.

.. tacv:: dependent inversion_clear @ident

   Like ``dependent inversion``, except that :n:`@ident` is cleared from the
   local context.

.. tacv:: dependent inversion_clear @ident as @or_and_intropattern_loc

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion_clear @ident`.

.. tacv:: dependent inversion @ident with @term
   :name: dependent inversion … with …

   This variant allows you to specify the generalization of the goal. It is
   useful when the system fails to generalize the goal automatically. If
   :n:`@ident` has type :g:`(I t)` and :g:`I` has type :g:`forall (x:T), s`,
   then :n:`@term` must be of type :g:`I:forall (x:T), I x -> s'` where
   :g:`s'` is the type of the goal.

.. tacv:: dependent inversion @ident as @or_and_intropattern_loc with @term

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion @ident with @term`.

.. tacv:: dependent inversion_clear @ident with @term

   Like :tacn:`dependent inversion … with …` with but clears :n:`@ident` from the
   local context.

.. tacv:: dependent inversion_clear @ident as @or_and_intropattern_loc with @term

   This allows naming the hypotheses introduced in the context by
   :n:`dependent inversion_clear @ident with @term`.

.. tacv:: simple inversion @ident
   :name: simple inversion

   It is a very primitive inversion tactic that derives all the necessary
   equalities but it does not simplify the constraints as ``inversion`` does.

.. tacv:: simple inversion @ident as @or_and_intropattern_loc

   This allows naming the hypotheses introduced in the context by
   ``simple inversion``.

.. tacn:: inversion @ident using @ident
   :name: inversion ... using ...

   .. todo using … instead of ... in the name above gives a Sphinx error, even though
      this works just find for :tacn:`move`

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

   Let us consider the relation :g:`Le` over natural numbers:

   .. coqtop:: reset in

      Inductive Le : nat -> nat -> Set :=
      | LeO : forall n:nat, Le 0 n
      | LeS : forall n m:nat, Le n m -> Le (S n) (S m).


   Let us consider the following goal:

   .. coqtop:: none

      Section Section.
      Variable P : nat -> nat -> Prop.
      Variable Q : forall n m:nat, Le n m -> Prop.
      Goal forall n m, Le (S n) m -> P n m.

   .. coqtop:: out

      intros.

   To prove the goal, we may need to reason by cases on :g:`H` and to derive
   that :g:`m` is necessarily of the form :g:`(S m0)` for certain :g:`m0` and that
   :g:`(Le n m0)`. Deriving these conditions corresponds to proving that the only
   possible constructor of :g:`(Le (S n) m)` is :g:`LeS` and that we can invert
   the arrow in the type of :g:`LeS`. This inversion is possible because :g:`Le`
   is the smallest set closed by the constructors :g:`LeO` and :g:`LeS`.

   .. coqtop:: all

      inversion_clear H.

   Note that :g:`m` has been substituted in the goal for :g:`(S m0)` and that the
   hypothesis :g:`(Le n m0)` has been added to the context.

   Sometimes it is interesting to have the equality :g:`m = (S m0)` in the
   context to use it after. In that case we can use :tacn:`inversion` that does
   not clear the equalities:

   .. coqtop:: none restart

      intros.

   .. coqtop:: all

      inversion H.

.. example::

   *Dependent inversion.*

   Let us consider the following goal:

   .. coqtop:: none

      Abort.
      Goal forall n m (H:Le (S n) m), Q (S n) m H.

   .. coqtop:: out

      intros.

   As :g:`H` occurs in the goal, we may want to reason by cases on its
   structure and so, we would like inversion tactics to substitute :g:`H` by
   the corresponding @term in constructor form. Neither :tacn:`inversion` nor
   :tacn:`inversion_clear` do such a substitution. To have such a behavior we
   use the dependent inversion tactics:

   .. coqtop:: all

      dependent inversion_clear H.

   Note that :g:`H` has been substituted by :g:`(LeS n m0 l)` and :g:`m` by :g:`(S m0)`.

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

.. seealso:: :tacn:`functional inversion`

.. tacn:: fix @ident @natural
   :name: fix

   This tactic is a primitive tactic to start a proof by induction. In
   general, it is easier to rely on higher-level induction tactics such
   as the ones described in :tacn:`induction`.

   In the syntax of the tactic, the identifier :n:`@ident` is the name given to
   the induction hypothesis. The natural number :n:`@natural` tells on which
   premise of the current goal the induction acts, starting from 1,
   counting both dependent and non dependent products, but skipping local
   definitions. Especially, the current lemma must be composed of at
   least :n:`@natural` products.

   Like in a fix expression, the induction hypotheses have to be used on
   structurally smaller arguments. The verification that inductive proof
   arguments are correct is done only at the time of registering the
   lemma in the global environment. To know if the use of induction hypotheses
   is correct at some time of the interactive development of a proof, use
   the command ``Guarded`` (see Section :ref:`requestinginformation`).

.. tacv:: fix @ident @natural with {+ (@ident {+ @binder} [{struct @ident}] : @type)}

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
   done only at the time of registering the lemma in the global environment. To
   know if the use of coinduction hypotheses is correct at some time of
   the interactive development of a proof, use the command ``Guarded``
   (see Section :ref:`requestinginformation`).

.. tacv:: cofix @ident with {+ (@ident {+ @binder} : @type)}

   This starts a proof by mutual coinduction. The statements to be
   simultaneously proved are respectively :g:`forall binder ... binder, type`
   The identifiers :n:`@ident` are the names of the coinduction hypotheses.


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
   the current local context.

.. exn:: Not a variable or hypothesis.
   :undocumented:

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

.. tacv:: simplify_eq @natural

   This does the same thing as :n:`intros until @natural` then
   :n:`simplify_eq @ident` where :n:`@ident` is the identifier for the last
   introduced hypothesis.

.. tacv:: simplify_eq @term with @bindings

   This does the same as :n:`simplify_eq @term` but using the given bindings to
   instantiate parameters or hypotheses of :n:`@term`.

.. tacv:: esimplify_eq @natural
          esimplify_eq @term {? with @bindings}
   :name: esimplify_eq; _

   This works the same as :tacn:`simplify_eq` but if the type of :n:`@term`, or the
   type of the hypothesis referred to by :n:`@natural`, has uninstantiated
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

Classical tactics
-----------------

In order to ease the proving process, when the ``Classical`` module is
loaded, a few more tactics are available. Make sure to load the module
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

Delaying solving unification constraints
----------------------------------------

.. tacn:: solve_constraints
   :name: solve_constraints
   :undocumented:

.. flag:: Solve Unification Constraints

   By default, after each tactic application, postponed typechecking unification
   problems are resolved using heuristics. Unsetting this flag disables this
   behavior, allowing tactics to leave unification constraints unsolved. Use the
   :tacn:`solve_constraints` tactic at any point to solve the constraints.

Proof maintenance
-----------------

*Experimental.*  Many tactics, such as :tacn:`intros`, can automatically generate names, such
as "H0" or "H1" for a new hypothesis introduced from a goal.  Subsequent proof steps
may explicitly refer to these names.  However, future versions of Coq may not assign
names exactly the same way, which could cause the proof to fail because the
new names don't match the explicit references in the proof.

The following "Mangle Names" settings let users find all the
places where proofs rely on automatically generated names, which can
then be named explicitly to avoid any incompatibility.  These
settings cause Coq to generate different names, producing errors for
references to automatically generated names.

.. flag:: Mangle Names

   When set, generated names use the prefix specified in the following
   option instead of the default prefix.

.. opt:: Mangle Names Prefix @string
   :name: Mangle Names Prefix

   Specifies the prefix to use when generating names.

Performance-oriented tactic variants
------------------------------------

.. todo: move the following adjacent to the `exact` tactic in the rewriting chapter?

.. tacn:: exact_no_check @term
   :name: exact_no_check

   For advanced usage. Similar to :tacn:`exact` :n:`@term`, but as an optimization,
   it skips checking that :n:`@term` has the goal's type, relying on the kernel
   check instead. See :tacn:`change_no_check` for more explanation.

   .. example::

      .. coqtop:: all abort

         Goal False.
           exact_no_check I.
         Fail Qed.

   .. tacv:: vm_cast_no_check @term
      :name: vm_cast_no_check

      For advanced usage. Similar to :tacn:`exact_no_check` :n:`@term`, but additionally
      instructs the kernel to use :tacn:`vm_compute` to compare the
      goal's type with the :n:`@term`'s type.

      .. example::

        .. coqtop:: all abort

            Goal False.
              vm_cast_no_check I.
            Fail Qed.

   .. tacv:: native_cast_no_check @term
      :name: native_cast_no_check

      for advanced usage. similar to :tacn:`exact_no_check` :n:`@term`, but additionally
      instructs the kernel to use :tacn:`native_compute` to compare the goal's
      type with the :n:`@term`'s type.

      .. example::

        .. coqtop:: all abort

            Goal False.
              native_cast_no_check I.
            Fail Qed.

.. [1] Actually, only the second subgoal will be generated since the
  other one can be automatically checked.
.. [2] This corresponds to the cut rule of sequent calculus.
.. [3] Reminder: opaque constants will not be expanded by δ reductions.
