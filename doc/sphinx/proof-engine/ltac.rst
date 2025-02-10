.. _ltac:

Ltac
====

.. note::

   Writing automation using Ltac is discouraged.
   Many alternatives are available as part of the Rocq standard library
   or the `Coq Platform <https://github.com/coq/platform>`_, and some
   demonstration of their respective power is performed in the
   `metaprogramming Rosetta stone project <https://github.com/coq-community/metaprogramming-rosetta-stone>`_.
   The official alternative to Ltac is :ref:`ltac2`.
   While Ltac is not going away anytime soon, we would like to strongly
   encourage users to use Ltac2 (or other alternatives) instead of Ltac
   for new projects and new automation code in existing projects.
   Reports about hindrances in using Ltac2 for writing automation are
   welcome as issues on the `Rocq bug tracker <https://github.com/coq/coq/issues>`_
   or as discussions on the `Ltac2 Zulip stream <https://coq.zulipchat.com/#narrow/stream/278935-Ltac2>`_.

This chapter documents the tactic language |Ltac|.

We start by giving the syntax followed by the informal
semantics. To learn more about the language and
especially about its foundations, please refer to :cite:`Del00`.
(Note the examples in the paper won't work as-is; Rocq has evolved
since the paper was written.)

.. example:: Basic tactic macros

   Here are some examples of simple tactic macros you can create with |Ltac|:

   .. rocqdoc::

      Ltac reduce_and_try_to_solve := simpl; intros; auto.

      Ltac destruct_bool_and_rewrite b H1 H2 :=
        destruct b; [ rewrite H1; eauto | rewrite H2; eauto ].

   See Section :ref:`ltac-examples` for more advanced examples.

.. _ltac_defects:

Defects
-------

The |Ltac| tactic language is probably one of the ingredients of the success of
Rocq, yet it is at the same time its Achilles' heel. Indeed, |Ltac|:

- has often unclear semantics
- is very non-uniform due to organic growth
- lacks expressivity (data structures, combinators, types, ...)
- is slow
- is error-prone and fragile
- has an intricate implementation

Following the need of users who are developing huge projects relying
critically on Ltac, we believe that we should offer a proper modern language
that features at least the following:

- at least informal, predictable semantics
- a type system
- standard programming facilities (e.g., datatypes)

This new language, called Ltac2, is described in the :ref:`ltac2`
chapter. We encourage users to start testing it, especially wherever
an advanced tactic language is needed.

.. _ltac-syntax:

Syntax
------

The syntax of the tactic language is given below.

The main entry of the grammar is :n:`@ltac_expr`, which is used in proof mode
as well as to define new tactics with the :cmd:`Ltac` command.

The grammar uses multiple :n:`ltac_expr*` nonterminals to express how subexpressions
are grouped when they're not fully parenthesized.  For example, in many programming
languages, `a*b+c` is interpreted as `(a*b)+c` because `*` has
higher precedence than `+`.  Usually `a/b/c` is given the :gdef:`left associative`
interpretation `(a/b)/c` rather than the :gdef:`right associative` interpretation
`a/(b/c)`.

In Rocq, the expression :n:`try repeat @tactic__1 || @tactic__2; @tactic__3; @tactic__4`
is interpreted as :n:`(try (repeat (@tactic__1 || @tactic__2)); @tactic__3); @tactic__4`
because `||` is part of :token:`ltac_expr2`, which has higher precedence than
:tacn:`try` and :tacn:`repeat` (at the level of :token:`ltac_expr3`), which
in turn have higher precedence than `;`, which is part of :token:`ltac_expr4`.
(A *lower* number in the nonterminal name means *higher* precedence in this grammar.)

The constructs in :token:`ltac_expr` are :term:`left associative`.

.. insertprodn ltac_expr tactic_atom

.. prodn::
   ltac_expr ::= @ltac_expr4
   ltac_expr4 ::= @ltac_expr3 ; @ltac_expr3
   | @ltac_expr3 ; [ @for_each_goal ]
   | @ltac_expr3
   ltac_expr3 ::= @l3_tactic
   | @ltac_expr2
   ltac_expr2 ::= @ltac_expr1 + @ltac_expr2
   | @ltac_expr1 %|| @ltac_expr2
   | @l2_tactic
   | @ltac_expr1
   ltac_expr1 ::= @tactic_value
   | @qualid {+ @tactic_arg }
   | @l1_tactic
   | @ltac_expr0
   tactic_value ::= {| @value_tactic | @syn_value }
   tactic_arg ::= @tactic_value
   | @term
   | ()
   ltac_expr0 ::= ( @ltac_expr )
   | [> @for_each_goal ]
   | @tactic_atom
   tactic_atom ::= @integer
   | @qualid
   | ()

.. todo For the moment, I've left the language constructs like +, || and ; unchanged in the grammar.
   Not sure what to do with them.  If we just make these indirections I think the grammar no longer
   gives you an overall idea of the concrete grammar without following the hyperlinks for many terms--not so easy
   (e.g. I have a construct and I want to figure out which productions generate it so I can read about them).
   We should think about eventually having a cheat sheet for the constructs, perhaps as part of the
   chapter introduction (use case: I know there's a construct but I can't remember its syntax).  They
   do show up in the index but they're not so easy to find.  I had thought a little about putting
   an ltac expression cheat sheet at the top of the tactics index.  Unconventional, but people would
   see it and remember how to find it.

   OTOH, as you rightly note, they are not really tactics.  Looking for better ideas that we are OK with.

.. note::

   Tactics described in other chapters of the documentation are :production:`simple_tactic`\s,
   which only modify the proof state.  |Ltac| provides additional constructs that can generally
   be used wherever a :token:`simple_tactic` can appear, even though they don't modify the proof
   state and that syntactically they're at
   varying levels in :token:`ltac_expr`.  For simplicity of presentation, the |Ltac| constructs
   are documented as tactics.  Tactics are grouped as follows:

   - :production:`l3_tactic`\s include |Ltac| tactics: :tacn:`try`,
     :tacn:`do`, :tacn:`repeat`, :tacn:`timeout`, :tacn:`time`, :tacn:`progress`, :tacn:`once`,
     :tacn:`exactly_once`, :tacn:`only` and :tacn:`abstract`
   - :production:`l2_tactic`\s are: :tacn:`tryif`
   - :production:`l1_tactic`\s are: :tacn:`fun` and :tacn:`let`,
     the :token:`simple_tactic`\s, :tacn:`first`, :tacn:`solve`,
     :tacn:`idtac`, :tacn:`fail` and
     :tacn:`gfail` as well as :tacn:`match`, :tacn:`match goal` and their :n:`lazymatch` and
     :n:`multimatch` variants.
   - :production:`value_tactic`\s, which return values rather than change the proof state.
     They are: :tacn:`eval`, :tacn:`context`, :tacn:`numgoals`, :tacn:`fresh`, :tacn:`type of`
     and :tacn:`type_term`.

   The documentation for these |Ltac| constructs mentions which group they belong to.

   The difference is only relevant in some compound tactics where
   extra parentheses may be needed.  For example, parentheses are required in
   :n:`idtac + (once idtac)` because :tacn:`once` is an :token:`l3_tactic`, which the
   production :n:`@ltac_expr2 ::= @ltac_expr1 + @ltac_expr2` doesn't
   accept after the `+`.

.. note::

   - The grammar reserves the token ``||``.

.. todo For the compound tactics, review all the descriptions of evaluation vs application,
   backtracking, etc. to get the language consistent and simple (refactoring so the common
   elements are described in one place)

Values
------

An |Ltac| value can be an integer, string, unit (written as "`()`" ), syntactic value
or tactic.
Syntactic values correspond to certain nonterminal symbols in the grammar,
each of which is a distinct type of value.
Most commonly, the value of an |Ltac| expression is a tactic that can be executed.

While there are a number of constructs that let you combine multiple tactics into
compound tactics, there are no operations for combining most other types of values.
For example, there's no function to add two integers.  Syntactic values are entered
with the :token:`syn_value` construct.  Values of all types can be assigned to toplevel
symbols with the :cmd:`Ltac` command or to local symbols with the :tacn:`let` tactic.
|Ltac| :tacn:`functions<fun>` can return values of any type.

Syntactic values
~~~~~~~~~~~~~~~~

.. insertprodn syn_value syn_value

.. prodn::
   syn_value ::= @ident : ( @nonterminal )

Provides a way to use the syntax and semantics of a grammar nonterminal as a
value in an :token:`ltac_expr`.  The table below describes the most useful of
these.  You can see the others by running ":cmd:`Print Grammar` `tactic`" and
examining the part at the end under "Entry tactic:tactic_value".

   :token:`ident`
      name of a grammar nonterminal listed in the table

   :production:`nonterminal`
      represents syntax described by :token:`nonterminal`.

   .. list-table::
      :header-rows: 1

      * -  Specified :token:`ident`
        - Parsed as
        - Interpreted as
        - as in tactic

      * - ``ident``
        - :token:`ident`
        - a user-specified name
        - :tacn:`intro`

      * - ``string``
        - :token:`string`
        - a string
        -

      * - ``integer``
        - :token:`integer`
        - an integer
        -

      * - ``reference``
        - :token:`qualid`
        - a qualified identifier
        -

      * - ``uconstr``
        - :token:`term`
        - an untyped term
        - :tacn:`refine`

      * - ``constr``
        - :token:`term`
        - a term
        - :tacn:`exact`

      * - ``ltac``
        - :token:`ltac_expr`
        - a tactic
        -

:n:`ltac:(@ltac_expr)` can be used to indicate that the parenthesized item
should be interpreted as a tactic and not as a term.  The constructs can also
be used to pass parameters to tactics written in OCaml.  (While all
of the :token:`syn_value`\s can appear at the beginning of an :token:`ltac_expr`,
the others are not useful because they will not evaluate to tactics.)

:n:`uconstr:(@term)` can be used to build untyped terms.
Terms built in |Ltac| are well-typed by default.  Building large
terms in recursive |Ltac| functions may give very slow behavior because
terms must be fully type checked at each step.  In this case, using
an untyped term may avoid most of the repetitive type checking for the term,
improving performance.

.. todo above: maybe elaborate on "well-typed by default"
   see https://github.com/coq/coq/pull/12103#discussion_r436317558

Untyped terms built using :n:`uconstr:(…)` can be used as arguments to the
:tacn:`refine` tactic, for example. In that case the untyped term is type
checked against the conclusion of the goal, and the holes which are not solved
by the typing procedure are turned into new subgoals.

Substitution
~~~~~~~~~~~~

.. todo next paragraph: we need a better discussion of substitution.
   Looks like that also applies to binder_tactics in some form.
   See https://github.com/coq/coq/pull/12103#discussion_r422105218

:token:`name`\s within |Ltac| expressions are used to represent both terms and
|Ltac| variables.  If the :token:`name` corresponds to
an |Ltac| variable or tactic name, |Ltac| substitutes the value before applying
the expression.  Generally it's best to choose distinctive names for |Ltac| variables
that won't clash with term names.  You can use :n:`ltac:(@name)` or :n:`(@name)`
to control whether a :token:`name` is interpreted as, respectively, an |Ltac|
variable or a term.

Note that values from toplevel symbols, unlike locally-defined symbols, are
substituted only when they appear at the beginning of an :token:`ltac_expr` or
as a :token:`tactic_arg`.  Local symbols are also substituted into tactics:

.. example:: Substitution of global and local symbols

   .. rocqtop:: reset none

      Goal True.

   .. rocqtop:: all

      Ltac n := 1.
      let n2 := n in idtac n2.
      Fail idtac n.

Local definitions: let
~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: let {? rec } @let_clause {* with @let_clause } in @ltac_expr

   .. insertprodn let_clause let_clause

   .. prodn::
      let_clause ::= @name := @ltac_expr
      | @ident {+ @name } := @ltac_expr

   Binds symbols within :token:`ltac_expr`.  :tacn:`let` evaluates each :n:`@let_clause`, substitutes
   the bound variables into :n:`@ltac_expr` and then evaluates :n:`@ltac_expr`.  There are
   no dependencies between the :n:`@let_clause`\s.

   Use :tacn:`let` `rec` to create recursive or mutually recursive bindings, which
   causes the definitions to be evaluated lazily.

   :tacn:`let` is a :token:`l1_tactic`.

Function construction and application
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A parameterized tactic can be built anonymously (without resorting to
local definitions) with:

.. tacn:: fun {+ @name } => @ltac_expr

   Indeed, local definitions of functions are syntactic sugar for binding
   a :n:`fun` tactic to an identifier.

   :tacn:`fun` is a :token:`l1_tactic`.

Functions can return values of any type.

A function application is an expression of the form:

.. tacn:: @qualid {+ @tactic_arg }

   :n:`@qualid` must be bound to a |Ltac| function
   with at least as many arguments as the provided :n:`@tactic_arg`\s.
   The :n:`@tactic_arg`\s are evaluated before the function is applied
   or partially applied.

   Functions may be defined with the :tacn:`fun` and :tacn:`let` tactics
   and with the :cmd:`Ltac` command.

   .. todo above: note "gobble" corner case
      https://github.com/coq/coq/pull/12103#discussion_r436414417

Tactics in terms
~~~~~~~~~~~~~~~~

.. insertprodn term_ltac term_ltac

.. prodn::
   term_ltac ::= ltac : ( @ltac_expr )

Allows including an :token:`ltac_expr` within a term.  Semantically,
it's the same as the :token:`syn_value` for `ltac`, but these are
distinct in the grammar.

.. _goal-selectors:

Goal selectors
--------------

.. todo: mention this applies to Print commands and the Info command

By default, tactic expressions are applied only to the first goal.  Goal
selectors provide a way to apply a tactic expression to another goal or multiple
goals.  (The :opt:`Default Goal Selector` option can be used to change the default
behavior.)

.. tacn:: @toplevel_selector : @ltac_expr
   :name: … : … (goal selector)

   .. insertprodn toplevel_selector toplevel_selector

   .. prodn::
      toplevel_selector ::= @goal_selector
      | all
      | !
      | par

   Reorders the goals and applies :token:`ltac_expr` to the selected goals.  It can
   only be used at the top level of a tactic expression; it cannot be used within a
   tactic expression.  The selected goals are reordered so they appear after the
   lowest-numbered selected goal, ordered by goal number.  :ref:`Example
   <reordering_goals_ex>`.  If the selector applies
   to a single goal or to all goals, the reordering will not be apparent.  The order of
   the goals in the :token:`goal_selector` is irrelevant.  (This may not be what you expect;
   see `#8481 <https://github.com/coq/coq/issues/8481>`_.)

   .. todo why shouldn't "all" and "!" be accepted anywhere a @goal_selector is accepted?
      It would be simpler to explain.

   `all`
      Selects all focused goals.

   `!`
      If exactly one goal is in focus, apply :token:`ltac_expr` to it.
      Otherwise the tactic fails.

   `par`
      Applies :n:`@ltac_expr` to all focused goals in parallel.
      The number of workers can be controlled via the command line option
      :n:`-async-proofs-tac-j @natural` to specify the desired number of workers.
      In the special case where :n:`@natural` is 0, this completely prevents
      Rocq from spawning any new process, and `par` blocks are treated as a
      variant of `all` that additionally checks that each subgoal is solved.
      Limitations: ``par:`` only works on goals that don't contain existential
      variables.  :n:`@ltac_expr` must either solve the goal completely or do
      nothing (i.e. it cannot make some progress).

Selectors can also be used nested within a tactic expression with the
:tacn:`only` tactic:

.. tacn:: only @goal_selector : @ltac_expr3

   .. insertprodn goal_selector range_selector

   .. prodn::
      goal_selector ::= {+, @range_selector }
      | [ @ident ]
      range_selector ::= @natural
      | @natural - @natural

   Applies :token:`ltac_expr3` to the selected goals.  (At the beginning of a
   sentence, use the form :n:`@goal_selector: @tactic` rather than :n:`only @goal_selector: @tactic`.
   In the latter, the :opt:`Default Goal Selector` (by default set to :n:`1:`)
   is applied before :n:`only` is interpreted.  This is probably not what you
   want.)

   :tacn:`only` is an :token:`l3_tactic`.

   :n:`{+, @range_selector }`
      The selected goals are the union of the specified :token:`range_selector`\s.

   :n:`[ @ident ]`
      Limits the application of :token:`ltac_expr3` to the goal previously named
      :token:`ident` by the user (see :ref:`existential-variables`).  This works
      even when the goal is not in focus.

   :n:`@natural`
      Selects a single goal.

   :n:`@natural__1 - @natural__2`
      Selects the goals :n:`@natural__1` through :n:`@natural__2`, inclusive.

.. exn:: No such goal.
   :name: No such goal. (Goal selector)
   :undocumented:

.. _reordering_goals_ex:

.. example:: Selector reordering goals

   .. rocqtop:: reset in

      Goal 1=0 /\ 2=0 /\ 3=0.

   .. rocqtop:: all

      repeat split.
      1,3: idtac.

.. TODO change error message index entry

Processing multiple goals
-------------------------

When presented with multiple focused goals, most |Ltac| constructs process each goal
separately.  They succeed only if there is a success for each goal.  For example:

.. example:: Multiple focused goals

   This tactic fails because there no match for the second goal (`False`).

   .. rocqtop:: reset none fail

      Goal True /\ False.

   .. rocqtop:: out

      split.

   .. rocqtop:: all

      Fail all: let n := numgoals in idtac "numgoals =" n;
      match goal with
      | |- True => idtac
      end.

.. _branching_and_backtracking:

Branching and backtracking
--------------------------

|Ltac| provides several :gdef:`branching` tactics that permit trying multiple alternative tactics
for a proof step.  For example, :tacn:`first`, which tries several alternatives and selects the first
that succeeds, or :tacn:`tryif`, which tests whether a given tactic would succeed or fail if it was
applied and then, depending on the result, applies one of two alternative tactics.  There
are also looping constructs :tacn:`do` and :tacn:`repeat`.  The order in which the subparts
of these tactics are evaluated is generally similar to
structured programming constructs in many languages.

The :tacn:`+<+ (backtracking branching)>`, :tacn:`multimatch` and :tacn:`multimatch goal` tactics
provide more complex capability.  Rather than applying a single successful
tactic, these tactics generate a series of successful tactic alternatives that are tried sequentially
when subsequent tactics outside these constructs fail.  For example:

   .. example:: Backtracking

      .. rocqtop:: all

         Fail multimatch True with
         | True => idtac "branch 1"
         | _ => idtac "branch 2"
         end ;
         idtac "branch A"; fail.

These constructs are evaluated using :gdef:`backtracking`.  Each  creates a
:gdef:`backtracking point`.  When a subsequent tactic fails, evaluation continues from the nearest
prior backtracking point with the next successful alternative and repeats the tactics after
the backtracking point.  When a backtracking point has
no more successful alternatives, evaluation continues from the next prior backtracking point.
If there are no more prior backtracking points, the overall tactic fails.

Thus, backtracking tactics can have multiple successes.  Non-backtracking constructs that appear
after a backtracking point are reprocessed after backtracking, as in the example
above, in which the :tacn:`;<ltac-seq>` construct is reprocessed after backtracking.  When a
backtracking construct is within
a non-backtracking construct, the latter uses the :gdef:`first success`.  Backtracking to
a point within a non-backtracking construct won't change the branch that was selected by the
non-backtracking construct.

The :tacn:`once` tactic stops further backtracking to backtracking points within that tactic.

Control flow
------------

Sequence: ;
~~~~~~~~~~~

A sequence is an expression of the following form:

.. tacn:: @ltac_expr3__1 ; @ltac_expr3__2
   :name: ltac-seq

   .. todo: can't use "… ; …" as the name because of the semicolon

   The expression :n:`@ltac_expr3__1` is evaluated to :n:`v__1`, which must be
   a tactic value. The tactic :n:`v__1` is applied to the current goals,
   possibly producing more goals. Then the right-hand side is evaluated to
   produce :n:`v__2`, which must be a tactic value. The tactic
   :n:`v__2` is applied to all the goals produced by the prior
   application. Sequence is associative.

   This construct uses backtracking: if :n:`@ltac_expr3__2` fails, Rocq will
   try each alternative success (if any) for :n:`@ltac_expr3__1`, retrying
   :n:`@ltac_expr3__2` for each until both tactics succeed or all alternatives
   have failed.  See :ref:`branching_and_backtracking`.

   .. todo I don't see the distinction between evaluating an ltac expression
      and applying it--how are they not the same thing?  If different, the
      "Semantics" section above should explain it.
      See https://github.com/coq/coq/pull/12103#discussion_r422210482

   .. note::

      - If you want :n:`@tactic__2; @tactic__3` to be fully applied to the first
        subgoal generated by :n:`@tactic__1` before applying it to the other
        subgoals, then you should write:

        - :n:`@tactic__1; [> @tactic__2; @tactic__3 .. ]` rather than

        - :n:`@tactic__1; (@tactic__2; @tactic__3)`.

Do loop
~~~~~~~

.. tacn:: do @nat_or_var @ltac_expr3

   The do loop repeats a tactic :token:`nat_or_var` times:

   :n:`@ltac_expr` is evaluated to ``v``, which must be a tactic value. This tactic
   value ``v`` is applied :token:`nat_or_var` times. If :token:`nat_or_var` > 1, after the
   first application of ``v``, ``v`` is applied, at least once, to the generated
   subgoals and so on. It fails if the application of ``v`` fails before :token:`nat_or_var`
   applications have been completed.

   :tacn:`do` is an :token:`l3_tactic`.

Repeat loop
~~~~~~~~~~~

.. tacn:: repeat @ltac_expr3

   The repeat loop repeats a tactic until it fails or doesn't change the proof context.

   :n:`@ltac_expr` is evaluated to ``v``. If ``v`` denotes a tactic, this tactic is
   applied to each focused goal independently. If the application succeeds, the
   tactic is applied recursively to all the generated subgoals until it eventually
   fails. The recursion stops in a subgoal when the tactic has failed *to make
   progress*. The tactic :tacn:`repeat` :n:`@ltac_expr` itself never fails.

   :tacn:`repeat` is an :token:`l3_tactic`.

Catching errors: try
~~~~~~~~~~~~~~~~~~~~

We can catch the tactic errors with:

.. tacn:: try @ltac_expr3

   :n:`@ltac_expr` is evaluated to ``v`` which must be a tactic value. The tactic
   value ``v`` is applied to each focused goal independently. If the application of
   ``v`` fails in a goal, it catches the error and leaves the goal unchanged. If the
   level of the exception is positive, then the exception is re-raised with its
   level decremented.

   :tacn:`try` is an :token:`l3_tactic`.

Conditional branching: tryif
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: tryif @ltac_expr__test then @ltac_expr__then else @ltac_expr2__else

   For each focused goal, independently: Evaluate and apply :n:`@ltac_expr__test`.
   If :n:`@ltac_expr__test` succeeds at least once, evaluate and apply :n:`@ltac_expr__then`
   to all the subgoals generated by :n:`@ltac_expr__test`.  Otherwise, evaluate and apply
   :n:`@ltac_expr2__else` to all the subgoals generated by :n:`@ltac_expr__test`.

   :tacn:`tryif` is an :token:`l2_tactic`.

   .. multigoal example - not sure it adds much
      Goal True /\ False.
      split; tryif
        match goal with
        | |- True => idtac "True"
        | |- False => idtac "False" end
      then idtac "then" else idtac "else".

Alternatives
------------

Branching with backtracking: +
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We can branch with backtracking with the following structure:

.. tacn:: @ltac_expr1 + @ltac_expr2
   :name: + (backtracking branching)

   Evaluates and applies :n:`@ltac_expr1` to each focused goal independently.  If it fails
   (i.e. there is no initial success), then evaluates and applies the right-hand side.  If the
   right-hand side fails, the construct fails.

   If :n:`ltac_expr1` has an initial success and a subsequent tactic (outside the `+` construct)
   fails, |Ltac| backtracks and selects the next success for :n:`ltac_expr1`.  If there are
   no more successes, then `+` similarly evaluates and applies (and backtracks in) the right-hand side.
   To prevent evaluation of further alternatives after an initial success for a tactic, use :tacn:`first` instead.

   `+` is left-associative.

   In all cases, :n:`(@ltac_expr__1 + @ltac_expr__2); @ltac_expr__3` is equivalent to
   :n:`(@ltac_expr__1; @ltac_expr__3) + (@ltac_expr__2; @ltac_expr__3)`.

   Additionally, in most cases, :n:`(@ltac_expr__1 + @ltac_expr__2) + @ltac_expr__3` is
   equivalent to :n:`@ltac_expr__1 + (@ltac_expr__2 + @ltac_expr__3)`.
   Here's an example where the behavior differs slightly:

      .. rocqtop:: reset none

         Goal True.

      .. rocqtop:: all

        Fail (fail 2 + idtac) + idtac.
        Fail fail 2 + (idtac + idtac).

   .. example:: Backtracking branching with +

      In the first tactic, `idtac "2"` is not executed.  In the second, the subsequent `fail` causes
      backtracking and the execution of `idtac "B"`.

      .. rocqtop:: reset none

         Goal True.

      .. rocqtop:: all

         idtac "1" + idtac "2".
         assert_fails ((idtac "A" + idtac "B"); fail).


Local application of tactics: [> ... ]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: [> @for_each_goal ]
   :name: [> … | … | … ] (dispatch)

   .. insertprodn for_each_goal goal_tactics

   .. prodn::
      for_each_goal ::= @goal_tactics
      | {? @goal_tactics %| } {? @ltac_expr } .. {? %| @goal_tactics }
      goal_tactics ::= {*| {? @ltac_expr } }

   Applies a different :n:`{? @ltac_expr }` to each of the focused goals.  In the first
   form of :token:`for_each_goal` (without `..`), the construct fails if the number of specified
   :n:`{? @ltac_expr }` is not the same as the number of focused goals.  Omitting an
   :n:`@ltac_expr` leaves the corresponding goal unchanged.

   In the second form (with :n:`{? @ltac_expr } ..`), the left and right :token:`goal_tactics`
   are applied respectively to a prefix or suffix of the list of focused goals.
   The :n:`{? @ltac_expr }` before the `..` is applied to any focused goals in the middle
   (possibly none) that are not covered by the :token:`goal_tactics`.  The number of
   :n:`{? @ltac_expr }` in the :token:`goal_tactics` must be no more than the number of
   focused goals.

   In particular:

   :n:`@goal_tactics | .. | @goal_tactics`
      The goals not covered by the two :token:`goal_tactics` are left unchanged.

   :n:`[> @ltac_expr .. ]`
      :n:`@ltac_expr` is applied independently to each of
      the goals, rather than globally. In particular, if there are no goals, the
      tactic is not run at all. A tactic which expects multiple goals, such as
      :tacn:`swap`, would act as if a single goal is focused.

   Note that :n:`@ltac_expr3 ; [ {*| @ltac_expr} ]` is a convenient idiom to
   process the goals generated by applying :n:`@ltac_expr3`.

.. tacn:: @ltac_expr3 ; [ @for_each_goal ]
   :name: [ … | … | … ] (dispatch)

   :n:`@ltac_expr3 ; [ ... ]` is equivalent to :n:`[> @ltac_expr3 ; [> ... ] .. ]`.

.. todo see discussion of [ ... ] in https://github.com/coq/coq/issues/12283

First tactic to succeed
~~~~~~~~~~~~~~~~~~~~~~~

In some cases backtracking may be too expensive.

.. tacn:: first [ {*| @ltac_expr } ]
          first @ident
   :name: first; _

   In the first form: for each focused goal, independently apply the first tactic
   (:token:`ltac_expr`) that succeeds.

   In the second form: :n:`@ident` represents a list
   of tactics passed to :n:`first` in a :cmd:`Tactic Notation` command (see example
   :ref:`here <taclist_in_first>`).

   :tacn:`first` is an :token:`l1_tactic`.

   .. exn:: No applicable tactic.
      :undocumented:

   Failures in tactics won't cause backtracking.
   (To allow backtracking, use the :tacn:`+<+ (backtracking branching)>`
   construct above instead.)

   If the :tacn:`first` contains a tactic that can backtrack, "success" means
   the first success of that tactic.  Consider the following:

   .. example:: Backtracking inside a non-backtracking construct

      .. rocqtop:: reset none

         Goal True.

      The :tacn:`fail` doesn't trigger the second :tacn:`idtac`:

      .. rocqtop:: all

         assert_fails (first [ idtac "1" | idtac "2" ]; fail).

      This backtracks within `(idtac "1A" + idtac "1B" + fail)` but
      :tacn:`first` won't consider the `idtac "2"` alternative:

      .. rocqtop:: all

       assert_fails (first [ (idtac "1A" + idtac "1B" + fail) | idtac "2" ]; fail).

.. _taclist_in_first:

   .. example:: Referring to a list of tactics in :cmd:`Tactic Notation`

      This works similarly for the :tacn:`solve` tactic.

    .. rocqtop:: reset all

       Tactic Notation "myfirst" "[" tactic_list_sep(tacl,"|") "]" := first tacl.
       Goal True.
       myfirst [ auto | apply I ].

Solving
~~~~~~~

.. tacn:: solve [ {*| @ltac_expr__i } ]
          solve @ident
   :name: solve; _

   In the first form: for each focused goal, independently apply the first tactic
   (:n:`@ltac_expr`) that solves the goal.

   In the second form: :n:`@ident` represents a list
   of tactics passed to :n:`solve` in a :cmd:`Tactic Notation` command (see example
   :ref:`here <taclist_in_first>`).

   If any of the goals are not solved, then the overall :tacn:`solve` fails.

   :tacn:`solve` is an :token:`l1_tactic`.

First tactic to make progress: ||
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Yet another way of branching without backtracking is the following
structure:

.. tacn:: @ltac_expr1 %|| @ltac_expr2
   :name: || (first tactic making progress)

   :n:`@ltac_expr1 || @ltac_expr2` is
   equivalent to :n:`first [ progress @ltac_expr1 | @ltac_expr2 ]`, except that
   if it fails, it fails like :n:`@ltac_expr2. `||` is left-associative.

   :n:`@ltac_expr`\s that don't evaluate to tactic values are ignored.  See the
   note at :tacn:`solve`.

Detecting progress
~~~~~~~~~~~~~~~~~~

We can check if a tactic made progress with:

.. tacn:: progress @ltac_expr3

   :n:`@ltac_expr` is evaluated to ``v`` which must be a tactic value. The tactic value ``v``
   is applied to each focused subgoal independently. If the application of ``v``
   to one of the focused subgoal produced subgoals equal to the initial
   goals (up to syntactical equality), then an error of level 0 is raised.

   :tacn:`progress` is an :token:`l3_tactic`.

   .. exn:: Failed to progress.
      :undocumented:

Success and failure
-------------------

Checking for success: assert_succeeds
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Rocq defines an |Ltac| tactic in `Init.Tactics` to check that a tactic has *at least one*
success:

.. tacn:: assert_succeeds @ltac_expr3

   If :n:`@ltac_expr3` has at least one success, the proof state is unchanged and
   no message is printed.  If :n:`@ltac_expr3` fails, the tactic fails with the same error.

Checking for failure: assert_fails
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Rocq defines an |Ltac| tactic in `Init.Tactics` to check that a tactic *fails*:

.. tacn:: assert_fails @ltac_expr3

   If :n:`@ltac_expr3` fails, the proof state is unchanged and no message is printed.
   If :n:`@ltac_expr3` unexpectedly has at least one success, the tactic performs
   a :tacn:`gfail` :n:`0`, printing the following message:

   .. exn:: Tactic failure: <tactic closure> succeeds.
      :undocumented:

   .. note:: :tacn:`assert_fails` and :tacn:`assert_succeeds` work as described when
      :token:`ltac_expr3` is a :token:`simple_tactic`.  In some more complex expressions,
      they may report an error from within :token:`ltac_expr3` when they shouldn't.
      This is due to the order in which parts of the :token:`ltac_expr3`
      are evaluated and executed.  For example:

      .. rocqtop:: reset none

         Goal True.

      .. rocqtop:: all fail

         assert_fails match True with _ => fail end.

      should not show any message.  The issue is that :tacn:`assert_fails` is an |Ltac|-defined
      tactic.  That makes it a function that's processed in the evaluation phase, causing
      the :tacn:`match` to find its first success earlier.  One workaround
      is to prefix :token:`ltac_expr3` with "`idtac;`".

      .. rocqtop:: all

         assert_fails (idtac; match True with _ => fail end).

      Alternatively, substituting the :tacn:`match` into the definition of :tacn:`assert_fails` works
      as expected:

      .. rocqtop:: all

         tryif (once match True with _ => fail end) then gfail 0 (* tac *) "succeeds" else idtac.

Failing
~~~~~~~

.. tacn:: {| fail | gfail } {? @nat_or_var } {* {| @ident | @string | @natural } }
   :name: fail; gfail

   :tacn:`fail` is the always-failing tactic: it does not solve any
   goal. It is useful for defining other tactics since it can be caught by
   :tacn:`try`, :tacn:`repeat`, :tacn:`match goal`, or the branching tacticals.

   :tacn:`gfail` fails even when used after :n:`;` and there are no goals left.
   Similarly, :tacn:`gfail` fails even when used after ``all:`` and there are no
   goals left.

   :tacn:`fail` and :tacn:`gfail` are :token:`l1_tactic`\s.


   See the example for a comparison of the two constructs.

   Note that if Rocq terms have to be
   printed as part of the failure, term construction always forces the
   tactic into the goals, meaning that if there are no goals when it is
   evaluated, a tactic call like :tacn:`let` :n:`x := H in` :tacn:`fail` `0 x` will succeed.

   :n:`@nat_or_var`
      The failure level. If no level is specified, it defaults to 0.
      The level is used by :tacn:`try`, :tacn:`repeat`, :tacn:`match goal` and the branching
      tacticals. If 0, it makes :tacn:`match goal` consider the next clause
      (backtracking). If nonzero, the current :tacn:`match goal` block, :tacn:`try`,
      :tacn:`repeat`, or branching command is aborted and the level is decremented. In
      the case of :n:`+`, a nonzero level skips the first backtrack point, even if
      the call to :tacn:`fail` :n:`@natural` is not enclosed in a :n:`+` construct,
      respecting the algebraic identity.

   :n:`{* {| @ident | @string | @natural } }`
      The given tokens are used for printing the failure message.  If :token:`ident`
      is an |Ltac| variable, its contents are printed; if not, it is an error.

   .. exn:: Tactic failure.
      :undocumented:

   .. exn:: Tactic failure (level @natural).
      :undocumented:

   .. exn:: No such goal.
      :name: No such goal. (fail)
      :undocumented:

   .. example::

      .. todo the example is too long; could show the Goal True. Proof. once and hide the Aborts
         to shorten it.  And add a line of text before each subexample.  Perhaps add some very short
         explanations/generalizations (e.g. gfail always fails; "tac; fail" succeeds but "fail." alone
         fails.

      .. rocqtop:: reset all fail

         Goal True.
         Proof. fail. Abort.

         Goal True.
         Proof. trivial; fail. Qed.

         Goal True.
         Proof. trivial. fail. Abort.

         Goal True.
         Proof. trivial. all: fail. Qed.

         Goal True.
         Proof. gfail. Abort.

         Goal True.
         Proof. trivial; gfail. Abort.

         Goal True.
         Proof. trivial. gfail. Abort.

         Goal True.
         Proof. trivial. all: gfail. Abort.

Soft cut: once
~~~~~~~~~~~~~~

.. todo Would like a different subsection title above.
   I have trouble distinguishing once and exactly_once.
   We need to explain backtracking somewhere.
   See https://github.com/coq/coq/pull/12103#discussion_r422360181

Another way of restricting backtracking is to restrict a tactic to a
single success:

.. tacn:: once @ltac_expr3

   :n:`@ltac_expr3` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied but only its first success is used. If ``v`` fails,
   :tacn:`once` :n:`@ltac_expr3` fails like ``v``. If ``v`` has at least one success,
   :tacn:`once` :n:`@ltac_expr3` succeeds once, but cannot produce more successes.

   :tacn:`once` is an :token:`l3_tactic`.

Checking for a single success: exactly_once
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Rocq provides an experimental way to check that a tactic has *exactly
one* success:

.. tacn:: exactly_once @ltac_expr3

   :n:`@ltac_expr3` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied if it has at most one success. If ``v`` fails,
   :tacn:`exactly_once` :n:`@ltac_expr3` fails like ``v``. If ``v`` has a exactly one success,
   :tacn:`exactly_once` :n:`@ltac_expr3` succeeds like ``v``. If ``v`` has two or more
   successes, :tacn:`exactly_once` :n:`@ltac_expr3` fails.

   :tacn:`exactly_once` is an :token:`l3_tactic`.

   .. warning::

      The experimental status of this tactic pertains to the fact if ``v``
      has side effects, they may occur in an unpredictable way. Indeed,
      normally ``v`` would only be executed up to the first success until
      backtracking is needed, however :tacn:`exactly_once` needs to look ahead to see
      whether a second success exists, and may run further effects
      immediately.

   .. exn:: This tactic has more than one success.
      :undocumented:

Manipulating values
-------------------

Pattern matching on terms: match
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: @match_key @ltac_expr__term with {? %| } {+| @match_pattern => @ltac_expr } end
   :name: lazymatch; match; multimatch

   .. insertprodn match_key cpattern

   .. prodn::
      match_key ::= lazymatch
      | match
      | multimatch
      match_pattern ::= @cpattern
      | context {? @ident } [ @cpattern ]
      cpattern ::= @term

   :tacn:`lazymatch`, :tacn:`match` and :tacn:`multimatch` are :token:`ltac_expr1`\s.

   Evaluates :n:`@ltac_expr__term`, which must yield a term, and matches it
   sequentially with the :token:`match_pattern`\s, which may have
   metavariables.  When a match is found, metavariable values are substituted
   into :n:`@ltac_expr`, which is then applied.

   Matching may continue depending on whether  `lazymatch`, `match` or `multimatch`
   is specified.

   In the :token:`match_pattern`\s, metavariables have the form :n:`?@ident`, whereas
   in the :n:`@ltac_expr`\s, the question mark is omitted.  Choose your metavariable
   names with care to avoid name conflicts.  For example, if you use the metavariable `S`,
   then the :token:`ltac_expr` can't use `S` to refer to the constructor of `nat`
   without qualifying the constructor as `Datatypes.S`.

   .. todo how does this differ from the 1-2 other unification routines elsewhere in Rocq?
      Does it use constr_eq or eq_constr_nounivs?

   Matching is non-linear: if a
   metavariable occurs more than once, each occurrence must match the same
   expression.  Expressions match if they are syntactically equal or are
   :term:`α-convertible <alpha-convertible>`.
   Matching is first-order except on variables of the form :n:`@?@ident`
   that occur in the head position of an application. For these variables,
   matching is second-order and returns a functional term.

   .. todo 30 May 20: the `@?ident` form is in dangling_pattern_extension_rule, not included in the doc yet
      maybe belongs with "Applications"

   `lazymatch`
      Causes the match to commit to the first matching branch
      rather than trying a new match if :n:`@ltac_expr` fails.
      :ref:`Example<match_vs_lazymatch_ex>`.

   `match`
      If :n:`@ltac_expr` fails, continue matching with the next branch.
      Failures in subsequent tactics (after the `match`) will not cause selection
      of a new branch.  Examples :ref:`here<match_vs_lazymatch_ex>` and
      :ref:`here<match_vs_multimatch_ex>`.

   `multimatch`
      If :n:`@ltac_expr` fails, continue matching with the next branch.
      When an :n:`@ltac_expr` succeeds for a branch, subsequent failures
      (after the `multimatch`) causing consumption of all the successes
      of :n:`@ltac_expr` trigger selection of a new matching branch.
      :ref:`Example<match_vs_multimatch_ex>`.

      :tacn:`match` :n:`…` is, in fact, shorthand for :tacn:`once` :tacn:`multimatch` `…`.

   :n:`@cpattern`
      The syntax of :token:`cpattern` is
      the same as that of :token:`term`\s, but it can contain pattern matching
      metavariables in the form :n:`?@ident`.  :g:`_` can be used to match
      irrelevant terms.  :ref:`Example<match_with_holes_ex>`.

      .. todo Didn't understand the following 2 paragraphs well enough to revise
         see https://github.com/coq/coq/pull/12103#discussion_r436297754 for a
         possible example

      When a metavariable in the form :n:`?id` occurs under binders,
      say :n:`x__1, …, x__n` and the expression matches, the
      metavariable is instantiated by a term which can then be used in any
      context which also binds the variables :n:`x__1, …, x__n` with
      same types. This provides with a primitive form of matching under
      context which does not require manipulating a functional term.

      There is also a special notation for second-order pattern matching: in an
      applicative pattern of the form :n:`@?@ident @ident__1 … @ident__n`,
      the variable :token:`ident` matches any complex expression with (possible)
      dependencies in the variables :n:`@ident__i` and returns a functional term
      of the form :n:`fun @ident__1 … @ident__n => @term`.

   .. _match_term_context:

   :n:`context {? @ident } [ @cpattern ]`
      Matches any term with a subterm matching :token:`cpattern`. If there is a match
      and :n:`@ident` is present, it is assigned the "matched
      context", i.e. the initial term where the matched subterm is replaced by a
      hole.  Note that `context`
      (with very similar syntax) appearing after the `=>` is the :tacn:`context` tactic.

      For :tacn:`match` and :tacn:`multimatch`, if the evaluation of the :token:`ltac_expr`
      fails, the next matching subterm is tried. If no further subterm matches, the next branch
      is tried.  Matching subterms are considered from top to bottom and from left to
      right (with respect to the raw printing obtained by setting the
      :flag:`Printing All` flag).  :ref:`Example<match_term_context_ex>`.

   .. todo There's a more realistic example from @JasonGross here:
      https://github.com/coq/coq/pull/12103#discussion_r432996954

   :n:`@ltac_expr`
      The tactic to apply if the construct matches.  Metavariable values from the pattern
      match are substituted
      into :n:`@ltac_expr` before it's applied.  Note that metavariables are not
      prefixed with the question mark as they are in :token:`cpattern`.

      If :token:`ltac_expr` evaluates to a tactic, then it is
      applied. If the tactic succeeds, the result of the match expression is
      :tacn:`idtac`.  If :token:`ltac_expr` does not evaluate
      to a tactic, that value is the result of the match expression.

      If :n:`@ltac_expr` is a tactic with backtracking points, then subsequent
      failures after a :tacn:`lazymatch` or :tacn:`multimatch` (but not :tacn:`match`) can cause
      backtracking into :n:`@ltac_expr` to select its next success.
      (:tacn:`match` :n:`…` is equivalent to :tacn:`once` :tacn:`multimatch` `…`.
      The :tacn:`once` prevents backtracking into the :tacn:`match` after it has succeeded.)

   .. note::
      Each |Ltac| construct is processed in two phases: an evaluation phase and an execution phase.
      In most cases, tactics that may change the proof state are applied in the second phase.
      (Tactics that generate integer, string or syntactic values, such as :tacn:`fresh`,
      are processed during the evaluation phase.)

      Unlike other tactics, `*match*` tactics get their first success (applying tactics to do
      so) as part of the evaluation phase.  Among other things, this can affect how early
      failures are processed in :tacn:`assert_fails`.  Please see the note in :tacn:`assert_fails`.

   .. exn:: Expression does not evaluate to a tactic.

      :n:`@ltac_expr` must evaluate to a tactic.

   .. exn:: No matching clauses for match.

      For at least one of the focused goals, there is no branch that matches
      its pattern *and* gets at least one success for :n:`@ltac_expr`.

   .. exn:: Argument of match does not evaluate to a term.

      This happens when :n:`@ltac_expr__term` does not denote a term.

.. _match_vs_lazymatch_ex:

   .. example:: Comparison of lazymatch and match

      In :tacn:`lazymatch`, if :token:`ltac_expr` fails, the :tacn:`lazymatch` fails;
      it doesn't look for further matches.  In :tacn:`match`, if :token:`ltac_expr` fails
      in a matching branch, it will try to match on subsequent branches.

      .. rocqtop:: reset none

         Goal True.

      .. rocqtop:: all

         Fail lazymatch True with
         | True => idtac "branch 1"; fail
         | _ => idtac "branch 2"
         end.

      .. rocqtop:: all

         match True with
         | True => idtac "branch 1"; fail
         | _ => idtac "branch 2"
         end.

.. _match_vs_multimatch_ex:

   .. example:: Comparison of match and multimatch

      :tacn:`match` tactics are only evaluated once, whereas :tacn:`multimatch`
      tactics may be evaluated more than once if the following constructs trigger backtracking:

      .. rocqtop:: all

         Fail match True with
         | True => idtac "branch 1"
         | _ => idtac "branch 2"
         end ;
         idtac "branch A"; fail.

      .. rocqtop:: all

         Fail multimatch True with
         | True => idtac "branch 1"
         | _ => idtac "branch 2"
         end ;
         idtac "branch A"; fail.

.. _match_with_holes_ex:

   .. example:: Matching a pattern with holes

      Notice the :tacn:`idtac` prints ``(z + 1)`` while the :tacn:`pose` substitutes
      ``(x + 1)``.

      .. rocqtop:: in reset

         Goal True.

      .. rocqtop:: all

           match constr:(fun x => (x + 1) * 3) with
           | fun z => ?y * 3 => idtac "y =" y; pose (fun z: nat => y * 5)
           end.

.. _match_term_context_ex:

   .. example:: Multiple matches for a "context" pattern.

      Internally "x <> y" is represented as "(~ (x = y))", which produces the
      first match.

      .. rocqtop:: in reset

         Ltac f t := match t with
                    | context [ (~ ?t) ] => idtac "?t = " t; fail
                    | _ => idtac
                    end.
         Goal True.

      .. rocqtop:: all

         f ((~ True) <> (~ False)).

.. _ltac-match-goal:

Pattern matching on goals and hypotheses: match goal
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: @match_key {? reverse } goal with {? %| } {+| @goal_pattern => @ltac_expr } end
   :name: lazymatch goal; match goal; multimatch goal

   .. insertprodn goal_pattern match_hyp

   .. prodn::
      goal_pattern ::= {*, @match_hyp } %|- @match_pattern
      | [ {*, @match_hyp } %|- @match_pattern ]
      | _
      match_hyp ::= @name : @match_pattern
      | @name := @match_pattern
      | @name := [ @match_pattern ] : @match_pattern

   :tacn:`lazymatch goal`, :tacn:`match goal` and :tacn:`multimatch goal` are :token:`l1_tactic`\s.

   Use this form to match hypotheses and/or goals in the local context.  These patterns have zero or
   more subpatterns to match hypotheses followed by a subpattern to match the conclusion.  Except for the
   differences noted below, this works the same as the corresponding :n:`@match_key @ltac_expr` construct
   (see :tacn:`match`).  Each current goal is processed independently.

   Matching is non-linear: if a
   metavariable occurs more than once, each occurrence must match the same
   expression.  Within a single term, expressions match if they are syntactically equal or
   :term:`α-convertible <alpha-convertible>`.  When a metavariable is used across
   multiple hypotheses or across a hypothesis and the current goal, the expressions match if
   they are :term:`convertible`.

   :n:`{*, @match_hyp }`
      Patterns to match with hypotheses.  Each pattern must match a distinct hypothesis in order
      for the branch to match.

      Hypotheses have the form :n:`@name {? := @term__binder } : @type`.  Patterns bind each of
      these nonterminals separately:

      .. list-table::
         :widths: 2 1
         :header-rows: 1

         * - Pattern syntax
           - Example pattern

         * - :n:`@name : @match_pattern__type`
           - `n : ?t`

         * - :n:`@name := @match_pattern__binder`
           - `n := ?b`

         * - :n:`@name := @term__binder : @type`
           - `n := ?b : ?t`

         * - :n:`@name := [ @match_pattern__binder ] : @match_pattern__type`
           - `n := [ ?b ] : ?t`

      ..

         :token:`name` can't have a `?`.  Note that the last two forms are equivalent except that:

         - if the `:` in the third form has been bound to something else in a notation, you must use the fourth form.
           Note that cmd:`Require Import` `ssreflect` loads a notation that does this.
         - a :n:`@term__binder` such as `[ ?l ]` (e.g., denoting a singleton list after
           :cmd:`Import` `ListNotations`) must be parenthesized or, for the fourth form,
           use double brackets: `[ [ ?l ] ]`.

         :n:`@term__binder`\s in the form `[?x ; ?y]` for a list are not parsed correctly.  The workaround is
         to add parentheses or to use the underlying term instead of the notation, i.e. `(cons ?x ?y)`.

      If there are multiple :token:`match_hyp`\s in a branch, there may be multiple ways to match them to hypotheses.
      For :tacn:`match goal` and :tacn:`multimatch goal`, if the evaluation of the :token:`ltac_expr` fails,
      matching will continue with the next hypothesis combination.  When those are exhausted,
      the next alternative from any `context` constructs in the :token:`match_pattern`\s is tried and then,
      when the context alternatives are exhausted, the next branch is tried.
      :ref:`Example<match_goal_multiple_hyps_ex>`.

   `reverse`
      Hypothesis matching for :token:`match_hyp`\s normally begins by matching them from left to right,
      to hypotheses, last to first.  Specifying `reverse` begins matching in the reverse order, from
      first to last.  :ref:`Normal<match_goal_hyps_ex>` and :ref:`reverse<match_goal_hyps_rev_ex>` examples.

   :n:`|- @match_pattern`
      A pattern to match with the current goal

   :n:`@goal_pattern with [ ... ]`
      The square brackets don't affect the semantics.  They are permitted for aesthetics.

   .. exn:: No matching clauses for match goal.

      No clause succeeds, i.e. all matching patterns, if any, fail at the
      application of the :token:`ltac_expr`.

Examples:

.. _match_goal_hyps_ex:

   .. example:: Matching hypotheses

      Hypotheses are matched from the last hypothesis (which is by default the newest
      hypothesis) to the first until the :tacn:`apply` succeeds.

      .. rocqtop:: reset all

         Goal forall A B : Prop, A -> B -> (A->B).
         intros.
         match goal with
         | H : _ |- _ => idtac "apply " H; apply H
         end.

.. _match_goal_hyps_rev_ex:

   .. example:: Matching hypotheses with reverse

      Hypotheses are matched from the first hypothesis to the last until the :tacn:`apply` succeeds.

      .. rocqtop:: reset all

         Goal forall A B : Prop, A -> B -> (A->B).
         intros.
         match reverse goal with
         | H : _ |- _ => idtac "apply " H; apply H
         end.

.. _match_goal_multiple_hyps_ex:

   .. example:: Multiple ways to match hypotheses

      Every possible match for the hypotheses is evaluated until the right-hand
      side succeeds.  Note that `H1` and `H2` are never matched to the same hypothesis.
      Observe that the number of permutations can grow as the factorial
      of the number of hypotheses and hypothesis patterns.

      .. rocqtop:: reset all

         Goal forall A B : Prop, A -> B -> (A->B).
         intros A B H.
         match goal with
         | H1 : _, H2 : _ |- _ => idtac "match " H1 H2; fail
         | _ => idtac
         end.

   .. todo need examples for:
      match_context_rule ::= [ {*, @match_hyp } |- @match_pattern ] => @ltac_expr
      match_hyp ::= | @name := {? [ @match_pattern ] : } @match_pattern

.. todo The following items (up to numgoals) are part of "value_tactic".  I'd like to make
   this a subsection and explain that they all return values.  How do I get a 5th-level section title?

Filling a term context
~~~~~~~~~~~~~~~~~~~~~~

The following expression is not a tactic in the sense that it does not
produce subgoals but generates a term to be used in tactic expressions:

.. tacn:: context @ident [ @term ]

   Returns the term matched with the `context` pattern (described :ref:`here<match_term_context>`)
   substituting :token:`term` for the hole created by the pattern.

   :tacn:`context` is a :token:`value_tactic`.

   .. exn:: Not a context variable.
      :undocumented:

   .. exn:: Unbound context identifier @ident.
      :undocumented:

   .. example:: Substituting a matched context

      .. rocqtop:: reset all

         Goal True /\ True.
         match goal with
         | |- context G [True] => let x := context G [False] in idtac x
         end.

Generating fresh hypothesis names
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tactics sometimes need to generate new names for hypothesis.  Letting Rocq
choose a name with the intro tactic is not so good since it is
very awkward to retrieve that name. The following
expression returns an identifier:

.. tacn:: fresh {* {| @string | @qualid } }

   .. todo you can't have a :tacn: with the same name as a :gdef: for now,
      eg `fresh` can't be both

   Returns a fresh identifier name (i.e. one that is not already used in the local context
   and not previously returned by :tacn:`fresh` in the current :token:`ltac_expr`).
   The fresh identifier is formed by concatenating the final :token:`ident` of each :token:`qualid`
   (dropping any qualified components) and each specified :token:`string`.
   If the resulting name is already used, a number is appended to make it fresh.
   If no arguments are given, the name is a fresh derivative of the name ``H``.

   .. note:: We recommend generating the fresh identifier immediately before
      adding it to the local context.  Using :tacn:`fresh` in a local function
      may not work as you expect:

      Successive calls to :tacn:`fresh` give distinct names even if the names haven't
      yet been added to the local context:

      .. rocqtop:: reset none

         Goal True -> True.

      .. rocqtop:: out

         intro x.

      .. rocqtop:: all

         let a := fresh "x" in
         let b := fresh "x" in
         idtac a b.

      When applying :tacn:`fresh` in a function, the name is chosen based on the
      tactic context at the point where the function was defined:

      .. rocqtop:: all

         let a := fresh "x" in
         let f := fun _ => fresh "x" in
         let c := f () in
         let d := f () in
         idtac a c d.

   :tacn:`fresh` is a :token:`value_tactic`.

Computing in a term: eval
~~~~~~~~~~~~~~~~~~~~~~~~~

Evaluation of a term can be performed with:

:n:`eval @red_expr in @term`

See :tacn:`eval`.  :tacn:`eval` is a :token:`value_tactic`.

Getting the type of a term
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: type of @term

   This tactic returns the type of :token:`term`.

   :tacn:`type of` is a :token:`value_tactic`.

Manipulating untyped terms: type_term
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The :n:`uconstr : ( @term )` construct can be used to build an untyped term.
See :token:`syn_value`.

.. tacn:: type_term @one_term

   In |Ltac|, an untyped term can contain references to hypotheses or to
   |Ltac| variables containing typed or untyped terms. An untyped term can be
   type checked with :tacn:`type_term` whose argument is parsed as an
   untyped term and returns a well-typed term which can be used in tactics.

   :tacn:`type_term` is a :token:`value_tactic`.

Counting goals: numgoals
~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: numgoals

   The number of goals under focus can be recovered using the :n:`numgoals`
   function. Combined with the :tacn:`guard` tactic below, it can be used to
   branch over the number of goals produced by previous tactics.

   :tacn:`numgoals` is a :token:`value_tactic`.

   .. example::

      .. rocqtop:: reset in

         Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

         Goal True /\ True /\ True.
         split;[|split].

      .. rocqtop:: all abort

         all:pr_numgoals.

Testing boolean expressions: guard
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: guard @int_or_var @comparison @int_or_var

   .. insertprodn int_or_var comparison

   .. prodn::
      int_or_var ::= {| @integer | @ident }
      comparison ::= =
      | <
      | <=
      | >
      | >=

   Tests a boolean expression.  If the expression evaluates to true,
   it succeeds without affecting the proof.  The tactic fails if the
   expression is false.

   The accepted tests are simple integer comparisons.

   .. todo why doesn't it support = and <> as well?

   .. example:: guard

      .. rocqtop:: in

         Goal True /\ True /\ True.
         split;[|split].

      .. rocqtop:: all

         all:let n:= numgoals in guard n<4.
         Fail all:let n:= numgoals in guard n=2.

   .. exn:: Condition not satisfied.
      :undocumented:

Checking properties of terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each of the following tactics acts as the identity if the check
succeeds, and results in an error otherwise.

.. tacn:: constr_eq_strict @one_term @one_term

   Succeeds if the arguments are equal modulo alpha conversion and ignoring casts.
   Universes are considered equal when they are equal in the universe graph.

   .. exn:: Not equal.
      :undocumented:

   .. exn:: Not equal (due to universes).
      :undocumented:

   .. tacn:: constr_eq @one_term @one_term

      Like :tacn:`constr_eq_strict`, but may add constraints to make universes equal.

   .. tacn:: constr_eq_nounivs @one_term @one_term

      Like :tacn:`constr_eq_strict`, but all universes are considered equal.

.. tacn:: convert @one_term @one_term

   Succeeds if the arguments are convertible, potentially
   adding universe constraints, and fails otherwise.

.. tacn:: unify @one_term @one_term {? with @ident }

   Succeeds if the arguments are unifiable, potentially
   instantiating existential variables, and fails otherwise.

   :n:`@ident`, if specified, is the name of the :ref:`hint database <hintdatabases>`
   that specifies which definitions are transparent.
   Otherwise, all definitions are considered transparent.  Unification only expands
   transparent definitions while matching the two :n:`@one_term`\s.

.. tacn:: is_evar @one_term

   Succeeds if :n:`@one_term` is an existential
   variable and otherwise fails. Existential variables are uninstantiated
   variables generated
   by :tacn:`eapply` and some other tactics.

   .. exn:: Not an evar.
      :undocumented:

.. tacn:: not_evar @one_term
   :undocumented:

.. tacn:: has_evar @one_term

   Succeeds if :n:`@one_term` has an existential variable as
   a subterm and fails otherwise. Unlike context patterns combined with
   ``is_evar``, this tactic scans all subterms, including those under binders.

   .. exn:: No evars.
      :undocumented:

.. tacn:: is_ground @one_term

   The negation of :n:`has_evar @one_term`.  Succeeds if :n:`@one_term`
   does not have an existential variable as a subterm and fails otherwise.

   .. exn:: Not ground.
      :undocumented:

.. tacn:: is_var @one_term

   Succeeds if :n:`@one_term` is a variable or hypothesis in
   the current local context and fails otherwise.

   .. exn:: Not a variable or hypothesis.
      :undocumented:

.. tacn:: is_const @one_term

   Succeeds if :n:`@one_term` is a global constant that is neither a (co)inductive
   type nor a constructor and fails otherwise.

   .. exn:: not a constant.
      :undocumented:

.. tacn:: is_fix @one_term

   Succeeds if :n:`@one_term` is a `fix` construct (see :n:`@term_fix`)
   and fails otherwise.  Fails for `let fix` forms.

   .. exn:: not a fix definition.
      :undocumented:

   .. example:: is_fix

      .. rocqtop:: reset in

         Goal True.
         is_fix (fix f (n : nat) := match n with S n => f n | O => O end).

.. tacn:: is_cofix @one_term
   :undocumented:

   Succeeds if :n:`@one_term` is a `cofix` construct (see :n:`@term_cofix`)
   and fails otherwise.  Fails for `let cofix` forms.

   .. exn:: not a cofix definition.
      :undocumented:

   .. example:: is_cofix

      .. rocqtop:: reset in

         CoInductive Stream (A : Type) : Type :=  Cons : A -> Stream A -> Stream A.
         Goal True.
         let c := constr:(cofix f : Stream unit := Cons _ tt f) in
           is_cofix c.

.. tacn:: is_constructor @one_term

   Succeeds if :n:`@one_term` is the constructor of a (co)inductive type and fails
   otherwise.

   .. exn:: not a constructor.
      :undocumented:

.. tacn:: is_ind @one_term

   Succeeds if :n:`@one_term` is a (co)inductive type (family) and fails otherwise.
   Note that `is_ind (list nat)` fails even though `is_ind list` succeeds, because
   `list nat` is an application.

   .. exn:: not an (co)inductive datatype.
      :undocumented:

.. tacn:: is_proj @one_term

   Succeeds if :n:`@one_term` is a primitive projection applied to a record argument
   and fails otherwise.

   .. exn:: not a primitive projection.
      :undocumented:

   .. example:: is_proj

      .. rocqtop:: reset in

         Set Primitive Projections.
         Record Box {T : Type} := box { unbox : T }.
         Arguments box {_} _.
         Goal True.
         is_proj (unbox (box 0)).

Timing
------

Timeout
~~~~~~~

We can force a tactic to stop if it has not finished after a certain
amount of time:

.. tacn:: timeout @nat_or_var @ltac_expr3

   :n:`@ltac_expr3` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied but only its first success is used (as with :tacn:`once`),
   and it is interrupted after :n:`@nat_or_var` seconds if it is still running.
   If it is interrupted the outcome is a failure.

   :tacn:`timeout` is an :token:`l3_tactic`.

   .. warning::

      For the moment, timeout is based on elapsed time in seconds,
      which is very machine-dependent: a script that works on a quick machine
      may fail on a slow one. The converse is even possible if you combine a
      timeout with some other tacticals. This tactical is hence proposed only
      for convenience during debugging or other development phases, we strongly
      advise you to not leave any timeout in final scripts.

Timing a tactic
~~~~~~~~~~~~~~~

A tactic execution can be timed:

.. tacn:: time {? @string } @ltac_expr3

   evaluates :n:`@ltac_expr3` and displays the running time of the tactic expression, whether it
   fails or succeeds. In case of several successes, the time for each successive
   run is displayed. Time is in seconds and is machine-dependent. The :n:`@string`
   argument is optional. When provided, it is used to identify this particular
   occurrence of :tacn:`time`.

   :tacn:`time` is an :token:`l3_tactic`.

Timing a tactic that evaluates to a term: time_constr
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tactic expressions that produce terms can be timed with the experimental
tactic

.. tacn:: time_constr @ltac_expr

   which evaluates :n:`@ltac_expr ()` and displays the time the tactic expression
   evaluated, assuming successful evaluation. Time is in seconds and is
   machine-dependent.

   This tactic currently does not support nesting, and will report times
   based on the innermost execution. This is due to the fact that it is
   implemented using the following internal tactics:

.. tacn:: restart_timer {? @string }

   Reset a timer

.. tacn:: finish_timing {? ( @string ) } {? @string }

   Display an optionally named timer. The parenthesized string argument
   is also optional, and determines the label associated with the timer
   for printing.

By copying the definition of :tacn:`time_constr` from the standard library,
users can achieve support for a fixed pattern of nesting by passing
different :token:`string` parameters to :tacn:`restart_timer` and
:tacn:`finish_timing` at each level of nesting.

.. example::

   .. rocqtop:: all reset abort

      Ltac time_constr1 tac :=
        let eval_early := match goal with _ => restart_timer "(depth 1)" end in
        let ret := tac () in
        let eval_early := match goal with _ => finish_timing ( "Tactic evaluation" ) "(depth 1)" end in
        ret.

      Goal True.
        let v := time_constr
             ltac:(fun _ =>
                     let x := time_constr1 ltac:(fun _ => constr:(10 * 10)) in
                     let y := time_constr1 ltac:(fun _ => eval compute in x) in
                     y) in
        pose v.

Print/identity tactic: idtac
----------------------------

.. tacn:: idtac {* {| @ident | @string | @natural } }

   Leaves the proof unchanged and prints the given tokens. :token:`String<string>`\s
   and :token:`natural`\s are printed
   literally. If :token:`ident` is an |Ltac| variable, its contents are printed; if not, it
   is an error.

   :tacn:`idtac` is an :token:`l1_tactic`.

Tactic toplevel definitions
---------------------------

Defining |Ltac| symbols
~~~~~~~~~~~~~~~~~~~~~~~

|Ltac| toplevel definitions are made as follows:

.. index:: ::=

.. cmd:: Ltac @tacdef_body {* with @tacdef_body }

   .. insertprodn tacdef_body tacdef_body

   .. prodn::
      tacdef_body ::= @qualid {* @name } {| := | ::= } @ltac_expr

   Defines or redefines an |Ltac| symbol.

   If the :attr:`local` attribute is specified, definitions will not be
   exported outside the current module and redefinitions only apply for the current module.

   :token:`qualid`
      Name of the symbol being defined or redefined.  For definitions, :token:`qualid`
      must be a simple :token:`ident`.

   :n:`{* @name }`
      If specified, the symbol defines a function with the given parameter names.
      If no names are specified, :token:`qualid` is assigned the value of :token:`ltac_expr`.

   `:=`
      Defines a user-defined symbol, but gives an error if the symbol has already
      been defined.

      .. todo apparent inconsistency:

         "Ltac intros := idtac" seems like it redefines/hides an
         existing tactic, but in fact it creates a tactic which can
         only be called by its qualified name.  This is true in
         general of tactic notations.  The only way to override most
         primitive tactics, and any user-defined tactic notation, is
         with another tactic notation.

      .. exn:: There is already an Ltac named @qualid
         :undocumented:

   `::=`
      Redefines an existing user-defined symbol, but gives an error if the
      symbol doesn't exist.  Note that :cmd:`Tactic Notation`\s
      do not count as user-defined tactics for `::=`.

      In sections or with :attr:`local`, the redefinition is forgotten
      at the end of the current module or section.
      :attr:`global` and :attr:`export` may be used with their standard meanings.

      Outside sections specifying no locality is equivalent to repeating the command
      with :attr:`global` and :attr:`export`.

      Redefinitions are incompatible with :n:`{* with @tacdef_body }`.

      .. exn:: There is no Ltac named @qualid
         :undocumented:

   :n:`{* with @tacdef_body }`
      Permits definition of mutually recursive tactics.

   .. note::

      The following definitions are equivalent:

      - :n:`Ltac @qualid {+ @name } := @ltac_expr`
      - :n:`Ltac @qualid := fun {+ @name } => @ltac_expr`

Printing |Ltac| tactics
~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Ltac @qualid

   Defined |Ltac| functions can be displayed using this command.

.. cmd:: Print Ltac Signatures

   This command displays a list of all user-defined tactics, with their arguments.


.. _ltac-examples:

Examples of using |Ltac|
-------------------------

Proof that the natural numbers have at least two elements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: Proof that the natural numbers have at least two elements

   The first example shows how to use pattern matching over the proof
   context to prove that natural numbers have at least two
   elements. This can be done as follows:

   .. rocqtop:: reset all

      Lemma card_nat :
        ~ exists x y : nat, forall z:nat, x = z \/ y = z.
      Proof.
      intros (x & y & Hz).
      destruct (Hz 0), (Hz 1), (Hz 2).

   At this point, the :tacn:`congruence` tactic would finish the job:

   .. rocqtop:: all abort

      all: congruence.

   But for the purpose of the example, let's craft our own custom
   tactic to solve this:

   .. rocqtop:: none

      Lemma card_nat :
        ~ exists x y : nat, forall z:nat, x = z \/ y = z.
      Proof.
      intros (x & y & Hz).
      destruct (Hz 0), (Hz 1), (Hz 2).

   .. rocqtop:: all abort

      all: match goal with
           | _ : ?a = ?b, _ : ?a = ?c |- _ => assert (b = c) by now transitivity a
           end.
      all: discriminate.

   Notice that all the (very similar) cases coming from the three
   eliminations (with three distinct natural numbers) are successfully
   solved by a ``match goal`` structure and, in particular, with only one
   pattern (use of non-linear matching).


Proving that a list is a permutation of a second list
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: Proving that a list is a permutation of a second list

   Let's first define the permutation predicate:

   .. rocqtop:: in reset

      Section Sort.

        Variable A : Set.

        Inductive perm : list A -> list A -> Prop :=
        | perm_refl : forall l, perm l l
        | perm_cons : forall a l0 l1, perm l0 l1 -> perm (a :: l0) (a :: l1)
        | perm_append : forall a l, perm (a :: l) (l ++ a :: nil)
        | perm_trans : forall l0 l1 l2, perm l0 l1 -> perm l1 l2 -> perm l0 l2.

      End Sort.

   .. rocqtop:: none

      Require Import ListDef.


   Next we define an auxiliary tactic :g:`perm_aux` which takes an
   argument used to control the recursion depth. This tactic works as
   follows: If the lists are identical (i.e. convertible), it
   completes the proof. Otherwise, if the lists have identical heads,
   it looks at their tails.  Finally, if the lists have different
   heads, it rotates the first list by putting its head at the end.

   Every time we perform a rotation, we decrement :g:`n`. When :g:`n`
   drops down to :g:`1`, we stop performing rotations and we fail.
   The idea is to give the length of the list as the initial value of
   :g:`n`. This way of counting the number of rotations will avoid
   going back to a head that had been considered before.

   From Section :ref:`ltac-syntax` we know that Ltac has a primitive
   notion of integers, but they are only used as arguments for
   primitive tactics and we cannot make computations with them. Thus,
   instead, we use Rocq's natural number type :g:`nat`.

   .. rocqtop:: in

      Ltac perm_aux n :=
        match goal with
        | |- (perm _ ?l ?l) => apply perm_refl
        | |- (perm _ (?a :: ?l1) (?a :: ?l2)) =>
           let newn := eval compute in (length l1) in
               (apply perm_cons; perm_aux newn)
        | |- (perm ?A (?a :: ?l1) ?l2) =>
           match eval compute in n with
           | 1 => fail
           | _ =>
               let l1' := constr:(l1 ++ a :: nil) in
               (apply (perm_trans A (a :: l1) l1' l2);
               [ apply perm_append | compute; perm_aux (pred n) ])
           end
        end.


   The main tactic is :g:`solve_perm`. It computes the lengths of the
   two lists and uses them as arguments to call :g:`perm_aux` if the
   lengths are equal. (If they aren't, the lists cannot be
   permutations of each other.)

   .. rocqtop:: in

      Ltac solve_perm :=
        match goal with
        | |- (perm _ ?l1 ?l2) =>
           match eval compute in (length l1 = length l2) with
           | (?n = ?n) => perm_aux n
           end
        end.

   And now, here is how we can use the tactic :g:`solve_perm`:

   .. rocqtop:: out

      Goal perm nat (1 :: 2 :: 3 :: nil) (3 :: 2 :: 1 :: nil).

   .. rocqtop:: all abort

      solve_perm.

   .. rocqtop:: out

      Goal perm nat
             (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)
             (0 :: 2 :: 4 :: 6 :: 8 :: 9 :: 7 :: 5 :: 3 :: 1 :: nil).

   .. rocqtop:: all abort

      solve_perm.


Deciding intuitionistic propositional logic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern matching on goals allows powerful backtracking when returning tactic
values. An interesting application is the problem of deciding intuitionistic
propositional logic. Considering the contraction-free sequent calculi LJT* of
Roy Dyckhoff :cite:`Dyc92`, it is quite natural to code such a tactic using the
tactic language as shown below.

.. rocqtop:: in reset

   Ltac basic :=
   match goal with
       | |- True => trivial
       | _ : False |- _ => contradiction
       | _ : ?A |- ?A => assumption
   end.

.. rocqtop:: in

   Ltac simplify :=
   repeat (intros;
       match goal with
           | H : ~ _ |- _ => red in H
           | H : _ /\ _ |- _ =>
               elim H; do 2 intro; clear H
           | H : _ \/ _ |- _ =>
               elim H; intro; clear H
           | H : ?A /\ ?B -> ?C |- _ =>
               cut (A -> B -> C);
                   [ intro | intros; apply H; split; assumption ]
           | H: ?A \/ ?B -> ?C |- _ =>
               cut (B -> C);
                   [ cut (A -> C);
                       [ intros; clear H
                       | intro; apply H; left; assumption ]
                   | intro; apply H; right; assumption ]
           | H0 : ?A -> ?B, H1 : ?A |- _ =>
               cut B; [ intro; clear H0 | apply H0; assumption ]
           | |- _ /\ _ => split
           | |- ~ _ => red
       end).

.. rocqtop:: in

   Ltac my_tauto :=
     simplify; basic ||
     match goal with
         | H : (?A -> ?B) -> ?C |- _ =>
             cut (B -> C);
                 [ intro; cut (A -> B);
                     [ intro; cut C;
                         [ intro; clear H | apply H; assumption ]
                     | clear H ]
                 | intro; apply H; intro; assumption ]; my_tauto
         | H : ~ ?A -> ?B |- _ =>
             cut (False -> B);
                 [ intro; cut (A -> False);
                     [ intro; cut B;
                         [ intro; clear H | apply H; assumption ]
                     | clear H ]
                 | intro; apply H; red; intro; assumption ]; my_tauto
         | |- _ \/ _ => (left; my_tauto) || (right; my_tauto)
     end.

The tactic ``basic`` tries to reason using simple rules involving truth, falsity
and available assumptions. The tactic ``simplify`` applies all the reversible
rules of Dyckhoff’s system. Finally, the tactic ``my_tauto`` (the main
tactic to be called) simplifies with ``simplify``, tries to conclude with
``basic`` and tries several paths using the backtracking rules (one of the
four Dyckhoff’s rules for the left implication to get rid of the contraction
and the right ``or``).

Having defined ``my_tauto``, we can prove tautologies like these:

.. rocqtop:: in

   Lemma my_tauto_ex1 :
     forall A B : Prop, A /\ B -> A \/ B.
   Proof. my_tauto. Qed.

.. rocqtop:: in

   Lemma my_tauto_ex2 :
     forall A B : Prop, (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.
   Proof. my_tauto. Qed.


Deciding type isomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~

A trickier problem is to decide equalities between types modulo
isomorphisms. Here, we choose to use the isomorphisms of the simply
typed λ-calculus with Cartesian product and unit type (see, for
example, :cite:`RC95`). The axioms of this λ-calculus are given below.

.. rocqtop:: in reset

   Open Scope type_scope.

.. rocqtop:: in

   Section Iso_axioms.

.. rocqtop:: in

   Variables A B C : Set.

.. rocqtop:: in

   Axiom Com : A * B = B * A.

   Axiom Ass : A * (B * C) = A * B * C.

   Axiom Cur : (A * B -> C) = (A -> B -> C).

   Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).

   Axiom P_unit : A * unit = A.

   Axiom AR_unit : (A -> unit) = unit.

   Axiom AL_unit : (unit -> A) = A.

.. rocqtop:: in

   Lemma Cons : B = C -> A * B = A * C.

   Proof.

   intro Heq; rewrite Heq; reflexivity.

   Qed.

.. rocqtop:: in

   End Iso_axioms.

.. rocqtop:: in

   Ltac simplify_type ty :=
   match ty with
       | ?A * ?B * ?C =>
           rewrite <- (Ass A B C); try simplify_type_eq
       | ?A * ?B -> ?C =>
           rewrite (Cur A B C); try simplify_type_eq
       | ?A -> ?B * ?C =>
           rewrite (Dis A B C); try simplify_type_eq
       | ?A * unit =>
           rewrite (P_unit A); try simplify_type_eq
       | unit * ?B =>
           rewrite (Com unit B); try simplify_type_eq
       | ?A -> unit =>
           rewrite (AR_unit A); try simplify_type_eq
       | unit -> ?B =>
           rewrite (AL_unit B); try simplify_type_eq
       | ?A * ?B =>
           (simplify_type A; try simplify_type_eq) ||
           (simplify_type B; try simplify_type_eq)
       | ?A -> ?B =>
           (simplify_type A; try simplify_type_eq) ||
           (simplify_type B; try simplify_type_eq)
   end
   with simplify_type_eq :=
   match goal with
       | |- ?A = ?B => try simplify_type A; try simplify_type B
   end.

.. rocqtop:: in

   Ltac len trm :=
   match trm with
       | _ * ?B => let succ := len B in constr:(S succ)
       | _ => constr:(1)
   end.

.. rocqtop:: in

   Ltac assoc := repeat rewrite <- Ass.

.. rocqtop:: in

   Ltac solve_type_eq n :=
   match goal with
       | |- ?A = ?A => reflexivity
       | |- ?A * ?B = ?A * ?C =>
           apply Cons; let newn := len B in solve_type_eq newn
       | |- ?A * ?B = ?C =>
           match eval compute in n with
               | 1 => fail
               | _ =>
                   pattern (A * B) at 1; rewrite Com; assoc; solve_type_eq (pred n)
           end
   end.

.. rocqtop:: in

   Ltac compare_structure :=
   match goal with
       | |- ?A = ?B =>
           let l1 := len A
           with l2 := len B in
               match eval compute in (l1 = l2) with
                   | ?n = ?n => solve_type_eq n
               end
   end.

.. rocqtop:: in

   Ltac solve_iso := simplify_type_eq; compare_structure.

The tactic to judge equalities modulo this axiomatization is shown above.
The algorithm is quite simple. First types are simplified using axioms that
can be oriented (this is done by ``simplify_type`` and ``simplify_type_eq``).
The normal forms are sequences of Cartesian products without a Cartesian product
in the left component. These normal forms are then compared modulo permutation
of the components by the tactic ``compare_structure``. If they have the same
length, the tactic ``solve_type_eq`` attempts to prove that the types are equal.
The main tactic that puts all these components together is ``solve_iso``.

Here are examples of what can be solved by ``solve_iso``.

.. rocqtop:: in

   Lemma solve_iso_ex1 :
     forall A B : Set, A * unit * B = B * (unit * A).
   Proof.
     intros; solve_iso.
   Qed.

.. rocqtop:: in

   Lemma solve_iso_ex2 :
     forall A B C : Set,
       (A * unit -> B * (C * unit)) =
       (A * unit -> (C -> unit) * C) * (unit -> A -> B).
   Proof.
     intros; solve_iso.
   Qed.


Debugging |Ltac| tactics
------------------------

Backtraces
~~~~~~~~~~

.. flag:: Ltac Backtrace

   Setting this :term:`flag` displays a backtrace on Ltac failures that can be useful
   to find out what went wrong. It is disabled by default for performance
   reasons.

Tracing execution
~~~~~~~~~~~~~~~~~

.. cmd:: Info @natural @ltac_expr

   Applies :token:`ltac_expr` and prints a trace of the tactics that were successfully
   applied, discarding branches that failed.
   :tacn:`idtac` tactics appear in the trace as comments containing the output.

   This command is valid only in proof mode.  It accepts :ref:`goal-selectors`.

   The number :n:`@natural` is the unfolding level of tactics in the trace. At level
   0, the trace contains a sequence of tactics in the actual script, at level 1,
   the trace will be the concatenation of the traces of these tactics, etc…

   .. example::

      .. rocqtop:: in reset

         Ltac t x := exists x; reflexivity.
         Goal exists n, n=0.

      .. rocqtop:: all

         Info 0 t 1||t 0.

      .. rocqtop:: in

         Undo.

      .. rocqtop:: all

         Info 1 t 1||t 0.

   The trace produced by :cmd:`Info` tries its best to be a reparsable
   |Ltac| script, but this goal is not achievable in all generality.
   So some of the output traces will contain oddities.

   As an additional help for debugging, the trace produced by :cmd:`Info` contains
   (in comments) the messages produced by the :tacn:`idtac` tactical at the right
   position in the script. In particular, the calls to idtac in branches which failed are
   not printed.

   .. opt:: Info Level @natural

      This :term:`option` is an alternative to the :cmd:`Info` command.

      This will automatically print the same trace as :n:`Info @natural` at each
      tactic call. The unfolding level can be overridden by a call to the
      :cmd:`Info` command.

.. _interactive-debugger:

Interactive debugger
~~~~~~~~~~~~~~~~~~~~

.. flag:: Ltac Debug

   This flag, when set, enables the step-by-step debugger in the |Ltac| interpreter.
   The debugger is supported in `rocq repl` and Proof General by printing information
   on the console and accepting typed commands.  In addition, RocqIDE now supports a
   :ref:`visual debugger <rocqide-debugger>` with additional capabilities.

When the debugger is activated in `rocq repl`, it stops at every step of the evaluation of
the current |Ltac| expression and prints information on what it is doing.
The debugger stops, prompting for a command which can be one of the
following:

+-----------------+-----------------------------------------------+
| newline         | go to the next step                           |
+-----------------+-----------------------------------------------+
| h               | get help                                      |
+-----------------+-----------------------------------------------+
| r n             | advance n steps further                       |
+-----------------+-----------------------------------------------+
| r string        | advance up to the next call to “idtac string” |
+-----------------+-----------------------------------------------+
| s               | continue current evaluation without stopping  |
+-----------------+-----------------------------------------------+
| x               | exit current evaluation                       |
+-----------------+-----------------------------------------------+

.. exn:: Debug mode not available in the IDE
   :undocumented:

A non-interactive mode for the debugger is available via the flag:

.. flag:: Ltac Batch Debug

   This flag has the effect of presenting a newline at every prompt, when
   the debugger is on in `rocq repl`.  (It has no effect when running the
   RocqIDE debugger.)  The debug log thus created, which does not require
   user input to generate when this flag is set, can then be run through
   external tools such as diff.

.. todo: maybe drop Debug

.. cmd:: Debug {| On | Off }

   Equivalent to :n:`Set Ltac Debug` or :n:`Unset Ltac Debug`.

Profiling |Ltac| tactics
~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to measure the time spent in invocations of primitive
tactics as well as tactics defined in |Ltac| and their inner
invocations. The primary use is the development of complex tactics,
which can sometimes be so slow as to impede interactive usage. The
reasons for the performance degradation can be intricate, like a slowly
performing |Ltac| match or a sub-tactic whose performance only
degrades in certain situations. The profiler generates a call tree and
indicates the time spent in a tactic depending on its calling context. Thus
it allows to locate the part of a tactic definition that contains the
performance issue.

.. flag:: Ltac Profiling

   This :term:`flag` enables and disables the profiler.

.. cmd:: Show Ltac Profile {? {| CutOff @integer | @string } }

   Prints the profile.

   :n:`CutOff @integer`
      By default, tactics that account for less than 2% of the total time are not displayed.
      `CutOff` lets you specify a different percentage.

   :n:`@string`

      Limits the profile to all tactics that start with :n:`@string`. Append a period
      (.) to the string if you only want exactly that name.

.. cmd:: Reset Ltac Profile

   Resets the profile, that is, deletes all accumulated information.

   .. warning::

      Backtracking across a :cmd:`Reset Ltac Profile` will not restore the information.

The following example requires the Stdlib library to use the :tacn:`lia` tactic.

.. rocqtop:: reset in extra-stdlib

   From Stdlib Require Import Lia.

   Ltac mytauto := tauto.
   Ltac tac := intros; repeat split; lia || mytauto.

   Notation max x y := (x + (y - x)) (only parsing).

   Goal forall x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z,
       max x (max y z) = max (max x y) z /\ max x (max y z) = max (max x y) z
       /\
       (A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J /\ K /\ L /\ M /\
        N /\ O /\ P /\ Q /\ R /\ S /\ T /\ U /\ V /\ W /\ X /\ Y /\ Z
        ->
        Z /\ Y /\ X /\ W /\ V /\ U /\ T /\ S /\ R /\ Q /\ P /\ O /\ N /\
        M /\ L /\ K /\ J /\ I /\ H /\ G /\ F /\ E /\ D /\ C /\ B /\ A).
   Proof.

.. rocqtop:: all extra-stdlib

   Set Ltac Profiling.
   tac.
   Show Ltac Profile.
   Show Ltac Profile "lia".

.. rocqtop:: in extra-stdlib

   Abort.
   Unset Ltac Profiling.

.. tacn:: start ltac profiling

   This tactic behaves like :tacn:`idtac` but enables the profiler.

.. tacn:: stop ltac profiling

   Similarly to :tacn:`start ltac profiling`, this tactic behaves like
   :tacn:`idtac`. Together, they allow you to exclude parts of a proof script
   from profiling.

.. tacn:: reset ltac profile

   Equivalent to the :cmd:`Reset Ltac Profile` command, which allows
   resetting the profile from tactic scripts for benchmarking purposes.

.. tacn:: show ltac profile {? {| cutoff @integer | @string } }

   Equivalent to the :cmd:`Show Ltac Profile` command,
   which allows displaying the profile from tactic scripts for
   benchmarking purposes.

.. warn:: Ltac Profiler encountered an invalid stack (no \
         self node). This can happen if you reset the profile during \
         tactic execution

   Currently, :tacn:`reset ltac profile` is not very well-supported,
   as it clears all profiling information about all tactics, including
   ones above the current tactic.  As a result, the profiler has
   trouble understanding where it is in tactic execution.  This mixes
   especially poorly with backtracking into multi-success tactics.  In
   general, non-top-level calls to :tacn:`reset ltac profile` should
   be avoided.

You can also pass the ``-profile-ltac`` command line option to ``rocq compile``, which
turns the :flag:`Ltac Profiling` flag on at the beginning of each document,
and performs a :cmd:`Show Ltac Profile` at the end.

Run-time optimization tactic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: optimize_heap

   This tactic behaves like :tacn:`idtac`, except that running it compacts the
   heap in the OCaml run-time system. It is analogous to the
   :cmd:`Optimize Heap` command.

.. cmd:: infoH @ltac_expr

   Used internally by Proof General.  See `#12423 <https://github.com/coq/coq/issues/12423>`_ for
   some background.
