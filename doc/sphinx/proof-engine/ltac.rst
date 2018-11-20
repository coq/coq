.. _ltac:

The tactic language
===================

This chapter gives a compact documentation of |Ltac|, the tactic language
available in |Coq|. We start by giving the syntax, and next, we present the
informal semantics. If you want to know more regarding this language and
especially about its foundations, you can refer to :cite:`Del00`. Chapter
:ref:`detailedexamplesoftactics` is devoted to giving small but nontrivial
use examples of this language.

.. _ltac-syntax:

Syntax
------

The syntax of the tactic language is given below. See Chapter
:ref:`gallinaspecificationlanguage` for a description of the BNF metasyntax used
in these grammar rules. Various already defined entries will be used in this
chapter: entries :token:`natural`, :token:`integer`, :token:`ident`,
:token:`qualid`, :token:`term`, :token:`cpattern` and :token:`atomic_tactic`
represent respectively the natural and integer numbers, the authorized
identificators and qualified names, Coq terms and patterns and all the atomic
tactics described in Chapter :ref:`tactics`. The syntax of :token:`cpattern` is
the same as that of terms, but it is extended with pattern matching
metavariables. In :token:`cpattern`, a pattern matching metavariable is
represented with the syntax :g:`?id` where :g:`id` is an :token:`ident`. The
notation :g:`_` can also be used to denote metavariable whose instance is
irrelevant. In the notation :g:`?id`, the identifier allows us to keep
instantiations and to make constraints whereas :g:`_` shows that we are not
interested in what will be matched. On the right hand side of pattern matching
clauses, the named metavariables are used without the question mark prefix. There
is also a special notation for second-order pattern matching problems: in an
applicative pattern of the form :g:`@?id id1 … idn`, the variable id matches any
complex expression with (possible) dependencies in the variables :g:`id1 … idn`
and returns a functional term of the form :g:`fun id1 … idn => term`.

The main entry of the grammar is :n:`@expr`. This language is used in proof
mode but it can also be used in toplevel definitions as shown below.

.. note::

   - The infix tacticals “… \|\| …”, “… + …”, and “… ; …” are associative.

   - In :token:`tacarg`, there is an overlap between qualid as a direct tactic
     argument and :token:`qualid` as a particular case of term. The resolution is
     done by first looking for a reference of the tactic language and if
     it fails, for a reference to a term. To force the resolution as a
     reference of the tactic language, use the form :g:`ltac:(@qualid)`. To
     force the resolution as a reference to a term, use the syntax
     :g:`(@qualid)`.

   - As shown by the figure, tactical ``\|\|`` binds more than the prefix
     tacticals try, repeat, do and abstract which themselves bind more
     than the postfix tactical “… ;[ … ]” which binds more than “… ; …”.

     For instance

     .. coqtop:: in

        try repeat tac1 || tac2; tac3; [tac31 | ... | tac3n]; tac4.

     is understood as

     .. coqtop:: in

        try (repeat (tac1 || tac2));
          ((tac3; [tac31 | ... | tac3n]); tac4).

.. productionlist::  coq
   expr              : `expr` ; `expr`
                     : | [> `expr` | ... | `expr` ]
                     : | `expr` ; [ `expr` | ... | `expr` ]
                     : | `tacexpr3`
   tacexpr3          : do (`natural` | `ident`) tacexpr3
                     : | progress `tacexpr3`
                     : | repeat `tacexpr3`
                     : | try `tacexpr3`
                     : | once `tacexpr3`
                     : | exactly_once `tacexpr3`
                     : | timeout (`natural` | `ident`) `tacexpr3`
                     : | time [`string`] `tacexpr3`
                     : | only `selector`: `tacexpr3`
                     : | `tacexpr2`
   tacexpr2          : `tacexpr1` || `tacexpr3`
                     : | `tacexpr1` + `tacexpr3`
                     : | tryif `tacexpr1` then `tacexpr1` else `tacexpr1`
                     : | `tacexpr1`
   tacexpr1          : fun `name` ... `name` => `atom`
                     : | let [rec] `let_clause` with ... with `let_clause` in `atom`
                     : | match goal with `context_rule` | ... | `context_rule` end
                     : | match reverse goal with `context_rule` | ... | `context_rule` end
                     : | match `expr` with `match_rule` | ... | `match_rule` end
                     : | lazymatch goal with `context_rule` | ... | `context_rule` end
                     : | lazymatch reverse goal with `context_rule` | ... | `context_rule` end
                     : | lazymatch `expr` with `match_rule` | ... | `match_rule` end
                     : | multimatch goal with `context_rule` | ... | `context_rule` end
                     : | multimatch reverse goal with `context_rule` | ... | `context_rule` end
                     : | multimatch `expr` with `match_rule` | ... | `match_rule` end
                     : | abstract `atom`
                     : | abstract `atom` using `ident`
                     : | first [ `expr` | ... | `expr` ]
                     : | solve [ `expr` | ... | `expr` ]
                     : | idtac [ `message_token` ... `message_token`]
                     : | fail [`natural`] [`message_token` ... `message_token`]
                     : | fresh [ `component` … `component` ]
                     : | context `ident` [`term`]
                     : | eval `redexpr` in `term`
                     : | type of `term`
                     : | constr : `term`
                     : | uconstr : `term`
                     : | type_term `term`
                     : | numgoals
                     : | guard `test`
                     : | assert_fails `tacexpr3`
                     : | assert_succeeds `tacexpr3`
                     : | `atomic_tactic`
                     : | `qualid` `tacarg` ... `tacarg`
                     : | `atom`
   atom              : `qualid`
                     : | ()
                     : | `integer`
                     : | ( `expr` )
   component : `string` | `qualid`
   message_token     : `string` | `ident` | `integer`
   tacarg            : `qualid`
                     : | ()
                     : | ltac : `atom`
                     : | `term`
   let_clause        : `ident` [`name` ... `name`] := `expr`
   context_rule      : `context_hyp`, ..., `context_hyp` |- `cpattern` => `expr`
                     : | `cpattern` => `expr`
                     : | |- `cpattern` => `expr`
                     : | _ => `expr`
   context_hyp       : `name` : `cpattern`
                     : | `name` := `cpattern` [: `cpattern`]
   match_rule        : `cpattern` => `expr`
                     : | context [ident] [ `cpattern` ] => `expr`
                     : | _ => `expr`
   test              : `integer` = `integer`
                     : | `integer` (< | <= | > | >=) `integer`
   selector          : [`ident`]
                     : | `integer`
                     : | (`integer` | `integer` - `integer`), ..., (`integer` | `integer` - `integer`)
   toplevel_selector : `selector`
                     : | all
                     : | par
                     : | !

.. productionlist:: coq
   top              : [Local] Ltac `ltac_def` with ... with `ltac_def`
   ltac_def         : `ident` [`ident` ... `ident`] := `expr`
                    : | `qualid` [`ident` ... `ident`] ::= `expr`

.. _ltac-semantics:

Semantics
---------

Tactic expressions can only be applied in the context of a proof. The
evaluation yields either a term, an integer or a tactic. Intermediate
results can be terms or integers but the final result must be a tactic
which is then applied to the focused goals.

There is a special case for ``match goal`` expressions of which the clauses
evaluate to tactics. Such expressions can only be used as end result of
a tactic expression (never as argument of a non-recursive local
definition or of an application).

The rest of this section explains the semantics of every construction of
|Ltac|.

Sequence
~~~~~~~~

A sequence is an expression of the following form:

.. tacn:: @expr__1 ; @expr__2
   :name: ltac-seq

   The expression :n:`@expr__1` is evaluated to :n:`v__1`, which must be
   a tactic value. The tactic :n:`v__1` is applied to the current goal,
   possibly producing more goals. Then :n:`@expr__2` is evaluated to
   produce :n:`v__2`, which must be a tactic value. The tactic
   :n:`v__2` is applied to all the goals produced by the prior
   application. Sequence is associative.

Local application of tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Different tactics can be applied to the different goals using the
following form:

.. tacn:: [> {*| @expr }]
   :name: [> ... | ... | ... ] (dispatch)

   The expressions :n:`@expr__i` are evaluated to :n:`v__i`, for
   i = 0, ..., n and all have to be tactics. The :n:`v__i` is applied to the
   i-th goal, for i = 1, ..., n. It fails if the number of focused goals is not
   exactly n.

   .. note::

      If no tactic is given for the i-th goal, it behaves as if the tactic idtac
      were given. For instance, ``[> | auto]`` is a shortcut for ``[> idtac | auto
      ]``.

   .. tacv:: [> {*| @expr__i} | @expr .. | {*| @expr__j}]

      In this variant, :n:`@expr` is used for each goal coming after those
      covered by the list of :n:`@expr__i` but before those covered by the
      list of :n:`@expr__j`.

   .. tacv:: [> {*| @expr} | .. | {*| @expr}]

      In this variant, idtac is used for the goals not covered by the two lists of
      :n:`@expr`.

   .. tacv:: [> @expr .. ]

      In this variant, the tactic :n:`@expr` is applied independently to each of
      the goals, rather than globally. In particular, if there are no goals, the
      tactic is not run at all. A tactic which expects multiple goals, such as
      ``swap``, would act as if a single goal is focused.

   .. tacv:: @expr__0 ; [{*| @expr__i}]

      This variant of local tactic application is paired with a sequence. In this
      variant, there must be as many :n:`@expr__i` as goals generated
      by the application of :n:`@expr__0` to each of the individual goals
      independently. All the above variants work in this form too.
      Formally, :n:`@expr ; [ ... ]` is equivalent to :n:`[> @expr ; [> ... ] .. ]`.

.. _goal-selectors:

Goal selectors
~~~~~~~~~~~~~~

We can restrict the application of a tactic to a subset of the currently
focused goals with:

.. tacn:: @toplevel_selector : @expr
   :name: ... : ... (goal selector)

   We can also use selectors as a tactical, which allows to use them nested
   in a tactic expression, by using the keyword ``only``:

   .. tacv:: only @selector : @expr
      :name: only ... : ...

      When selecting several goals, the tactic :token:`expr` is applied globally to all
      selected goals.

   .. tacv:: [@ident] : @expr

      In this variant, :token:`expr` is applied locally to a goal previously named
      by the user (see :ref:`existential-variables`).

   .. tacv:: @num : @expr

      In this variant, :token:`expr` is applied locally to the :token:`num`-th goal.

   .. tacv:: {+, @num-@num} : @expr

      In this variant, :n:`@expr` is applied globally to the subset of goals
      described by the given ranges. You can write a single ``n`` as a shortcut
      for ``n-n`` when specifying multiple ranges.

   .. tacv:: all: @expr
      :name: all: ...

      In this variant, :token:`expr` is applied to all focused goals. ``all:`` can only
      be used at the toplevel of a tactic expression.

   .. tacv:: !: @expr

      In this variant, if exactly one goal is focused, :token:`expr` is
      applied to it. Otherwise the tactic fails. ``!:`` can only be
      used at the toplevel of a tactic expression.

   .. tacv:: par: @expr
      :name: par: ...

      In this variant, :n:`@expr` is applied to all focused goals in parallel.
      The number of workers can be controlled via the command line option
      ``-async-proofs-tac-j`` taking as argument the desired number of workers.
      Limitations: ``par:`` only works on goals containing no existential
      variables and :n:`@expr` must either solve the goal completely or do
      nothing (i.e. it cannot make some progress). ``par:`` can only be used at
      the toplevel of a tactic expression.

   .. exn:: No such goal.
      :name: No such goal. (Goal selector)
      :undocumented:

   .. TODO change error message index entry

For loop
~~~~~~~~

There is a for loop that repeats a tactic :token:`num` times:

.. tacn:: do @num @expr
   :name: do

   :n:`@expr` is evaluated to ``v`` which must be a tactic value. This tactic
   value ``v`` is applied :token:`num` times. Supposing :token:`num` > 1, after the
   first application of ``v``, ``v`` is applied, at least once, to the generated
   subgoals and so on. It fails if the application of ``v`` fails before the num
   applications have been completed.

Repeat loop
~~~~~~~~~~~

We have a repeat loop with:

.. tacn:: repeat @expr
   :name: repeat

   :n:`@expr` is evaluated to ``v``. If ``v`` denotes a tactic, this tactic is
   applied to each focused goal independently. If the application succeeds, the
   tactic is applied recursively to all the generated subgoals until it eventually
   fails. The recursion stops in a subgoal when the tactic has failed *to make
   progress*. The tactic :n:`repeat @expr` itself never fails.

Error catching
~~~~~~~~~~~~~~

We can catch the tactic errors with:

.. tacn:: try @expr
   :name: try

   :n:`@expr` is evaluated to ``v`` which must be a tactic value. The tactic
   value ``v`` is applied to each focused goal independently. If the application of
   ``v`` fails in a goal, it catches the error and leaves the goal unchanged. If the
   level of the exception is positive, then the exception is re-raised with its
   level decremented.

Detecting progress
~~~~~~~~~~~~~~~~~~

We can check if a tactic made progress with:

.. tacn:: progress expr
   :name: progress

   :n:`@expr` is evaluated to v which must be a tactic value. The tactic value ``v``
   is applied to each focued subgoal independently. If the application of ``v``
   to one of the focused subgoal produced subgoals equal to the initial
   goals (up to syntactical equality), then an error of level 0 is raised.

   .. exn:: Failed to progress.
      :undocumented:

Backtracking branching
~~~~~~~~~~~~~~~~~~~~~~

We can branch with the following structure:

.. tacn:: @expr__1 + @expr__2
   :name: + (backtracking branching)

   :n:`@expr__1` and :n:`@expr__2` are evaluated respectively to :n:`v__1` and
   :n:`v__2` which must be tactic values. The tactic value :n:`v__1` is applied to
   each focused goal independently and if it fails or a later tactic fails, then
   the proof backtracks to the current goal and :n:`v__2` is applied.

   Tactics can be seen as having several successes. When a tactic fails it
   asks for more successes of the prior tactics.
   :n:`@expr__1 + @expr__2` has all the successes of :n:`v__1` followed by all the
   successes of :n:`v__2`. Algebraically,
   :n:`(@expr__1 + @expr__2); @expr__3 = (@expr__1; @expr__3) + (@expr__2; @expr__3)`.

   Branching is left-associative.

First tactic to work
~~~~~~~~~~~~~~~~~~~~

Backtracking branching may be too expensive. In this case we may
restrict to a local, left biased, branching and consider the first
tactic to work (i.e. which does not fail) among a panel of tactics:

.. tacn:: first [{*| @expr}]
   :name: first

   The :n:`@expr__i` are evaluated to :n:`v__i` and :n:`v__i` must be
   tactic values for i = 1, ..., n. Supposing n > 1,
   :n:`first [@expr__1 | ... | @expr__n]` applies :n:`v__1` in each
   focused goal independently and stops if it succeeds; otherwise it
   tries to apply :n:`v__2` and so on. It fails when there is no
   applicable tactic. In other words,
   :n:`first [@expr__1 | ... | @expr__n]` behaves, in each goal, as the first
   :n:`v__i` to have *at least* one success.

   .. exn:: No applicable tactic.
      :undocumented:

   .. tacv:: first @expr

      This is an |Ltac| alias that gives a primitive access to the first
      tactical as an |Ltac| definition without going through a parsing rule. It
      expects to be given a list of tactics through a ``Tactic Notation``,
      allowing to write notations of the following form:

      .. example::

         .. coqtop:: in

            Tactic Notation "foo" tactic_list(tacs) := first tacs.

Left-biased branching
~~~~~~~~~~~~~~~~~~~~~

Yet another way of branching without backtracking is the following
structure:

.. tacn:: @expr__1 || @expr__2
   :name: || (left-biased branching)

   :n:`@expr__1` and :n:`@expr__2` are evaluated respectively to :n:`v__1` and
   :n:`v__2` which must be tactic values. The tactic value :n:`v__1` is
   applied in each subgoal independently and if it fails *to progress* then
   :n:`v__2` is applied. :n:`@expr__1 || @expr__2` is
   equivalent to :n:`first [ progress @expr__1 | @expr__2 ]` (except that
   if it fails, it fails like :n:`v__2`). Branching is left-associative.

Generalized biased branching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The tactic

.. tacn:: tryif @expr__1 then @expr__2 else @expr__3
   :name: tryif

   is a generalization of the biased-branching tactics above. The
   expression :n:`@expr__1` is evaluated to :n:`v__1`, which is then
   applied to each subgoal independently. For each goal where :n:`v__1`
   succeeds at least once, :n:`@expr__2` is evaluated to :n:`v__2` which
   is then applied collectively to the generated subgoals. The :n:`v__2`
   tactic can trigger backtracking points in :n:`v__1`: where :n:`v__1`
   succeeds at least once,
   :n:`tryif @expr__1 then @expr__2 else @expr__3` is equivalent to
   :n:`v__1; v__2`. In each of the goals where :n:`v__1` does not succeed at least
   once, :n:`@expr__3` is evaluated in :n:`v__3` which is is then applied to the
   goal.

Soft cut
~~~~~~~~

Another way of restricting backtracking is to restrict a tactic to a
single success *a posteriori*:

.. tacn:: once @expr
   :name: once

   :n:`@expr` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied but only its first success is used. If ``v`` fails,
   :n:`once @expr` fails like ``v``. If ``v`` has at least one success,
   :n:`once @expr` succeeds once, but cannot produce more successes.

Checking the successes
~~~~~~~~~~~~~~~~~~~~~~

Coq provides an experimental way to check that a tactic has *exactly
one* success:

.. tacn:: exactly_once @expr
   :name: exactly_once

   :n:`@expr` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied if it has at most one success. If ``v`` fails,
   :n:`exactly_once @expr` fails like ``v``. If ``v`` has a exactly one success,
   :n:`exactly_once @expr` succeeds like ``v``. If ``v`` has two or more
   successes, exactly_once expr fails.

   .. warning::

      The experimental status of this tactic pertains to the fact if ``v``
      performs side effects, they may occur in an unpredictable way. Indeed,
      normally ``v`` would only be executed up to the first success until
      backtracking is needed, however exactly_once needs to look ahead to see
      whether a second success exists, and may run further effects
      immediately.

   .. exn:: This tactic has more than one success.
      :undocumented:

Checking the failure
~~~~~~~~~~~~~~~~~~~~

Coq provides a derived tactic to check that a tactic *fails*:

.. tacn:: assert_fails @expr
   :name: assert_fails

   This behaves like :n:`tryif @expr then fail 0 tac "succeeds" else idtac`.

Checking the success
~~~~~~~~~~~~~~~~~~~~

Coq provides a derived tactic to check that a tactic has *at least one*
success:

.. tacn:: assert_succeeds @expr
   :name: assert_succeeds

   This behaves like
   :n:`tryif (assert_fails tac) then fail 0 tac "fails" else idtac`.

Solving
~~~~~~~

We may consider the first to solve (i.e. which generates no subgoal)
among a panel of tactics:

.. tacn:: solve [{*| @expr}]
   :name: solve

   The :n:`@expr__i` are evaluated to :n:`v__i` and :n:`v__i` must be
   tactic values, for i = 1, ..., n. Supposing n > 1,
   :n:`solve [@expr__1 | ... | @expr__n]` applies :n:`v__1` to
   each goal independently and stops if it succeeds; otherwise it tries to
   apply :n:`v__2` and so on. It fails if there is no solving tactic.

   .. exn:: Cannot solve the goal.
      :undocumented:

   .. tacv:: solve @expr

      This is an |Ltac| alias that gives a primitive access to the :n:`solve:`
      tactical. See the :n:`first` tactical for more information.

Identity
~~~~~~~~

The constant :n:`idtac` is the identity tactic: it leaves any goal unchanged but
it appears in the proof script.

.. tacn:: idtac {* message_token}
   :name: idtac

   This prints the given tokens. Strings and integers are printed
   literally. If a (term) variable is given, its contents are printed.

Failing
~~~~~~~

.. tacn:: fail
   :name: fail

   This is the always-failing tactic: it does not solve any
   goal. It is useful for defining other tacticals since it can be caught by
   :tacn:`try`, :tacn:`repeat`, :tacn:`match goal`, or the branching tacticals.

   .. tacv:: fail @num

      The number is the failure level. If no level is specified, it defaults to 0.
      The level is used by :tacn:`try`, :tacn:`repeat`, :tacn:`match goal` and the branching
      tacticals. If 0, it makes :tacn:`match goal` consider the next clause
      (backtracking). If nonzero, the current :tacn:`match goal` block, :tacn:`try`,
      :tacn:`repeat`, or branching command is aborted and the level is decremented. In
      the case of :n:`+`, a nonzero level skips the first backtrack point, even if
      the call to :n:`fail @num` is not enclosed in a :n:`+` command,
      respecting the algebraic identity.

   .. tacv:: fail {* message_token}

      The given tokens are used for printing the failure message.

   .. tacv:: fail @num {* message_token}

      This is a combination of the previous variants.

   .. tacv:: gfail
      :name: gfail

      This variant fails even when used after :n:`;` and there are no goals left.
      Similarly, ``gfail`` fails even when used after ``all:`` and there are no
      goals left. See the example for clarification.

   .. tacv:: gfail {* message_token}
             gfail @num {* message_token}

      These variants fail with an error message or an error level even if
      there are no goals left. Be careful however if Coq terms have to be
      printed as part of the failure: term construction always forces the
      tactic into the goals, meaning that if there are no goals when it is
      evaluated, a tactic call like :n:`let x := H in fail 0 x` will succeed.

   .. exn:: Tactic Failure message (level @num).
      :undocumented:

   .. exn:: No such goal.
      :name: No such goal. (fail)
      :undocumented:

   .. example::

      .. coqtop:: all

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

Timeout
~~~~~~~

We can force a tactic to stop if it has not finished after a certain
amount of time:

.. tacn:: timeout @num @expr
   :name: timeout

   :n:`@expr` is evaluated to ``v`` which must be a tactic value. The tactic value
   ``v`` is applied normally, except that it is interrupted after :n:`@num` seconds
   if it is still running. In this case the outcome is a failure.

   .. warning::

      For the moment, timeout is based on elapsed time in seconds,
      which is very machine-dependent: a script that works on a quick machine
      may fail on a slow one. The converse is even possible if you combine a
      timeout with some other tacticals. This tactical is hence proposed only
      for convenience during debugging or other development phases, we strongly
      advise you to not leave any timeout in final scripts. Note also that
      this tactical isn’t available on the native Windows port of Coq.

Timing a tactic
~~~~~~~~~~~~~~~

A tactic execution can be timed:

.. tacn:: time @string @expr
   :name: time

   evaluates :n:`@expr` and displays the running time of the tactic expression, whether it
   fails or succeeds. In case of several successes, the time for each successive
   run is displayed. Time is in seconds and is machine-dependent. The :n:`@string`
   argument is optional. When provided, it is used to identify this particular
   occurrence of time.

Timing a tactic that evaluates to a term
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tactic expressions that produce terms can be timed with the experimental
tactic

.. tacn:: time_constr expr
   :name: time_constr

   which evaluates :n:`@expr ()` and displays the time the tactic expression
   evaluated, assuming successful evaluation. Time is in seconds and is
   machine-dependent.

   This tactic currently does not support nesting, and will report times
   based on the innermost execution. This is due to the fact that it is
   implemented using the following internal tactics:

   .. tacn:: restart_timer @string
      :name: restart_timer

      Reset a timer

   .. tacn:: finish_timing {? (@string)} @string
      :name: finish_timing

      Display an optionally named timer. The parenthesized string argument
      is also optional, and determines the label associated with the timer
      for printing.

   By copying the definition of :tacn:`time_constr` from the standard library,
   users can achive support for a fixed pattern of nesting by passing
   different :token:`string` parameters to :tacn:`restart_timer` and
   :tacn:`finish_timing` at each level of nesting.

   .. example::

      .. coqtop:: all

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
         Abort.

Local definitions
~~~~~~~~~~~~~~~~~

Local definitions can be done as follows:

.. tacn:: let @ident__1 := @expr__1 {* with @ident__i := @expr__i} in @expr
   :name: let ... := ...

   each :n:`@expr__i` is evaluated to :n:`v__i`, then, :n:`@expr` is evaluated
   by substituting :n:`v__i` to each occurrence of :n:`@ident__i`, for
   i = 1, ..., n. There are no dependencies between the :n:`@expr__i` and the
   :n:`@ident__i`.

   Local definitions can be made recursive by using :n:`let rec` instead of :n:`let`.
   In this latter case, the definitions are evaluated lazily so that the rec
   keyword can be used also in non-recursive cases so as to avoid the eager
   evaluation of local definitions.

   .. but rec changes the binding!!

Application
~~~~~~~~~~~

An application is an expression of the following form:

.. tacn:: @qualid {+ @tacarg}

   The reference :n:`@qualid` must be bound to some defined tactic definition
   expecting at least as many arguments as the provided :n:`tacarg`. The
   expressions :n:`@expr__i` are evaluated to :n:`v__i`, for i = 1, ..., n.

   .. what expressions ??

Function construction
~~~~~~~~~~~~~~~~~~~~~

A parameterized tactic can be built anonymously (without resorting to
local definitions) with:

.. tacn:: fun {+ @ident} => @expr

   Indeed, local definitions of functions are a syntactic sugar for binding
   a :n:`fun` tactic to an identifier.

Pattern matching on terms
~~~~~~~~~~~~~~~~~~~~~~~~~

We can carry out pattern matching on terms with:

.. tacn:: match @expr with {+| @cpattern__i => @expr__i} end

   The expression :n:`@expr` is evaluated and should yield a term which is
   matched against :n:`cpattern__1`. The matching is non-linear: if a
   metavariable occurs more than once, it should match the same expression
   every time. It is first-order except on the variables of the form :n:`@?id`
   that occur in head position of an application. For these variables, the
   matching is second-order and returns a functional term.

   Alternatively, when a metavariable of the form :n:`?id` occurs under binders,
   say :n:`x__1, …, x__n` and the expression matches, the
   metavariable is instantiated by a term which can then be used in any
   context which also binds the variables :n:`x__1, …, x__n` with
   same types. This provides with a primitive form of matching under
   context which does not require manipulating a functional term.

   If the matching with :n:`@cpattern__1` succeeds, then :n:`@expr__1` is
   evaluated into some value by substituting the pattern matching
   instantiations to the metavariables. If :n:`@expr__1` evaluates to a
   tactic and the match expression is in position to be applied to a goal
   (e.g. it is not bound to a variable by a :n:`let in`), then this tactic is
   applied. If the tactic succeeds, the list of resulting subgoals is the
   result of the match expression. If :n:`@expr__1` does not evaluate to a
   tactic or if the match expression is not in position to be applied to a
   goal, then the result of the evaluation of :n:`@expr__1` is the result
   of the match expression.

   If the matching with :n:`@cpattern__1` fails, or if it succeeds but the
   evaluation of :n:`@expr__1` fails, or if the evaluation of
   :n:`@expr__1` succeeds but returns a tactic in execution position whose
   execution fails, then :n:`cpattern__2` is used and so on. The pattern
   :n:`_` matches any term and shadows all remaining patterns if any. If all
   clauses fail (in particular, there is no pattern :n:`_`) then a
   no-matching-clause error is raised.

   Failures in subsequent tactics do not cause backtracking to select new
   branches or inside the right-hand side of the selected branch even if it
   has backtracking points.

   .. exn:: No matching clauses for match.

      No pattern can be used and, in particular, there is no :n:`_` pattern.

   .. exn:: Argument of match does not evaluate to a term.

      This happens when :n:`@expr` does not denote a term.

   .. tacv:: multimatch @expr with {+| @cpattern__i => @expr__i} end

      Using multimatch instead of match will allow subsequent tactics to
      backtrack into a right-hand side tactic which has backtracking points
      left and trigger the selection of a new matching branch when all the
      backtracking points of the right-hand side have been consumed.

      The syntax :n:`match …` is, in fact, a shorthand for :n:`once multimatch …`.

   .. tacv:: lazymatch @expr with {+| @cpattern__i => @expr__i} end

      Using lazymatch instead of match will perform the same pattern
      matching procedure but will commit to the first matching branch
      rather than trying a new matching if the right-hand side fails. If
      the right-hand side of the selected branch is a tactic with
      backtracking points, then subsequent failures cause this tactic to
      backtrack.

   .. tacv:: context @ident [@cpattern]

      This special form of patterns matches any term with a subterm matching
      cpattern. If there is a match, the optional :n:`@ident` is assigned the "matched
      context", i.e. the initial term where the matched subterm is replaced by a
      hole. The example below will show how to use such term contexts.

      If the evaluation of the right-hand-side of a valid match fails, the next
      matching subterm is tried. If no further subterm matches, the next clause
      is tried. Matching subterms are considered top-bottom and from left to
      right (with respect to the raw printing obtained by setting option
      :flag:`Printing All`).

   .. example::

      .. coqtop:: all

         Ltac f x :=
           match x with
             context f [S ?X] =>
             idtac X;                    (* To display the evaluation order *)
             assert (p := eq_refl 1 : X=1);    (* To filter the case X=1 *)
             let x:= context f[O] in assert (x=O) (* To observe the context *)
           end.
         Goal True.
         f (3+4).

.. _ltac-match-goal:

Pattern matching on goals
~~~~~~~~~~~~~~~~~~~~~~~~~

We can perform pattern matching on goals using the following expression:

.. we should provide the full grammar here

.. tacn:: match goal with {+| {+ hyp} |- @cpattern => @expr } | _ => @expr end
   :name: match goal

   If each hypothesis pattern :n:`hyp`\ :sub:`1,i`, with i = 1, ..., m\ :sub:`1` is
   matched (non-linear first-order unification) by a hypothesis of the
   goal and if :n:`cpattern_1` is matched by the conclusion of the goal,
   then :n:`@expr__1` is evaluated to :n:`v__1` by substituting the
   pattern matching to the metavariables and the real hypothesis names
   bound to the possible hypothesis names occurring in the hypothesis
   patterns. If :n:`v__1` is a tactic value, then it is applied to the
   goal. If this application fails, then another combination of hypotheses
   is tried with the same proof context pattern. If there is no other
   combination of hypotheses then the second proof context pattern is tried
   and so on. If the next to last proof context pattern fails then
   the last :n:`@expr` is evaluated to :n:`v` and :n:`v` is
   applied. Note also that matching against subterms (using the :n:`context
   @ident [ @cpattern ]`) is available and is also subject to yielding several
   matchings.

   Failures in subsequent tactics do not cause backtracking to select new
   branches or combinations of hypotheses, or inside the right-hand side of
   the selected branch even if it has backtracking points.

   .. exn:: No matching clauses for match goal.

      No clause succeeds, i.e. all matching patterns, if any, fail at the
      application of the right-hand-side.

   .. note::

      It is important to know that each hypothesis of the goal can be matched
      by at most one hypothesis pattern. The order of matching is the
      following: hypothesis patterns are examined from right to left
      (i.e. hyp\ :sub:`i,m`\ :sub:`i`` before hyp\ :sub:`i,1`). For each
      hypothesis pattern, the goal hypotheses are matched in order (newest
      first), but it possible to reverse this order (oldest first)
      with the :n:`match reverse goal with` variant.

   .. tacv:: multimatch goal with {+| {+ hyp} |- @cpattern => @expr } | _ => @expr end

      Using :n:`multimatch` instead of :n:`match` will allow subsequent tactics
      to backtrack into a right-hand side tactic which has backtracking points
      left and trigger the selection of a new matching branch or combination of
      hypotheses when all the backtracking points of the right-hand side have
      been consumed.

      The syntax :n:`match [reverse] goal …` is, in fact, a shorthand for
      :n:`once multimatch [reverse] goal …`.

   .. tacv:: lazymatch goal with {+| {+ hyp} |- @cpattern => @expr } | _ => @expr end

      Using lazymatch instead of match will perform the same pattern matching
      procedure but will commit to the first matching branch with the first
      matching combination of hypotheses rather than trying a new matching if
      the right-hand side fails. If the right-hand side of the selected branch
      is a tactic with backtracking points, then subsequent failures cause
      this tactic to backtrack.

Filling a term context
~~~~~~~~~~~~~~~~~~~~~~

The following expression is not a tactic in the sense that it does not
produce subgoals but generates a term to be used in tactic expressions:

.. tacn:: context @ident [@expr]

   :n:`@ident` must denote a context variable bound by a context pattern of a
   match expression. This expression evaluates replaces the hole of the
   value of :n:`@ident` by the value of :n:`@expr`.

   .. exn:: Not a context variable.
      :undocumented:

   .. exn:: Unbound context identifier @ident.
      :undocumented:

Generating fresh hypothesis names
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tactics sometimes have to generate new names for hypothesis. Letting the
system decide a name with the intro tactic is not so good since it is
very awkward to retrieve the name the system gave. The following
expression returns an identifier:

.. tacn:: fresh {* component}

   It evaluates to an identifier unbound in the goal. This fresh identifier
   is obtained by concatenating the value of the :n:`@component`\ s (each of them
   is, either a :n:`@qualid` which has to refer to a (unqualified) name, or
   directly a name denoted by a :n:`@string`).

   If the resulting name is already used, it is padded with a number so that it
   becomes fresh. If no component is given, the name is a fresh derivative of
   the name ``H``.

Computing in a constr
~~~~~~~~~~~~~~~~~~~~~

Evaluation of a term can be performed with:

.. tacn:: eval @redexpr in @term

   where :n:`@redexpr` is a reduction tactic among :tacn:`red`, :tacn:`hnf`,
   :tacn:`compute`, :tacn:`simpl`, :tacn:`cbv`, :tacn:`lazy`, :tacn:`unfold`,
   :tacn:`fold`, :tacn:`pattern`.

Recovering the type of a term
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: type of @term

   This tactic returns the type of :token:`term`.

Manipulating untyped terms
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: uconstr : @term

   The terms built in |Ltac| are well-typed by default. It may not be
   appropriate for building large terms using a recursive |Ltac| function: the
   term has to be entirely type checked at each step, resulting in potentially
   very slow behavior. It is possible to build untyped terms using |Ltac| with
   the :n:`uconstr : @term` syntax.

.. tacn:: type_term @term

   An untyped term, in |Ltac|, can contain references to hypotheses or to
   |Ltac| variables containing typed or untyped terms. An untyped term can be
   type checked using the function type_term whose argument is parsed as an
   untyped term and returns a well-typed term which can be used in tactics.

Untyped terms built using :n:`uconstr :` can also be used as arguments to the
:tacn:`refine` tactic. In that case the untyped term is type
checked against the conclusion of the goal, and the holes which are not solved
by the typing procedure are turned into new subgoals.

Counting the goals
~~~~~~~~~~~~~~~~~~

.. tacn:: numgoals

   The number of goals under focus can be recovered using the :n:`numgoals`
   function. Combined with the guard command below, it can be used to
   branch over the number of goals produced by previous tactics.

   .. example::

      .. coqtop:: in

         Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".

         Goal True /\ True /\ True.
         split;[|split].

      .. coqtop:: all

         all:pr_numgoals.

Testing boolean expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: guard @test
   :name: guard

   The :tacn:`guard` tactic tests a boolean expression, and fails if the expression
   evaluates to false. If the expression evaluates to true, it succeeds
   without affecting the proof.

   The accepted tests are simple integer comparisons.

   .. example::

      .. coqtop:: in

         Goal True /\ True /\ True.
         split;[|split].

      .. coqtop:: all

         all:let n:= numgoals in guard n<4.
         Fail all:let n:= numgoals in guard n=2.

   .. exn:: Condition not satisfied.
      :undocumented:

Proving a subgoal as a separate lemma
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: abstract @expr
   :name: abstract

   From the outside, :n:`abstract @expr` is the same as :n:`solve @expr`.
   Internally it saves an auxiliary lemma called ``ident_subproofn`` where
   ``ident`` is the name of the current goal and ``n`` is chosen so that this is
   a fresh name. Such an auxiliary lemma is inlined in the final proof term.

   This tactical is useful with tactics such as :tacn:`omega` or
   :tacn:`discriminate` that generate huge proof terms. With that tool the user
   can avoid the explosion at time of the Save command without having to cut
   manually the proof in smaller lemmas.

   It may be useful to generate lemmas minimal w.r.t. the assumptions they
   depend on. This can be obtained thanks to the option below.

   .. tacv:: abstract @expr using @ident

      Give explicitly the name of the auxiliary lemma.

      .. warning::

         Use this feature at your own risk; explicitly named and reused subterms
         don’t play well with asynchronous proofs.

   .. tacv:: transparent_abstract @expr
      :name: transparent_abstract

      Save the subproof in a transparent lemma rather than an opaque one.

      .. warning::

         Use this feature at your own risk; building computationally relevant
         terms with tactics is fragile.

   .. tacv:: transparent_abstract @expr using @ident

      Give explicitly the name of the auxiliary transparent lemma.

      .. warning::

         Use this feature at your own risk; building computationally relevant terms
         with tactics is fragile, and explicitly named and reused subterms
         don’t play well with asynchronous proofs.

   .. exn:: Proof is not complete.
      :name: Proof is not complete. (abstract)
      :undocumented:

Tactic toplevel definitions
---------------------------

Defining |Ltac| functions
~~~~~~~~~~~~~~~~~~~~~~~~~

Basically, |Ltac| toplevel definitions are made as follows:

.. cmd:: Ltac @ident {* @ident} := @expr

   This defines a new |Ltac| function that can be used in any tactic
   script or new |Ltac| toplevel definition.

   .. note::

      The preceding definition can equivalently be written:

      :n:`Ltac @ident := fun {+ @ident} => @expr`

   Recursive and mutual recursive function definitions are also possible
   with the syntax:

   .. cmdv:: Ltac @ident {* @ident} {* with @ident {* @ident}} := @expr

      It is also possible to *redefine* an existing user-defined tactic using the syntax:

   .. cmdv:: Ltac @qualid {* @ident} ::= @expr

      A previous definition of qualid must exist in the environment. The new
      definition will always be used instead of the old one and it goes across
      module boundaries.

   If preceded by the keyword Local the tactic definition will not be
   exported outside the current module.

Printing |Ltac| tactics
~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Ltac @qualid

   Defined |Ltac| functions can be displayed using this command.

.. cmd:: Print Ltac Signatures

   This command displays a list of all user-defined tactics, with their arguments.

Debugging |Ltac| tactics
------------------------

Info trace
~~~~~~~~~~

.. cmd:: Info @num @expr
   :name: Info

   This command can be used to print the trace of the path eventually taken by an
   |Ltac| script. That is, the list of executed tactics, discarding
   all the branches which have failed. To that end the :cmd:`Info` command can be
   used with the following syntax.


   The number :n:`@num` is the unfolding level of tactics in the trace. At level
   0, the trace contains a sequence of tactics in the actual script, at level 1,
   the trace will be the concatenation of the traces of these tactics, etc…

   .. example::

      .. coqtop:: in reset

         Ltac t x := exists x; reflexivity.
         Goal exists n, n=0.

      .. coqtop:: all

         Info 0 t 1||t 0.

      .. coqtop:: in

         Undo.

      .. coqtop:: all

         Info 1 t 1||t 0.

   The trace produced by :cmd:`Info` tries its best to be a reparsable
   |Ltac| script, but this goal is not achievable in all generality.
   So some of the output traces will contain oddities.

   As an additional help for debugging, the trace produced by :cmd:`Info` contains
   (in comments) the messages produced by the :tacn:`idtac` tactical at the right
   position in the script. In particular, the calls to idtac in branches which failed are
   not printed.

   .. opt:: Info Level @num
      :name: Info Level

      This option is an alternative to the :cmd:`Info` command.

      This will automatically print the same trace as :n:`Info @num` at each
      tactic call. The unfolding level can be overridden by a call to the
      :cmd:`Info` command.

Interactive debugger
~~~~~~~~~~~~~~~~~~~~

.. flag:: Ltac Debug

   This option governs the step-by-step debugger that comes with the |Ltac| interpreter

When the debugger is activated, it stops at every step of the evaluation of
the current |Ltac| expression and prints information on what it is doing.
The debugger stops, prompting for a command which can be one of the
following:

+-----------------+-----------------------------------------------+
| simple newline: | go to the next step                           |
+-----------------+-----------------------------------------------+
| h:              | get help                                      |
+-----------------+-----------------------------------------------+
| x:              | exit current evaluation                       |
+-----------------+-----------------------------------------------+
| s:              | continue current evaluation without stopping  |
+-----------------+-----------------------------------------------+
| r n:            | advance n steps further                       |
+-----------------+-----------------------------------------------+
| r string:       | advance up to the next call to “idtac string” |
+-----------------+-----------------------------------------------+

.. exn:: Debug mode not available in the IDE
   :undocumented:

A non-interactive mode for the debugger is available via the option:

.. flag:: Ltac Batch Debug

   This option has the effect of presenting a newline at every prompt, when
   the debugger is on. The debug log thus created, which does not require
   user input to generate when this option is set, can then be run through
   external tools such as diff.

Profiling |Ltac| tactics
~~~~~~~~~~~~~~~~~~~~~~~~

It is possible to measure the time spent in invocations of primitive
tactics as well as tactics defined in |Ltac| and their inner
invocations. The primary use is the development of complex tactics,
which can sometimes be so slow as to impede interactive usage. The
reasons for the performence degradation can be intricate, like a slowly
performing |Ltac| match or a sub-tactic whose performance only
degrades in certain situations. The profiler generates a call tree and
indicates the time spent in a tactic depending on its calling context. Thus
it allows to locate the part of a tactic definition that contains the
performance issue.

.. flag:: Ltac Profiling

   This option enables and disables the profiler.

.. cmd:: Show Ltac Profile

   Prints the profile

   .. cmdv:: Show Ltac Profile @string

      Prints a profile for all tactics that start with :n:`@string`. Append a period
      (.) to the string if you only want exactly that name.

.. cmd:: Reset Ltac Profile

   Resets the profile, that is, deletes all accumulated information.

   .. warning::

      Backtracking across a :cmd:`Reset Ltac Profile` will not restore the information.

.. coqtop:: reset in

   Require Import Coq.omega.Omega.

   Ltac mytauto := tauto.
   Ltac tac := intros; repeat split; omega || mytauto.

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

.. coqtop:: all

  Set Ltac Profiling.
  tac.
  Show Ltac Profile.
  Show Ltac Profile "omega".

.. coqtop:: in

   Abort.
   Unset Ltac Profiling.

.. tacn:: start ltac profiling
   :name: start ltac profiling

   This tactic behaves like :tacn:`idtac` but enables the profiler.

.. tacn:: stop ltac profiling
   :name: stop ltac profiling

   Similarly to :tacn:`start ltac profiling`, this tactic behaves like
   :tacn:`idtac`. Together, they allow you to exclude parts of a proof script
   from profiling.

.. tacn:: reset ltac profile
   :name: reset ltac profile

   This tactic behaves like the corresponding vernacular command
   and allow displaying and resetting the profile from tactic scripts for
   benchmarking purposes.

.. tacn:: show ltac profile
   :name: show ltac profile

   This tactic behaves like the corresponding vernacular command
   and allow displaying and resetting the profile from tactic scripts for
   benchmarking purposes.

.. tacn:: show ltac profile @string
   :name: show ltac profile

   This tactic behaves like the corresponding vernacular command
   and allow displaying and resetting the profile from tactic scripts for
   benchmarking purposes.

You can also pass the ``-profile-ltac`` command line option to ``coqc``, which
turns the :flag:`Ltac Profiling` option on at the beginning of each document,
and performs a :cmd:`Show Ltac Profile` at the end.

.. warning::

   Note that the profiler currently does not handle backtracking into
   multi-success tactics, and issues a warning to this effect in many cases
   when such backtracking occurs.

Run-time optimization tactic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. tacn:: optimize_heap
   :name: optimize_heap

   This tactic behaves like :n:`idtac`, except that running it compacts the
   heap in the OCaml run-time system. It is analogous to the Vernacular
   command :cmd:`Optimize Heap`.
