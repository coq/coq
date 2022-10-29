.. _tactics:

Tactics
========

Tactics specify how to transform the :term:`proof state` of an
incomplete proof to eventually generate a complete proof.

Proofs can be developed in two basic ways: In :gdef:`forward reasoning`,
the proof begins by proving simple statements that are then combined to prove the
theorem statement as the last step of the proof. With forward reasoning,
for example,
the proof of `A /\\ B` would begin with proofs of `A` and `B`, which are
then used to prove `A /\\ B`.  Forward reasoning is probably the most common
approach in human-generated proofs.

In :gdef:`backward reasoning`, the proof begins with the theorem statement
as the goal, which is then gradually transformed until every subgoal generated
along the way has been proven.  In this case, the proof of `A /\\ B` begins
with that formula as the goal.  This can be transformed into two subgoals,
`A` and `B`, followed by the proofs of `A` and `B`.  Coq and its tactics
use backward reasoning.

A tactic may fully prove a goal, in which case the goal is removed
from the proof state.
More commonly, a tactic replaces a goal with one or more :term:`subgoals <subgoal>`.
(We say that a tactic reduces a goal to its subgoals.)

Most tactics require specific elements or preconditions to reduce a goal;
they display error messages if they can't be applied to the goal.
A few tactics, such as :tacn:`auto`, don't fail even if the proof state
is unchanged.

Goals are identified by number. The current goal is number
1. Tactics are applied to the current goal by default.  (The
default can be changed with the :opt:`Default Goal Selector`
option.)  They can
be applied to another goal or to multiple goals with a
:ref:`goal selector <goal-selectors>` such as :n:`2: @tactic`.

This chapter describes many of the most common built-in tactics.
Built-in tactics can be combined to form tactic expressions, which are
described in the :ref:`Ltac` chapter.  Since tactic expressions can
be used anywhere that a built-in tactic can be used, "tactic" may
refer to both built-in tactics and tactic expressions.

Common elements of tactics
--------------------------

Reserved keywords
~~~~~~~~~~~~~~~~~

The tactics described in this chapter reserve the following keywords::

  by using

Thus, these keywords cannot be used as identifiers. It also declares
the following character sequences as tokens::

  ** [= |-

.. _invocation-of-tactics:

Invocation of tactics
~~~~~~~~~~~~~~~~~~~~~

A tactic is applied as an ordinary command. It may be preceded by a
goal selector (see Section :ref:`goal-selectors`). If no selector is
specified, the default selector is used.

.. _tactic_invocation_grammar:

  .. prodn::
     tactic_invocation ::= @toplevel_selector : @tactic.
     | @tactic.

.. todo: fully describe selectors.  At the moment, ltac has a fairly complete description

.. todo: mention selectors can be applied to some commands, such as
   Check, Search, SearchPattern, SearchRewrite.

.. opt:: Default Goal Selector "@toplevel_selector"
   :name: Default Goal Selector

   This :term:`option` controls the default selector, used when no selector is
   specified when applying a tactic. The initial value is 1, hence the
   tactics are, by default, applied to the first goal.

   Using value ``all`` will make it so that tactics are, by default,
   applied to every goal simultaneously. Then, to apply a tactic tac
   to the first goal only, you can write ``1:tac``.

   Using value ``!`` enforces that all tactics are used either on a
   single focused goal or with a local selector (’’strict focusing
   mode’’).

   Although other selectors are available, only ``all``, ``!`` or a
   single natural number are valid default goal selectors.

.. _bindings:

Bindings
~~~~~~~~

Tactics that take a term as an argument may also accept :token:`bindings`
to instantiate some parameters of the term by name or position.
The general form of a term with :token:`bindings` is
:n:`@term__tac with @bindings` where :token:`bindings` can take two different forms:

  .. insertprodn bindings bindings

  .. prodn::
     bindings ::= {+ ( {| @ident | @natural } := @term ) }
     | {+ @one_term }

+ In the first form, if an :token:`ident` is specified, it must be bound in the
  type of :n:`@term` and provides the tactic with an instance for the
  parameter of this name. If a :token:`natural` is specified, it refers to
  the ``n``-th non-dependent premise of :n:`@term__tac`.

  .. exn:: No such binder.
     :undocumented:

+ In the second form, the interpretation of the :token:`one_term`\s depend on which
  tactic they appear in.  For :tacn:`induction`, :tacn:`destruct`, :tacn:`elim`
  and :tacn:`case`, the :token:`one_term`\s
  provide instances for all the dependent products in the type of :n:`@term__tac` while in
  the case of :tacn:`apply`, or of :tacn:`constructor` and its variants, only instances
  for the dependent products that are not bound in the conclusion of :n:`@term__tac`
  are required.

  .. exn:: Not the right number of missing arguments.
     :undocumented:

.. _intropatterns:

Intro patterns
~~~~~~~~~~~~~~

Intro patterns let you specify the name to assign to variables and hypotheses
introduced by tactics.  They also let you split an introduced hypothesis into
multiple hypotheses or subgoals.  Common tactics that accept intro patterns
include :tacn:`assert`, :tacn:`intros` and :tacn:`destruct`.

.. insertprodn intropattern equality_intropattern

.. prodn::
   intropattern ::= *
   | **
   | @simple_intropattern
   simple_intropattern ::= @simple_intropattern_closed {* % @term0 }
   simple_intropattern_closed ::= @naming_intropattern
   | _
   | @or_and_intropattern
   | @equality_intropattern
   naming_intropattern ::= @ident
   | ?
   | ?@ident
   or_and_intropattern ::= [ {*| {* @intropattern } } ]
   | ( {*, @simple_intropattern } )
   | ( @simple_intropattern & {+& @simple_intropattern } )
   equality_intropattern ::= ->
   | <-
   | [= {* @intropattern } ]

Note that the intro pattern syntax varies between tactics.
Most tactics use :n:`@simple_intropattern` in the grammar.
:tacn:`destruct`, :tacn:`edestruct`, :tacn:`induction`,
:tacn:`einduction`, :tacn:`case`, :tacn:`ecase` and the various
:tacn:`inversion` tactics use :n:`@or_and_intropattern`, while
:tacn:`intros` and :tacn:`eintros` use :n:`{* @intropattern }`.
The :n:`eqn:` construct in various tactics uses :n:`@naming_intropattern`.

**Naming patterns**

Use these elementary patterns to specify a name:

* :n:`@ident` — use the specified name
* :n:`?` — let Coq generate a fresh name
* :n:`?@ident` — generate a name that begins with :n:`@ident`
* :n:`_` — discard the matched part (unless it is required for another
  hypothesis)
* if a disjunction pattern omits a name, such as :g:`[|H2]`, Coq will choose a name

**Splitting patterns**

The most common splitting patterns are:

* split a hypothesis in the form :n:`A /\ B` into two
  hypotheses :g:`H1: A` and :g:`H2: B` using the pattern :g:`(H1 & H2)` or
  :g:`(H1, H2)` or :g:`[H1 H2]`.
  :ref:`Example <intropattern_conj_ex>`.  This also works on :n:`A <-> B`, which
  is just a notation representing :n:`(A -> B) /\ (B -> A)`.
* split a hypothesis in the form :g:`A \/ B` into two
  subgoals using the pattern :g:`[H1|H2]`.  The first subgoal will have the hypothesis
  :g:`H1: A` and the second subgoal will have the hypothesis :g:`H2: B`.
  :ref:`Example <intropattern_disj_ex>`
* split a hypothesis in either of the forms :g:`A /\ B` or :g:`A \/ B` using the pattern :g:`[]`.

Patterns can be nested: :n:`[[Ha|Hb] H]` can be used to split :n:`(A \/ B) /\ C`.

Note that there is no equivalent to intro patterns for goals.  For a goal :g:`A /\ B`,
use the :tacn:`split` tactic to replace the current goal with subgoals :g:`A` and :g:`B`.
For a goal :g:`A \/ B`, use :tacn:`left` to replace the current goal with :g:`A`, or
:tacn:`right` to replace the current goal with :g:`B`.

* :n:`( {+, @simple_intropattern}` ) — matches
  a product over an inductive type with a
  :ref:`single constructor <intropattern_cons_note>`.
  If the number of patterns
  equals the number of constructor arguments, then it applies the patterns only to
  the arguments, and
  :n:`( {+, @simple_intropattern} )` is equivalent to :n:`[{+ @simple_intropattern}]`.
  If the number of patterns equals the number of constructor arguments plus the number
  of :n:`let-ins`, the patterns are applied to the arguments and :n:`let-in` variables.

* :n:`( {+& @simple_intropattern} )` — matches a right-hand nested term that consists
  of one or more nested binary inductive types such as :g:`a1 OP1 a2 OP2 ...`
  (where the :g:`OPn` are right-associative).
  (If the :g:`OPn` are left-associative, additional parentheses will be needed to make the
  term right-hand nested, such as :g:`a1 OP1 (a2 OP2 ...)`.)
  The splitting pattern can have more than 2 names, for example :g:`(H1 & H2 & H3)`
  matches :g:`A /\ B /\ C`.
  The inductive types must have a
  :ref:`single constructor with two parameters <intropattern_cons_note>`.
  :ref:`Example <intropattern_ampersand_ex>`

* :n:`[ {+| {* @intropattern } } ]` — splits an inductive type that has
  :ref:`multiple constructors <intropattern_cons_note>`
  such as :n:`A \/ B`
  into multiple subgoals.  The number of :token:`intropattern`\s must be the same as the number of
  constructors for the matched part.
* :n:`[ {+ @intropattern} ]` — splits an inductive type that has a
  :ref:`single constructor with multiple parameters <intropattern_cons_note>`
  such as :n:`A /\ B` into multiple hypotheses.  Use :n:`[H1 [H2 H3]]` to match :g:`A /\ B /\ C`.
* :n:`[]` — splits an inductive type:  If the inductive
  type has multiple constructors, such as :n:`A \/ B`,
  create one subgoal for each constructor.  If the inductive type has a single constructor with
  multiple parameters, such as :n:`A /\ B`, split it into multiple hypotheses.

**Equality patterns**

These patterns can be used when the hypothesis is an equality:

* :n:`->` — replaces the right-hand side of the hypothesis with the left-hand
  side of the hypothesis in the conclusion of the goal; the hypothesis is
  cleared; if the left-hand side of the hypothesis is a variable, it is
  substituted everywhere in the context and the variable is removed.
  :ref:`Example <intropattern_rarrow_ex>`
* :n:`<-` — similar to :n:`->`, but replaces the left-hand side of the hypothesis
  with the right-hand side of the hypothesis.
* :n:`[= {*, @intropattern} ]` — If the product is over an equality type,
  applies either :tacn:`injection` or :tacn:`discriminate`.
  If :tacn:`injection` is applicable, the intropattern
  is used on the hypotheses generated by :tacn:`injection`.  If the
  number of patterns is smaller than the number of hypotheses generated, the
  pattern :n:`?` is used to complete the list.
  :ref:`Example <intropattern_inj_discr_ex>`

**Other patterns**

* :n:`*` — introduces one or more quantified variables from the result
  until there are no more quantified variables.
  :ref:`Example <intropattern_star_ex>`

* :n:`**` — introduces one or more quantified variables or hypotheses from the result until there are
  no more quantified variables or implications (:g:`->`).  :g:`intros **` is equivalent
  to :g:`intros`.
  :ref:`Example <intropattern_2stars_ex>`

* :n:`@simple_intropattern_closed {* % @term}` — first applies each of the terms
  with the :tacn:`apply … in` tactic on the hypothesis to be introduced, then it uses
  :n:`@simple_intropattern_closed`.
  :ref:`Example <intropattern_injection_ex>`

.. _intropattern_cons_note:

.. note::

   :n:`A \/ B` and :n:`A /\ B` use infix notation to refer to the inductive
   types :n:`or` and :n:`and`.
   :n:`or` has multiple constructors (:n:`or_introl` and :n:`or_intror`),
   while :n:`and` has a single constructor (:n:`conj`) with multiple parameters
   (:n:`A` and :n:`B`).
   These are defined in ``theories/Init/Logic.v``.  The "where" clauses define the
   infix notation for "or" and "and".

   .. coqdoc::

      Inductive or (A B:Prop) : Prop :=
        | or_introl : A -> A \/ B
        | or_intror : B -> A \/ B
      where "A \/ B" := (or A B) : type_scope.

      Inductive and (A B:Prop) : Prop :=
        conj : A -> B -> A /\ B
      where "A /\ B" := (and A B) : type_scope.

.. note::

   :n:`intros {+ p}` is not always equivalent to :n:`intros p; ... ; intros p`
   if some of the :n:`p` are :g:`_`.  In the first form, all erasures are done
   at once, while they're done sequentially for each tactic in the second form.
   If the second matched term depends on the first matched term and the pattern
   for both is :g:`_` (i.e., both will be erased), the first :n:`intros` in the second
   form will fail because the second matched term still has the dependency on the first.

Examples:

.. _intropattern_conj_ex:

   .. example:: intro pattern for /\\

      .. coqtop:: reset none

         Goal forall (A: Prop) (B: Prop), (A /\ B) -> True.

      .. coqtop:: out

         intros.

      .. coqtop:: all

         destruct H as (HA & HB).

.. _intropattern_disj_ex:

   .. example:: intro pattern for \\/

      .. coqtop:: reset none

         Goal forall (A: Prop) (B: Prop), (A \/ B) -> True.

      .. coqtop:: out

         intros.

      .. coqtop:: all

         destruct H as [HA|HB]. all: swap 1 2.

.. _intropattern_rarrow_ex:

   .. example:: -> intro pattern

      .. coqtop:: reset none

         Goal forall (x:nat) (y:nat) (z:nat), (x = y) -> (y = z) -> (x = z).

      .. coqtop:: out

         intros * H.

      .. coqtop:: all

         intros ->.

.. _intropattern_inj_discr_ex:

   .. example:: [=] intro pattern

      The first :n:`intros [=]` uses :tacn:`injection` to strip :n:`(S ...)` from
      both sides of the matched equality.  The second uses :tacn:`discriminate` on
      the contradiction :n:`1 = 2` (internally represented as :n:`(S O) = (S (S O))`)
      to complete the goal.

      .. coqtop:: reset none

         Goal forall (n m:nat),  (S n) = (S m) -> (S O)=(S (S O)) -> False.

      .. coqtop:: out

         intros *.

      .. coqtop:: all

         intros [= H].

      .. coqtop:: all

         intros [=].

.. _intropattern_ampersand_ex:

   .. example:: (A & B & ...) intro pattern

      .. coqtop:: reset none

         Parameters (A : Prop) (B: nat -> Prop) (C: Prop).

      .. coqtop:: out

         Goal A /\ (exists x:nat, B x /\ C) -> True.

      .. coqtop:: all

         intros (a & x & b & c).

.. _intropattern_star_ex:

   .. example:: * intro pattern

      .. coqtop:: reset out

         Goal forall (A: Prop) (B: Prop), A -> B.

      .. coqtop:: all

         intros *.

.. _intropattern_2stars_ex:

   .. example:: ** pattern ("intros \**" is equivalent to "intros")

      .. coqtop:: reset out

         Goal forall (A: Prop) (B: Prop), A -> B.

      .. coqtop:: all

         intros **.

   .. example:: compound intro pattern

      .. coqtop:: reset out

         Goal forall A B C:Prop, A \/ B /\ C -> (A -> C) -> C.

      .. coqtop:: all

         intros * [a | (_,c)] f.
         all: swap 1 2.

.. _intropattern_injection_ex:

   .. example:: combined intro pattern using [=] -> and %

      .. coqtop:: reset none

         Require Import Coq.Lists.List.
         Section IntroPatterns.
         Variables (A : Type) (xs ys : list A).

      .. coqtop:: out

         Example ThreeIntroPatternsCombined :
         S (length ys) = 1 -> xs ++ ys = xs.

      .. coqtop:: all

         intros [=->%length_zero_iff_nil].

      * `intros` would add :g:`H : S (length ys) = 1`
      * `intros [=]` would additionally apply :tacn:`injection` to :g:`H` to yield :g:`H0 : length ys = 0`
      * `intros [=->%length_zero_iff_nil]` applies the theorem, making H the equality :g:`l=nil`,
        which is then applied as for :g:`->`.

      .. coqdoc::

         Theorem length_zero_iff_nil (l : list A):
            length l = 0 <-> l=nil.

      The example is based on `Tej Chajed's coq-tricks <https://github.com/tchajed/coq-tricks/blob/8e6efe4971ed828ac8bdb5512c1f615d7d62691e/src/IntroPatterns.v>`_

.. _occurrenceclauses:

Occurrence clauses
~~~~~~~~~~~~~~~~~~

An :gdef:`occurrence` is a subterm of a goal or hypothesis that
matches a pattern provided by a tactic.  Occurrence clauses
select a subset of the ocurrences in a goal and/or in
one or more of its hypotheses.

   .. insertprodn occurrences concl_occs

   .. prodn::
      occurrences ::= at @occs_nums
      | in @goal_occurrences
      simple_occurrences ::= @occurrences
      occs_nums ::= {? - } {+ @nat_or_var }
      nat_or_var ::= {| @natural | @ident }
      goal_occurrences ::= {+, @hyp_occs } {? %|- {? @concl_occs } }
      | * %|- {? @concl_occs }
      | %|- {? @concl_occs }
      | {? @concl_occs }
      hyp_occs ::= @hypident {? at @occs_nums }
      hypident ::= @ident
      | ( type of @ident )
      | ( value of @ident )
      concl_occs ::= * {? at @occs_nums }

   :n:`@occurrences`
     The first form of :token:`occurrences` selects occurrences in
     the conclusion of the goal.  The second form can select occurrences
     in the goal conclusion and in one or more hypotheses.

   :n:`@simple_occurrences`
     A semantically restricted form of :n:`@occurrences` that doesn't allow the
     `at` clause anywhere within it.

   :n:`{? - } {+ @nat_or_var }`
     Selects the specified occurrences within a single goal or hypothesis.
     Occurrences are numbered starting with 1 following a depth-first traversal
     of the term's expression, including occurrences in
     :ref:`implicit arguments <ImplicitArguments>`
     and :ref:`coercions <Coercions>` that are not displayed by default.
     (Set the :flag:`Printing All` flag to show those in the printed term.)

     For example, when matching the pattern `_ + _` in the term `(a + b) + c`,
     occurrence 1 is `(...) + c` and
     occurrence 2 is `(a + b)`.  When matching that pattern with term `a + (b + c)`,
     occurrence 1 is `a + (...)` and occurrence 2 is `b + c`.

     Specifying `-` includes all occurrences *except* the ones listed.

   :n:`{*, @hyp_occs } {? %|- {? @concl_occs } }`
     Selects occurrences in the specified hypotheses and the
     specified occurrences in the conclusion.

   :n:`* %|- {? @concl_occs }`
     Selects all occurrences in all hypotheses and the
     specified occurrences in the conclusion.

   :n:`%|- {? @concl_occs }`
     Selects the specified occurrences in the conclusion.

   :n:`@goal_occurrences ::= {? @concl_occs }`
     Selects all occurrences in all hypotheses and in the specified occurrences
     in the conclusion.

   :n:`@hypident {? at @occs_nums }`
     Omiting :token:`occs_nums` selects all occurrences within the hypothesis.

   :n:`@hypident ::= @ident`
     Selects the hypothesis named :token:`ident`.

   :n:`( type of @ident )`
     Selects the type part of the named hypothesis (e.g. `: nat`).

   :n:`( value of @ident )`
     Selects the value part of the named hypothesis (e.g. `:= 1`).

   :n:`@concl_occs ::= * {? at @occs_nums }`
     Selects occurrences in the conclusion.  '*' by itself selects all occurrences.
     :n:`@occs_nums` selects the specified occurrences.

   Use `in *` to select all occurrences in all hypotheses and the conclusion,
   which is equivalent to `in * |- *`.  Use `* |-` to select all occurrences
   in all hypotheses.

   When rewriting in multiple hypotheses, they must not appear in the
   term to rewrite. For instance `rewrite H in H,H'` is an error. If
   an hypothesis appears only through a hole, it will be removed from
   that hole's context.

   With `rewrite term in *`, hypotheses on which the dependency cannot
   be avoided are skipped, for instance `rewrite H in *` skips
   rewriting in `H`. This is the case even if only one hypothesis ends
   up rewritten.

   If multiple
   occurrences are given, such as in :tacn:`rewrite` `H at 1 2 3`, the tactic
   must match at least one occurrence in order to succeed.  The tactic will fail
   if no occurrences match.  Occurrence numbers that are out of range (e.g.
   `at 1 3` when there are only 2 occurrences in the hypothesis or conclusion)
   are ignored.

   .. todo: remove last sentence above and add "Invalid occurrence number @natural" exn for 8.14
      per #13568.

   Tactics that use occurrence clauses include :tacn:`set`,
   :tacn:`remember`, :tacn:`induction` and :tacn:`destruct`.


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
   subgoals as there are remaining holes in the elaborated term. Any subgoal that
   occurs in other subgoals is automatically shelved, as if calling
   :tacn:`shelve_unifiable`. The produced subgoals (shelved or not)
   are *not* candidates for typeclass resolution, even if they have a type-class
   type as conclusion, letting the user control when and how typeclass resolution
   is launched on them. This low-level tactic can be useful to advanced users.

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

      This tactic behaves like the combination of :tacn:`simple refine` and
      :tacn:`notypeclasses refine`: it performs type checking without resolution of
      typeclasses, does not perform beta reductions or shelve the subgoals.

   :opt:`Debug` ``"unification"`` enables printing traces of
   unification steps used during elaboration/typechecking and the
   :tacn:`refine` tactic. ``"ho-unification"`` prints information
   about higher order heuristics.

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

   .. tacv:: apply @term with @bindings

      This also provides apply with values for instantiating premises. Here, variables
      are referred by names and non-dependent products by increasing numbers (see
      :ref:`bindings`).

      .. flag:: Apply With Renaming

         When on, this flag causes the names in the :n:`@term`'s type to be renamed for uniqueness.
         By default no renaming is done.

         .. deprecated:: 8.15

            This flag is provided for compatibility with versions prior to 8.15.

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

   .. tacv:: rapply @term
      :name: rapply

      The tactic :tacn:`rapply` behaves like :tacn:`eapply` but it
      uses the proof engine of :tacn:`refine` for dealing with
      existential variables, holes, and conversion problems.  This may
      result in slightly different behavior regarding which conversion
      problems are solvable.  However, like :tacn:`apply` but unlike
      :tacn:`eapply`, :tacn:`rapply` will fail if there are any holes
      which remain in :n:`@term` itself after typechecking and
      typeclass resolution but before unification with the goal.  More
      technically, :n:`@term` is first parsed as a
      :production:`constr` rather than as a :production:`uconstr` or
      :production:`open_constr` before being applied to the goal. Note
      that :tacn:`rapply` prefers to instantiate as many hypotheses of
      :n:`@term` as possible.  As a result, if it is possible to apply
      :n:`@term` to arbitrarily many arguments without getting a type
      error, :tacn:`rapply` will loop.

      Note that you need to :n:`Require Import Coq.Program.Tactics` to
      make use of :tacn:`rapply`.

   .. tacv:: simple apply @term.

      This behaves like :tacn:`apply` but it reasons modulo conversion only on subterms
      that contain no variables to instantiate. For instance, the following example
      does not succeed because it would require the conversion of ``id ?foo`` and
      :g:`O`.

      .. _simple_apply_ex:
      .. example::

         .. coqtop:: all

            Definition id (x : nat) := x.
            Parameter H : forall x y, id x = y.
            Goal O = O.
            Fail simple apply H.

      Because it reasons modulo a limited amount of conversion, :tacn:`simple apply` fails
      quicker than :tacn:`apply` and it is then well-suited for uses in user-defined
      tactics that backtrack often. Moreover, it does not traverse tuples as :tacn:`apply`
      does.

   .. tacv:: {? simple} apply {+, @term {? with @bindings}}
             {? simple} eapply {+, @term {? with @bindings}}
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

.. example::

   Assume we have a transitive relation ``R`` on ``nat``:

   .. coqtop:: reset in

      Parameter R : nat -> nat -> Prop.

      Axiom Rtrans : forall x y z:nat, R x y -> R y z -> R x z.

      Parameters n m p : nat.

      Axiom Rnm : R n m.

      Axiom Rmp : R m p.

   Consider the goal ``(R n p)`` provable using the transitivity of ``R``:

   .. coqtop:: in

      Goal R n p.

   The direct application of ``Rtrans`` with ``apply`` fails because no value
   for ``y`` in ``Rtrans`` is found by ``apply``:

   .. coqtop:: all fail

      apply Rtrans.

   A solution is to ``apply (Rtrans n m p)`` or ``(Rtrans n m)``.

   .. coqtop:: all

      apply (Rtrans n m p).

   Note that ``n`` can be inferred from the goal, so the following would work
   too.

   .. coqtop:: in restart

      apply (Rtrans _ m).

   More elegantly, ``apply Rtrans with (y:=m)`` allows only mentioning the
   unknown m:

   .. coqtop:: in restart

      apply Rtrans with (y := m).

   Another solution is to mention the proof of ``(R x y)`` in ``Rtrans``

   .. coqtop:: all restart

      apply Rtrans with (1 := Rnm).

   ... or the proof of ``(R y z)``.

   .. coqtop:: all restart

      apply Rtrans with (2 := Rmp).

   On the opposite, one can use ``eapply`` which postpones the problem of
   finding ``m``. Then one can apply the hypotheses ``Rnm`` and ``Rmp``. This
   instantiates the existential variable and completes the proof.

   .. coqtop:: all restart abort

      eapply Rtrans.

      apply Rnm.

      apply Rmp.

.. note::
   When the conclusion of the type of the term to ``apply`` is an inductive
   type isomorphic to a tuple type and ``apply`` looks recursively whether a
   component of the tuple matches the goal, it excludes components whose
   statement would result in applying an universal lemma of the form
   ``forall A, ... -> A``. Excluding this kind of lemma can be avoided by
   setting the following flag:

.. tacn:: apply @term in @ident
   :name: apply … in

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

   .. tacv:: apply {+, @term} in {+, @ident}

      This applies each :token:`term` in sequence in each hypothesis :token:`ident`.

   .. tacv:: apply {+, @term with @bindings} in {+, @ident}

      This does the same but uses the bindings to instantiate
      parameters of :token:`term` (see :ref:`bindings`).

   .. tacv:: eapply {+, @term {? with @bindings } } in {+, @ident}

      This works as :tacn:`apply … in` but turns unresolved bindings into
      existential variables, if any, instead of failing.

   .. tacv:: apply {+, @term {? with @bindings } } in {+, @ident {? as @simple_intropattern}}
      :name: apply … in … as

      This works as :tacn:`apply … in` but applying an associated
      :token:`simple_intropattern` to each hypothesis :token:`ident`
      that comes with such clause.

   .. tacv:: simple apply @term in {+, @ident}

      This behaves like :tacn:`apply … in` but it reasons modulo conversion
      only on subterms that contain no variables to instantiate and does not
      traverse tuples. See :ref:`the corresponding example <simple_apply_ex>`.

   .. tacv:: {? simple} apply {+, @term {? with @bindings}} in {+, @ident {? as @simple_intropattern}}
             {? simple} eapply {+, @term {? with @bindings}} in {+, @ident {? as @simple_intropattern}}

      This summarizes the different syntactic variants of :n:`apply @term in {+, @ident}`
      and :n:`eapply @term in {+, @ident}`.

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

.. tacn:: intros {* @intropattern }
   :name: intros …

   Introduces one or more variables or hypotheses from the goal by matching the
   intro patterns.  See the description in :ref:`intropatterns`.

.. tacn:: eintros {* @intropattern }
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
      :ref:`goal occurrences <occurrenceclauses>`.

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

   .. coqtop:: all abort

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

   This tactic behaves functionally as :tacn:`idtac`.

   .. deprecated:: 8.16

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
