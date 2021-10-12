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
primarily use backward reasoning.

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

Tactics may be preceded by a
goal selector (see Section :ref:`goal-selectors`). If no selector is
specified, the default selector is used.

.. _tactic_invocation_grammar:

  .. prodn::
     tactic_invocation ::= {? @toplevel_selector : } @tactic.

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

Tactics that take a term as an argument may also accept :token:`bindings` to
specify the values to assign unbound variables in a term.
Bindings can be given by position or name.  Generally these appear in the form
:n:`@one_term_with_bindings` or :n:`with @bindings`, depending on the tactic.

  .. insertprodn one_term_with_bindings bindings

  .. prodn::
     one_term_with_bindings ::= @one_term {? with @bindings }
     bindings ::= {+ @one_term }
     | {+ ( {| @ident | @natural } := @term ) }

* :n:`@one_term {? with @bindings }` — bindings for variables in :n:`@one_term`
  are typically determined by unifying :n:`@one_term` with a tactic-dependent part
  of the context, with any remaining unbound variables provided by the :n:`@bindings`.

* :n:`{+ @one_term }` — binds free variables in the left-to-right order of their first
  appearance in the relevant term.

  For some tactics, bindings for all free variables
  must be provided, such as for :tacn:`induction`, :tacn:`destruct`, :tacn:`elim`
  and :tacn:`case`.  Other tactics automatically generate some or all
  of the bindings from the conclusion or a hypothesis, such as :tacn:`apply` and
  :tacn:`constructor` and its variants.  In this case, only instances
  for the :term:`dependent premises <dependent premise>` that are not bound in
  the conclusion of the relevant term are required (and permitted).

* :n:`{+ ( {| @ident | @natural } := @term ) }` —  binds variables by name (if :n:`@ident` is given), or
  by unifying with the ``n``-th :term:`premise` of the relevant term
  (if :n:`@natural` is given).

.. exn:: No such binder.

   :n:`@natural` is 0 or more than the number of unbound variables.

.. exn:: No such bound variable @ident (no bound variables at all in the expression).
   :undocumented:

.. exn:: No such bound variable @ident__1 (possible names are: @ident__2 ...).

   The specified binder name :n:`@ident__1` is not used in the :n:`@one_term`.
   :n:`@ident__2 ...` lists all the valid binder names.

.. exn:: Not the right number of missing arguments (expected @natural).

   Generated when the first form of :n:`@bindings` doesn't have the
   expected number of arguments.

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
  of one or more nested binary inductive types such as :g:`a1 OP1 a2 OP2 …`
  (where the :g:`OPn` are right-associative).
  (If the :g:`OPn` are left-associative, additional parentheses will be needed to make the
  term right-hand nested, such as :g:`a1 OP1 (a2 OP2 …)`.)
  The splitting pattern can have more than 2 names, for example :g:`(H1 & H2 & H3)`
  matches :g:`A /\ B /\ C`.
  The inductive types must have a
  :ref:`single constructor with two parameters <intropattern_cons_note>`.
  :ref:`Example <intropattern_ampersand_ex>`

* :n:`[ {+| {* @intropattern } } ]` — splits an inductive type that has
  :ref:`multiple constructors <intropattern_cons_note>`
  such as :n:`A \/ B` into multiple subgoals.  The number of :token:`intropattern`\s
  must be the same as the number of constructors for the matched part.
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

* :n:`*` — introduces one or more :term:`dependent premises <dependent premise>`
  from the result until there are no more.
  :ref:`Example <intropattern_star_ex>`

* :n:`**` — introduces one or more :term:`dependent <dependent premise>`
  or :term:`non-dependent premises <non-dependent premise>` from the result
  until there are no more premises.  :g:`intros **` is equivalent to :g:`intros`.
  :ref:`Example <intropattern_2stars_ex>`

* :n:`@simple_intropattern_closed {* % @term}` — first applies each of the terms
  with the :tacn:`apply` tactic on the hypothesis to be introduced, then it uses
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

   :tacn:`intros` :n:`{+ p}` is not always equivalent to :n:`intros p; … ; intros p`
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

      The first :tacn:`intros` :n:`[=]` uses :tacn:`injection` to strip :n:`(S …)` from
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

   .. example:: (A & B & …) intro pattern

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
     occurrence 1 is `(…) + c` and
     occurrence 2 is `(a + b)`.  When matching that pattern with term `a + (b + c)`,
     occurrence 1 is `a + (…)` and occurrence 2 is `b + c`.

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

   .. exn:: No such hypothesis: @ident.
      :undocumented:

.. seealso::

   :ref:`Managingthelocalcontext`, :ref:`caseanalysisandinduction`,
   :ref:`printing_constructions_full`.


.. _applyingtheorems:

Applying theorems
---------------------

.. tacn:: exact @one_term

   Directly gives the exact proof term for the goal.
   ``exact p`` succeeds if and only if :n:`@one_term` and the type of ``p`` are
   unifiable (see :ref:`Conversion-rules`).

   .. exn:: Not an exact proof.
      :undocumented:

   .. tacn:: eexact @one_term

      Behaves like :tacn:`exact` but can handle terms and
      goals with existential variables.

.. tacn:: assumption

   This tactic looks in the local context for a hypothesis whose type is
   convertible to the goal. If it is the case, the subgoal is proved.
   Otherwise, it fails.

   .. exn:: No such assumption.
      :undocumented:

   .. tacn:: eassumption

      Behaves like :tacn:`assumption` but is able to handle
      goals and hypotheses with existential variables.

.. tacn:: {? simple } {? notypeclasses } refine @one_term
   :name: refine

   Behaves like :tacn:`exact` but allows holes (denoted by ``_``
   or :n:`(_ : @type)`) in :n:`@one_term`. :tacn:`refine` generates as many
   subgoals as there are remaining holes in the elaborated term. The types
   of these holes must be inferable or declared by an explicit cast
   such as ``(_ : nat -> Prop)``. Any subgoal that
   occurs in other subgoals is automatically shelved, as if calling
   :tacn:`shelve_unifiable`.

   `simple`
     If specified, don't shelve any subgoals or perform beta reduction.

   `notypeclasses`
     If specified, do checking without resolving typeclasses.  The generated
     subgoals (shelved or not) are *not* candidates for typeclass resolution,
     even if they have a typeclass type as their conclusion.

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

   .. exn:: Cannot infer a term for this placeholder.
      :name: Cannot infer a term for this placeholder. (refine)

      There is a hole in the term you gave whose type cannot be inferred. Put a
      cast around it.

   Setting :opt:`Debug` ``"unification"`` enables printing traces of
   unification steps used during elaboration/typechecking and the
   :tacn:`refine` tactic. ``"ho-unification"`` prints information
   about higher order heuristics.

.. tacn:: apply {+, {? > } @one_term_with_bindings } {? @in_hyp_as }

   .. insertprodn in_hyp_as as_ipat

   .. prodn::
      in_hyp_as ::= in {+, @ident {? @as_ipat } }
      as_ipat ::= as @simple_intropattern

   Uses unification to match the type of each :n:`@one_term`
   (in :n:`@one_term_with_bindings`) with the goal
   (to do :term:`backward reasoning`) or with a hypothesis (to do :term:`forward reasoning`).
   Specifying multiple :n:`@one_term_with_bindings` is equivalent to
   giving each one serially, left to right, as separate `apply` tactics.

   The type of :n:`@one_term` contains zero or more :term:`premises <premise>`
   followed by a :ref:`conclusion <conclusion_meaning_2>`,
   i.e. it typically has the form :n:`{? forall @open_binders , } {* @term__premise -> } @term__conclusion`.
   (The ``forall``\s may also be interleaved with the premises, but common usage is
   to equivalently gather them at the beginning of the :n:`@one_term`.)
   Backward reasoning with a :n:`@one_term` whose type is, for example, `A -> B`
   replaces an as-yet unproven goal `B` with `A`.  Forward reasoning with the same
   :n:`@one_term` changes a hypothesis with type `A` to `B`.  (Hypotheses are
   considered proven propositions within the context that contains them.)

   Unification creates a map from the variables in the type of :n:`@one_term`
   to matching subterms of the goal or hypothesis.
   The matching subterms are then substituted into the type of :n:`@one_term`
   when generating the updated goal or hypothesis.  Unmatched premises become
   new subgoals with similar substitutions.  If no match is found, the
   tactic fails.

   Setting :opt:`Debug` ``"tactic-unification"`` enables printing traces of
   unification steps in tactic unification. Tactic unification is used in
   tactics such as :tacn:`apply` and :tacn:`rewrite`.

   The goal and hypothesis cases are described separately for clarity.

.. _unused1:

   .. the dummy ref name is needed to get correct formatting of the next line and "Without..."

   :n:`@one_term` (inside :n:`@one_term_with_bindings`)
     If :n:`@one_term` is an :n:`@ident`, it is the name of
     a theorem, lemma or hypothesis whose type is given in the
     theorem statement or shown in the context.  Otherwise it is a proof term whose
     type can be displayed with :cmd:`Check` :n:`@one_term`.

   Without :n:`@in_hyp_as` (the goal case)
     If the goal matches all of the type of :n:`@one_term` (both premises and
     the conclusion), the tactic proves the goal.
     Otherwise, the tactic matches the goal against the conclusion of :n:`@one_term`
     and, if possible, one or more premises (from right to left).
     If the match succeeds, the tactic replaces the current goal with a subgoal for
     each unmatched premise of the type of :n:`@one_term`.  This
     :ref:`example <apply_backward>` matches only the conclusion, while
     this :ref:`one <apply_backward_w_premises>` also matches a premise.

     If the conclusion of the type of :token:`one_term` does not match the goal
     *and* the conclusion is an inductive type with a single constructor,
     then each premise in the constructor is recursively matched to the goal in
     right-to-left order and the first match is used.  In this case, the tactic
     will not match premises that would result in applying a lemma of the form
     ``forall A, … -> A``.  See example :ref:`here <apply_with_iff>`.

.. _apply_with_second_order_unification:

     The goal case uses first-order unification with dependent types unless the
     conclusion of the type of :token:`term` is of the form
     :n:`P t__1 … t__n` with :n:`P` to be instantiated. In the latter case,
     the behavior depends on the form of the target. If the target is of the form
     :n:`Q u__1 … u__n` and the :n:`t__i` and :n:`u__i` unify,
     then :n:`P` is instantiated into :n:`Q`. Otherwise, :tacn:`apply`
     tries to define :n:`P` by abstracting over :n:`t__1 … t__n` in the target.
     You can use :tacn:`pattern` to transform the target so that it
     gets the form :n:`(fun x__1 … x__n => Q) u__1 … u__n`.  See the example
     :ref:`here <example_apply_pattern>`.

   :n:`@in_hyp_as` (the hypothesis case)
     Proceeding from *right to left*, find the first premise of the type of
     :n:`@one_term` that matches the specified hypothesis.  If a match
     is found, the hypothesis is replaced with the conclusion of the type of
     :n:`@one_term` (substituting for the unified variables)
     and the tactic creates a new subgoal for each unmatched premise.
     See the example :ref:`here <apply_forward>`.

     If specified, :n:`as @simple_intropattern` is applied to the conclusion
     of the type of :n:`@one_term`. In this case, the selected hypothesis
     is left unchanged if its name is not reused.

     If the type of :n:`@one_term` is an inductive type with a single constructor,
     then each premise in the constructor is recursively matched to the conclusion
     of the hypothesis in right-to-left order and the first match is used.
     See example :ref:`here <apply_with_iff>`.

     For the hypothesis case, matching is done only with first-order unification.

   :n:`with @bindings` (in :n:`@one_term_with_bindings`)
     Gives explicit instantiations for variables used in the type of :n:`@one_term`.
     There are 3 cases:

     - Bindings for variables can be provided in a list of :n:`@one_term`\s
       in the left-to-right order of their first appearance in the type of
       :n:`@one_term`.  For the goal case (:ref:`example <apply_with_binding_goal>`),
       the list should give bindings only for variables that aren't bound by
       unification.  However, in the hypothesis case
       (:ref:`example <apply_with_binding_hyp>`),
       the list must include bindings for *all* variables.

     - Bindings for unbound variables can be given by name with the
       :n:`(@ident := @term)` form.

     - The form :n:`(@natural := @term)` binds additional variables by
       unifying the Nth premise of the type of :n:`@one_term` with :n:`@term`.
       (Use `1` for the first premise.)

   .. exn:: Unable to unify @one_term with @one_term.

      The :tacn:`apply` tactic failed to match the conclusion of :token:`one_term`.
      You can help :tacn:`apply` by
      transforming your goal with the :tacn:`change` or :tacn:`pattern`
      tactics.

   .. exn:: Unable to apply lemma of type "..." on hypothesis of type "...".

      This happens if the conclusion of :token:`ident` does not match any of
      the premises of the type of :token:`one_term`.

   .. exn:: Unable to find an instance for the variables {+ @ident}.

      This occurs when some instantiations of the premises of :token:`one_term` are not deducible
      from the unification. This is the case, for instance, when you want to apply a
      transitivity property.  To fix this, add bindings for the :n:`@ident`\s using
      to :n:`with @bindings` or use :tacn:`eapply`.

   .. todo: we should be listing things like "Debug tactic-unification" in
      in the options index.  Maybe we should add ":debug:" as a new tag.

   .. flag:: Apply With Renaming

      When on, this flag causes the names in the :n:`@term`'s type to be renamed for uniqueness.
      By default no renaming is done.

      .. deprecated:: 8.15

         Provided for compatibility with versions prior to 8.15.

   .. _apply_backward:
   .. example:: Backward reasoning in the goal with `apply`

      .. coqtop:: reset none

         Goal forall A B C: Prop, (A -> B -> C) -> C.

      .. coqtop:: out

         intros A B C H.

      .. coqtop:: all

         apply H.  (* replace goal with new goals for unmatched premises of H *)

   .. _apply_backward_w_premises:
   .. example:: Backward reasoning in the goal with `apply` including a premise

      .. coqtop:: reset none

         Goal forall A B C: Prop, (A -> B -> C) -> (B -> C).

      .. coqtop:: out

         intros A B C H.

      .. coqtop:: all

         apply H.  (* match on "B -> C", replace goal with "A" *)

   .. _apply_forward:
   .. example:: Forward reasoning in hypotheses with `apply`

      .. coqtop:: reset none

         Goal forall A B C: Prop, B -> (A -> B -> C) -> True.

      .. coqtop:: out

         intros A B C H0 H1.

      .. coqtop:: all

         apply H1 in H0.  (* change H0, create new goals for unmatched premises of H1 *)

   .. _apply_with_binding_goal:
   .. example:: Apply a theorem with a binding in a goal

      :tacn:`apply` unifies the conclusion `n <= p` of the theorem
      `le_trans : forall n m p, n <= m -> m <= p -> n <= p`
      with the goal, assigning `x * x` and `y * y` in the goal
      to, repectively, `n` and `p` in theorem (backward reasoning).
      The `with` clause provides the binding for `m`:

      .. coqtop:: reset in

         Require Import PeanoNat.

      .. coqtop:: none

         Goal forall (x y : nat), x <= y -> x * x <= y * y.

      .. coqtop:: out

         intros x y H0.

      .. coqtop:: all

         apply Nat.le_trans with (y * x).

   .. _apply_with_binding_hyp:
   .. example:: Apply a theorem with a binding in a hypothesis

      When applying a theorem in a hypothesis,
      :tacn:`apply` unifies the hypothesis with one of the premises
      of the theorem `le_trans : forall n m p, n <= m -> m <= p -> n <= p`.
      In this case, it unifies with the first premise
      (`n <= m`) and assigns `x * x` and `y * y` to,
      respectively, `n` and `m` in the theorem (forward reasoning).
      The  `with` clause provides the binding for `p`.

      In addition, :tacn:`apply` in a hypothesis isn't as flexible as
      :tacn:`apply` in the goal: for hypotheses, the unbound variable can be bound
      by name (as shown) or values for all the variables can be given
      positionally, i.e. `apply Nat.le_trans with (x * x) (y * y) (y * x) in H.`

      .. coqtop:: reset in

         Require Import PeanoNat.

      .. coqtop:: none

         Goal forall (x y : nat), x * x <= y * y -> x <= y.

      .. coqtop:: out

         intros x y H.

      .. coqtop:: all

         apply Nat.le_trans with (p := y * x) in H.

   .. _apply_with_iff:
   .. example:: Applying theorems with `<->`

      .. Note: :n:`/\` and :n:`/\\` don't give the desired output.  A bug.

      :n:`A <-> B` is defined as :n:`(A -> B) /\ (B -> A)`.
      `/\\` represents an inductive type with a single constructor:
      :n:`Inductive and (C D:Prop) : Prop := conj : C -> D -> D /\ C`.  The premises
      of :n:`conj` are :n:`C` and :n:`D`.  The tactic uses the first matching
      constructor premise in right-to-left order.

      Theorems that use :n:`<->` to state a logical equivalence behave consistently
      when applied to goals and hypotheses.

      .. coqtop:: reset none

         Goal forall (A B: Prop) (H1: A <-> B) (H: A), A.

      .. coqtop:: out

         intros A B H1 H.

      .. coqtop:: all

         apply H1.
         apply H1 in H.

   .. _example_apply_pattern:
   .. example:: Special case of second-order unification in apply

      Shows the use of the special case second-order unification described
      :ref:`here <apply_with_second_order_unification>` (after "unless").

      Note that we usually use :tacn:`induction` rather than applying ``nat_ind`` directly.

      .. coqtop:: reset none

         Goal forall x y, x + y = y + x.

      .. coqtop:: out

         intros.

      .. coqtop:: all

         Check nat_ind.

         apply nat_ind.  (* Notice the goals are unprovable. *)
         Show Proof.     (* apply has instantiated P with (eq (x + y))
                        because the goal was (eq (x + y) (y + x))
                        and n could be unified with (y + x) *)
         (* However, we can use the pattern tactic to get the instantiation we want: *)

         Undo.
         pattern x.
         apply nat_ind.
         Show Proof.     (* apply has instantiated P with (fun n : nat => n + y = y + n)
                        and the goal can be proven *)

   .. tacn:: eapply {+, {? > } @one_term_with_bindings } {? @in_hyp_as }

      Behaves like :tacn:`apply`, but creates
      :ref:`existential variables <Existential-Variables>`
      when Coq is unable to deduce instantiations for variables, rather than failing.

   .. tacn:: rapply @one_term

      Behaves like :tacn:`eapply` but
      uses the proof engine of :tacn:`refine` to handle
      existential variables, holes and conversion problems.  This may
      result in slightly different behavior regarding which conversion
      problems are solvable.  However, :tacn:`rapply` fails if any holes remain
      in :n:`@one_term` itself after typechecking and
      typeclass resolution but before unification with the goal. Note
      that :tacn:`rapply` tries to instantiate as many hypotheses of
      :n:`@one_term` as possible.  As a result, if it is possible to apply
      :n:`@one_term` to arbitrarily many arguments without getting a type
      error, :tacn:`rapply` will loop.

      Note that you must :n:`Require Import Coq.Program.Tactics` to
      use :tacn:`rapply`.

   .. tacn:: simple apply {+, {? > } @one_term_with_bindings } {? @in_hyp_as }

      Behaves like :tacn:`apply` but it reasons modulo conversion only on subterms
      that contain no variables to instantiate and does not traverse tuples.
      For instance, the following example fails because it would require converting
      ``id ?foo`` and :g:`O`.

      .. _simple_apply_ex:
      .. example::

         .. coqtop:: reset all

            Definition id (x : nat) := x.
            Parameter H : forall x y, id x = y.
            Goal O = O.
            Fail simple apply H.

      Because it reasons modulo a limited amount of conversion, :tacn:`simple apply` fails
      faster than :tacn:`apply` and it is thus well-suited for use in user-defined
      tactics that backtrack often.

   .. tacn:: simple eapply {+, {? > } @one_term_with_bindings } {? @in_hyp_as }
      :undocumented:

   .. tacn:: lapply @one_term

      Splits a :n:`@one_term` in the goal reducible to the form `A -> B`, replacing it
      with two new subgoals `A` and `B -> G`.
      ``lapply H`` (where `H` is `A -> B` and `B` does not start with a product)
      is equivalent to :tacn:`cut` ``B. 2:apply H.``.

      .. exn:: lapply needs a non-dependent product.
         :undocumented:

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

   … or the proof of ``(R y z)``.

   .. coqtop:: all restart

      apply Rtrans with (2 := Rmp).

   On the opposite, one can use ``eapply`` which postpones the problem of
   finding ``m``. Then one can apply the hypotheses ``Rnm`` and ``Rmp``. This
   instantiates the existential variable and completes the proof.

   .. coqtop:: all restart abort

      eapply Rtrans.

      apply Rnm.

      apply Rmp.

.. _managingthelocalcontext:

Managing the local context
------------------------------

.. tacn:: intro {? @ident } {? @where }

   Applies the :tacn:`hnf` tactic until it finds an item that can be
   introduced in the context by removing certain constructs in the goal.
   If no item is found, the tactic fails.  The name used is
   :n:`@ident` (if specified) or from the construct, except that if the name from the
   construct already exists in the :term:`local context`, Coq uses a fresh name
   instead.  The constructs have these forms:
   (See examples :ref:`here <intro_examples>`.)

   :n:`forall x : T, @term`
     `x : T` is a :term:`dependent premise`.  Removes `forall x : T,`
     from the goal and adds `x : T` to the context.

   :n:`A -> …`
     `A` is a :term:`non-dependent premise`.  Removes `A ->` from
     the goal and adds `H : A` to the context.

   :n:`let x := c, @term`
     Removes `let x := c,` from the goal and adds `x := c : T` to the context.

.. _warn_should_give_name_in_intro:

   We recommend always specifying :n:`@ident` so that the names of hypotheses don't
   change as the proof is updated, making your proof easier to maintain.  For example,
   if H exists in the context, Coq will consider using `H0`, `H1`, ... until it finds an
   unused name.  Modifications to a proof can change automatically assigned names
   that subsequent tactics likely refer to, making the proofs harder to maintain.  The
   :flag:`Mangle Names` flag gives some control over how fresh names are generated (see
   :ref:`proof-maintenance`).

   Note that :tacn:`intros` lets you introduce multiple items into
   the context with a single tactic.

   :n:`@ident`
     The name to give to the introduced item.  If not given, Coq uses the
     variable name from the :n:`forall` or `H` for premises.
     If a name such as `H` is already in use, Coq will consider using `H0`,
     `H1`, ... until it finds a fresh name.

     .. note::

        If a hypothesis name hides the base name of a global constant then
        the latter can still be referred to by a qualified name
        (see :ref:`Qualified-names`).

   :n:`@where`
     Indicates where to place the introduced hypothesis: at the top or bottom
     of the context or before or after another specified hypothesis.  The default
     is `at bottom`.

   .. exn:: @ident is already used.

      The provided :n:`@ident` is already used in the :term:`local context`.

   .. exn:: No product even after head-reduction.

      There is nothing to introduce even after :tacn:`hnf` has been completely applied.

   .. _intro_examples:
   .. example:: `intro` and `intros`

      .. coqtop:: reset out

         Goal forall m n, m < n -> (let x := 0 in True).

      .. coqtop:: all

         intro m.
         intro n.
         intro H.
         intro x.

      This single `intros` tactic is equivalent to the 4 preceding `intro` tactics:

      .. coqtop:: reset out

         Goal forall m n, m < n -> (let x := 0 in True).

      .. coqtop:: all

         intros m n H x.

.. tacn:: intros {* @intropattern }
          intros until {| @ident | @natural }

      The first form introduces zero or more items into the context from the
      constructs listed in :tacn:`intro`.  If :n:`@intropattern` is not specified,
      the tactic introduces items until it reaches the :term:`head constant`;
      it never fails and may leave the context unchanged.

      If :n:`@intropattern` is specified, the :tacn:`hnf` tactic is applied until
      it finds an item that can be introduced into the context.
      The :n:`@intropattern` is
      often just a list of :n:`@ident`\s, but other forms can also be specified
      in order to, for example, introduce all :term:`dependent premises <dependent premise>` (`*`);
      introduce all dependent and :term:`non-dependent premises <non-dependent premise>` (`**`);
      split terms such as `A /\\ B` (`[]`) and pick a fresh name with a given prefix (`?X`).
      See :ref:`intropatterns`.

      The second form repeats :n:`intro` until it has introduced a :term:`dependent premise`
      with the name :n:`@ident` or has introduced
      :n:`@natural` :term:`premises <premise>` (like ``A`` in ``A -> B``).

      We recommend explicitly naming items with :tacn:`intros` instead of using
      :n:`intros until @natural`.  See the explanation :ref:`here <warn_should_give_name_in_intro>`.

      .. example:: intros until

         .. coqtop:: reset out

            Goal forall x y : nat, x = y -> y = x.

         .. coqtop:: all

            intros until y.

         Or:

         .. coqtop:: reset out

            Goal forall x y : nat, x = y -> y = x.

         .. coqtop:: all

            intros until 1.

      .. exn:: No quantified hypothesis named @ident in current goal even after head-reduction.

         The :n:`@ident` in the ``until`` clause doesn't appear as a :term:`dependent premise`.

      .. exn:: No @natural-th non dependent hypothesis in current goal even after head-reduction.

         There are fewer than :n:`@natural` premises in the goal.

.. tacn:: eintros {* @intropattern }

   Works just like :tacn:`intros` except that it creates existential variables
   for any unresolved variables rather than failing.  Typically this happens when
   using a ``%`` intropattern (see :n:`@simple_intropattern`).

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

.. [2] This corresponds to the cut rule of sequent calculus.
