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
`A` and `B`, followed by the proofs of `A` and `B`.  Rocq and its tactics
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
   | ( {*& @simple_intropattern } )
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
* :n:`?` — let Rocq generate a fresh name
* :n:`?@ident` — generate a name that begins with :n:`@ident`
* :n:`_` — discard the matched part (unless it is required for another
  hypothesis)
* if a disjunction pattern omits a name, such as :g:`[|H2]`, Rocq will choose a name

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

   .. rocqdoc::

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

      .. rocqtop:: reset none

         Goal forall (A: Prop) (B: Prop), (A /\ B) -> True.

      .. rocqtop:: out

         intros.

      .. rocqtop:: all

         destruct H as (HA & HB).

.. _intropattern_disj_ex:

   .. example:: intro pattern for \\/

      .. rocqtop:: reset none

         Goal forall (A: Prop) (B: Prop), (A \/ B) -> True.

      .. rocqtop:: out

         intros.

      .. rocqtop:: all

         destruct H as [HA|HB]. all: swap 1 2.

.. _intropattern_rarrow_ex:

   .. example:: -> intro pattern

      .. rocqtop:: reset none

         Goal forall (x:nat) (y:nat) (z:nat), (x = y) -> (y = z) -> (x = z).

      .. rocqtop:: out

         intros * H.

      .. rocqtop:: all

         intros ->.

.. _intropattern_inj_discr_ex:

   .. example:: [=] intro pattern

      The first :tacn:`intros` :n:`[=]` uses :tacn:`injection` to strip :n:`(S …)` from
      both sides of the matched equality.  The second uses :tacn:`discriminate` on
      the contradiction :n:`1 = 2` (internally represented as :n:`(S O) = (S (S O))`)
      to complete the goal.

      .. rocqtop:: reset none

         Goal forall (n m:nat),  (S n) = (S m) -> (S O)=(S (S O)) -> False.

      .. rocqtop:: out

         intros *.

      .. rocqtop:: all

         intros [= H].

      .. rocqtop:: all

         intros [=].

.. _intropattern_ampersand_ex:

   .. example:: (A & B & …) intro pattern

      .. rocqtop:: reset none

         Parameters (A : Prop) (B: nat -> Prop) (C: Prop).

      .. rocqtop:: out

         Goal A /\ (exists x:nat, B x /\ C) -> True.

      .. rocqtop:: all

         intros (a & x & b & c).

.. _intropattern_star_ex:

   .. example:: * intro pattern

      .. rocqtop:: reset out

         Goal forall (A: Prop) (B: Prop), A -> B.

      .. rocqtop:: all

         intros *.

.. _intropattern_2stars_ex:

   .. example:: ** pattern ("intros \**" is equivalent to "intros")

      .. rocqtop:: reset out

         Goal forall (A: Prop) (B: Prop), A -> B.

      .. rocqtop:: all

         intros **.

   .. example:: compound intro pattern

      .. rocqtop:: reset out

         Goal forall A B C:Prop, A \/ B /\ C -> (A -> C) -> C.

      .. rocqtop:: all

         intros * [a | (_,c)] f.
         all: swap 1 2.

.. _intropattern_injection_ex:

   .. example:: combined intro pattern using [=] -> and %

      .. rocqtop:: reset none

         Require Import ListDef.
         Section IntroPatterns.
         Variables (A : Type) (xs ys : list A).
         Axiom length_zero_iff_nil :
           forall [A] (l : list A), length l = 0 <-> l = nil.

      .. rocqtop:: out

         Example ThreeIntroPatternsCombined :
         S (length ys) = 1 -> xs ++ ys = xs.

      .. rocqtop:: all

         intros [=->%length_zero_iff_nil].

      * `intros` would add :g:`H : S (length ys) = 1`
      * `intros [=]` would additionally apply :tacn:`injection` to :g:`H` to yield :g:`H0 : length ys = 0`
      * `intros [=->%length_zero_iff_nil]` applies the theorem, making H the equality :g:`l=nil`,
        which is then applied as for :g:`->`.

      .. rocqdoc::

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

      Behaves like :tacn:`assumption` but is able to process
      goals and hypotheses with existential variables.  It can also
      resolve existential variables, which :tacn:`assumption` will not.

.. tacn:: {? simple } {? notypeclasses } refine @one_term
   :name: refine

   Behaves like :tacn:`exact` but allows holes (denoted by ``_``
   or :n:`(_ : @type)`) in :n:`@one_term`. :tacn:`refine` generates as many
   subgoals as there are remaining holes in the elaborated term. Any subgoal
   that occurs in other subgoals is automatically shelved, as if calling
   :tacn:`shelve_unifiable`.

   `simple`
     If specified, don't shelve any subgoals or perform beta reduction.

   `notypeclasses`
     If specified, do checking without resolving typeclasses.  The generated
     subgoals (shelved or not) are *not* candidates for typeclass resolution,
     even if they have a typeclass type as their conclusion.

   .. example::

      .. rocqtop:: reset all

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

.. tacn:: apply {+, @one_term_with_bindings } {? @in_hyp_as }

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

   .. _apply_backward:
   .. example:: Backward reasoning in the goal with `apply`

      .. rocqtop:: reset none

         Goal forall A B C: Prop, (A -> B -> C) -> C.

      .. rocqtop:: out

         intros A B C H.

      .. rocqtop:: all

         apply H.  (* replace goal with new goals for unmatched premises of H *)

   .. _apply_backward_w_premises:
   .. example:: Backward reasoning in the goal with `apply` including a premise

      .. rocqtop:: reset none

         Goal forall A B C: Prop, (A -> B -> C) -> (B -> C).

      .. rocqtop:: out

         intros A B C H.

      .. rocqtop:: all

         apply H.  (* match on "B -> C", replace goal with "A" *)

   .. _apply_forward:
   .. example:: Forward reasoning in hypotheses with `apply`

      .. rocqtop:: reset none

         Goal forall A B C: Prop, B -> (A -> B -> C) -> True.

      .. rocqtop:: out

         intros A B C H0 H1.

      .. rocqtop:: all

         apply H1 in H0.  (* change H0, create new goals for unmatched premises of H1 *)

   .. _apply_with_binding_goal:
   .. example:: Apply a theorem with a binding in a goal

      :tacn:`apply` unifies the conclusion `n <= p` of the theorem
      `le_trans : forall n m p, n <= m -> m <= p -> n <= p`
      with the goal, assigning `x * x` and `y * y` in the goal
      to, repectively, `n` and `p` in theorem (backward reasoning).
      The `with` clause provides the binding for `m`:

      .. rocqtop:: reset none

         Axiom le_trans : forall n m p, n <= m -> m <= p -> n <= p.

         Goal forall (x y : nat), x <= y -> x * x <= y * y.

      .. rocqtop:: out

         intros x y H0.

      .. rocqtop:: all

         apply le_trans with (y * x).

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

      .. rocqtop:: reset none

         Axiom le_trans : forall n m p, n <= m -> m <= p -> n <= p.

         Goal forall (x y : nat), x * x <= y * y -> x <= y.

      .. rocqtop:: out

         intros x y H.

      .. rocqtop:: all

         apply le_trans with (p := y * x) in H.

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

      .. rocqtop:: reset none

         Goal forall (A B: Prop) (H1: A <-> B) (H: A), A.

      .. rocqtop:: out

         intros A B H1 H.

      .. rocqtop:: all

         apply H1.
         apply H1 in H.

   .. _example_apply_pattern:
   .. example:: Special case of second-order unification in apply

      Shows the use of the special case second-order unification described
      :ref:`here <apply_with_second_order_unification>` (after "unless").

      Note that we usually use :tacn:`induction` rather than applying ``nat_ind`` directly.

      .. rocqtop:: reset none

         Goal forall x y, x + y = y + x.

      .. rocqtop:: out

         intros.

      .. rocqtop:: all

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

   .. tacn:: eapply {+, @one_term_with_bindings } {? @in_hyp_as }

      Behaves like :tacn:`apply`, but creates
      :ref:`existential variables <Existential-Variables>`
      when Rocq is unable to deduce instantiations for variables, rather than failing.

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

   .. tacn:: simple apply {+, @one_term_with_bindings } {? @in_hyp_as }

      Behaves like :tacn:`apply` but it reasons modulo conversion only on subterms
      that contain no variables to instantiate and does not traverse tuples.
      For instance, the following example fails because it would require converting
      ``id ?foo`` and :g:`O`.

      .. _simple_apply_ex:
      .. example::

         .. rocqtop:: reset all

            Definition id (x : nat) := x.
            Parameter H : forall x y, id x = y.
            Goal O = O.
            Fail simple apply H.

      Because it reasons modulo a limited amount of conversion, :tacn:`simple apply` fails
      faster than :tacn:`apply` and it is thus well-suited for use in user-defined
      tactics that backtrack often.

   .. tacn:: simple eapply {+, @one_term_with_bindings } {? @in_hyp_as }
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

   .. rocqtop:: reset in

      Parameter R : nat -> nat -> Prop.
      Axiom Rtrans : forall x y z:nat, R x y -> R y z -> R x z.
      Parameters n m p : nat.
      Axiom Rnm : R n m.
      Axiom Rmp : R m p.

   Consider the goal ``(R n p)`` provable using the transitivity of ``R``:

   .. rocqtop:: in

      Goal R n p.

   The direct application of ``Rtrans`` with ``apply`` fails because no value
   for ``y`` in ``Rtrans`` is found by ``apply``:

   .. rocqtop:: all fail

      apply Rtrans.

   A solution is to ``apply (Rtrans n m p)`` or ``(Rtrans n m)``.

   .. rocqtop:: all

      apply (Rtrans n m p).

   Note that ``n`` can be inferred from the goal, so the following would work
   too.

   .. rocqtop:: in restart

      apply (Rtrans _ m).

   More elegantly, ``apply Rtrans with (y:=m)`` allows only mentioning the
   unknown m:

   .. rocqtop:: in restart

      apply Rtrans with (y := m).

   Another solution is to mention the proof of ``(R x y)`` in ``Rtrans``

   .. rocqtop:: all restart

      apply Rtrans with (1 := Rnm).

   … or the proof of ``(R y z)``.

   .. rocqtop:: all restart

      apply Rtrans with (2 := Rmp).

   On the opposite, one can use ``eapply`` which postpones the problem of
   finding ``m``. Then one can apply the hypotheses ``Rnm`` and ``Rmp``. This
   instantiates the existential variable and completes the proof.

   .. rocqtop:: all restart abort

      eapply Rtrans.

      apply Rnm.

      apply Rmp.

.. todo the following title isn't the greatest.  Perhaps more like "trivial tactics"
   or "simple tactics"???

.. _managingthelocalcontext:

Managing the local context
------------------------------

.. tacn:: intro {? @ident } {? @where }

   Applies the :tacn:`hnf` tactic until it finds an item that can be
   introduced in the context by removing certain constructs in the goal.
   If no item is found, the tactic fails.  The name used is
   :n:`@ident` (if specified) or from the construct, except that if the name from the
   construct already exists in the :term:`local context`, Rocq uses a fresh name
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
   if H exists in the context, Rocq will consider using `H0`, `H1`, ... until it finds an
   unused name.  Modifications to a proof can change automatically assigned names
   that subsequent tactics likely refer to, making the proofs harder to maintain.  The
   :flag:`Mangle Names` flag gives some control over how fresh names are generated (see
   :ref:`proof-maintenance`).

   Note that :tacn:`intros` lets you introduce multiple items into
   the context with a single tactic.

   :n:`@ident`
     The name to give to the introduced item.  If not given, Rocq uses the
     variable name from the :n:`forall` or `H` for premises.
     If a name such as `H` is already in use, Rocq will consider using `H0`,
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

      .. rocqtop:: reset out

         Goal forall m n, m < n -> (let x := 0 in True).

      .. rocqtop:: all

         intro m.
         intro n.
         intro H.
         intro x.

      This single `intros` tactic is equivalent to the 4 preceding `intro` tactics:

      .. rocqtop:: reset out

         Goal forall m n, m < n -> (let x := 0 in True).

      .. rocqtop:: all

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

         .. rocqtop:: reset out

            Goal forall x y : nat, x = y -> y = x.

         .. rocqtop:: all

            intros until y.

         Or:

         .. rocqtop:: reset out

            Goal forall x y : nat, x = y -> y = x.

         .. rocqtop:: all

            intros until 1.

      .. exn:: No quantified hypothesis named @ident in current goal even after head-reduction.

         The :n:`@ident` in the ``until`` clause doesn't appear as a :term:`dependent premise`.

      .. exn:: No @natural-th non dependent hypothesis in current goal even after head-reduction.

         There are fewer than :n:`@natural` premises in the goal.

.. tacn:: eintros {* @intropattern }

   Works just like :tacn:`intros` except that it creates existential variables
   for any unresolved variables rather than failing.  Typically this happens when
   using a ``%`` intropattern (see :n:`@simple_intropattern`).

.. tacn:: clear {? {? - } {+ @ident } }

   Erases *unneeded* hypotheses from the context of the current goal.  "Unneeded"
   means that the unselected hypotheses and the goal don't depend directly or
   indirectly on the erased hypotheses.  That means the hypotheses will no longer
   appear in the context and therefore can't be used in subsequent proof steps.
   Note that erasing an uneeded hypothesis may turn a goal that was provable
   into an unprovable goal.

   :n:`clear`
     All unneeded hypotheses are erased.  This may leave the context unchanged; this form
     never fails.

   :n:`clear {+ @ident }`
     Erases the named hypotheses if they are unneeded and fails otherwise.

      .. exn:: @ident is used in the conclusion.
         :undocumented:

      .. exn:: @ident is used in the hypothesis @ident.
         :undocumented:

   :n:`clear - {+ @ident }`
     Selects all hypotheses that are not named by the :n:`@ident`\s, then
     erases those that are unneeded.
     This may leave the context unchanged; this form never fails as long as the
     :n:`@ident`\s name hypotheses in the context.

   .. tacn:: clearbody {+ @ident }

      This tactic expects :n:`{+ @ident}` to be :term:`local definitions <context-local definition>`
      and clears their respective bodies.
      In other words, it turns the given definitions into assumptions.

      .. exn:: @ident is not a local definition.
         :undocumented:

   .. tacn:: clear dependent @ident

      Clears the hypothesis :token:`ident` and all the hypotheses that depend on it.

.. tacn:: revert {+ @ident }

   Moves the specified hypotheses and :term:`local definitions <context-local definition>`
   to the goal, if this respects dependencies. This is
   the inverse of :tacn:`intro`.

   .. tacn:: revert dependent @ident

      .. deprecated:: 8.18

      An alias for :tacn:`generalize dependent`.

.. tacn:: move @ident__from @where

   .. insertprodn where where

   .. prodn::
      where ::= at top
      | at bottom
      | before @ident
      | after @ident

   Moves a hypothesis :n:`@ident__from` and hypotheses that directly or indirectly
   refer to :n:`@ident__from` that appear between :n:`@ident__from` and :n:`@ident`.
   `at top` and `at bottom` are
   equivalent to giving the name of the first or last hypotheses in the context.  The
   dependent hypotheses will appear after :n:`@ident__from`, appearing in dependency order.
   This lets users show and group hypotheses in the order they prefer.  It doesn't
   change the goal or the proof term.

   .. todo: "at top and at bottom are equivalent to giving the name of the first or
      last hypotheses in the context."  Equivalent to "after first" and
      "after last"??

   .. note::

      Perhaps confusingly, "before" and "after" are interpeted with respect to the direction
      in which the hypotheses are moved rather than in the order of the resulting
      list of hypotheses.  If :n:`@ident__from` is before :n:`@ident` in the context, these
      notions are the
      same: for hypotheses `A B C`, `move A after B` gives `B A C`, whereas if :n:`@ident__from`
      is after :n:`@ident` in the context, they are the opposite: `move C after A` gives
      `C A B` because the direction of movement is reversed.

      .. todo This is dreadful behavior

   .. exn:: Cannot move @ident__from after @ident: it occurs in the type of @ident.
      :undocumented:

   .. exn:: Cannot move @ident__from after @ident: it depends on @ident.
      :undocumented:

   .. example:: move

      .. rocqtop:: reset none

         Goal forall x :nat, x = 0 -> forall y z:nat, y=y-> 0=x.

      .. rocqtop:: out

           intros x Hx y z Hy.

      .. rocqtop:: in

           (*                    x Hx y z Hy *)
           move y after z.  (*    x Hx z y Hy   (z was left of y, intuitive case) *)
           Undo.
           move z after y.  (*    x Hx z y Hy   (z was right of y, see Note above) *)
           Undo.
           move x after Hy.  (*   y z Hy x Hx   (Hx depends on x, so moved) *)
           Undo.
           move x before Hy.  (*  y z x Hx Hy *)
           Undo.
           move Hy after Hx.  (*  x y Hy Hx z *)
           Undo.
           move Hy before Hx.  (* x Hx y Hy z *)

.. tacn:: rename {+, @ident__1 into @ident__2 }

   Renames hypothesis :n:`@ident__1` into :n:`@ident__2` for each pair of :n:`@ident`\s.
   Renaming is done simultaneously, which permits swapping the names of 2 hypotheses.
   (Note that the renaming is applied in the context and the existential
   variables, but the proof term doesn't change.)

.. tacn:: set @alias_definition {? @occurrences }
          set @one_term {? @as_name } {? @occurrences }
   :name: set; _

   .. insertprodn alias_definition as_name

   .. prodn::
      alias_definition ::= ( @ident {* @simple_binder } := @term )
      simple_binder ::= @name
      | ( {+ @name } : @term )
      as_name ::= as @ident

   The first form adds a new local definition :n:`@ident := …`.  If
   :n:`@simple_binder` is not specified, the definition body is :n:`@term` and
   otherwise :n:`fun {* @simple_binder } => @term`.  Then the tactic replaces
   the body expression with the new variable :n:`@ident` in the goal or as
   specified by :n:`@occurrences`.  The tactic may succeed and add the local
   definition even if no replacements are made.

   The second form is equivalent to :n:`set (@ident := @one_term) {? @occurrences }`
   using :n:`@ident`, if present, or an auto-generated name if not provided.

   If :token:`term` or :token:`one_term` has holes (i.e. subexpressions with the
   form “`_`”), the tactic first checks that all subterms matching the pattern
   are compatible before doing the replacement using the leftmost subterm
   matching the pattern.

   .. exn:: The variable @ident is already declared.
      :undocumented:

   .. example:: set with a :n:`@simple_binder`

      :n:`set` does a simple syntactic replacement in the goal:

      .. rocqtop:: reset none

         Goal forall n, n = 0.

      .. rocqtop:: out

         intros.

      .. rocqtop:: all

         pattern n. (* without this, "set" won't replace anything in the goal *)
         set (f x := x = 0).

   .. tacn:: eset @alias_definition {? @occurrences }
             eset @one_term {? @as_name } {? @occurrences }
      :name: eset; _

      Similar to :tacn:`set`, but instead of failing because of uninstantiated
      variables, generates existential variables for them.
      In practice, this is relevant only when :tacn:`eset` is
      used as a synonym of :tacn:`epose`, i.e. when the :token:`term` does
      not occur in the goal.

.. tacn:: remember @one_term {? @as_name } {? eqn : @naming_intropattern } {? in @goal_occurrences }

   Similar to :n:`set (@ident := @one_term) in *` but creates a hypothesis using
   :term:`Leibniz equality` to remember the relation between the introduced
   variable and the term rather than creating a
   :term:`local definition <context-local definition>`.  If :n:`@as_name` is not
   specified a fresh name is used.
   Use :n:`@naming_intropattern` to name the new equation.

   .. tacn:: eremember @one_term {? @as_name } {? eqn : @naming_intropattern } {? in @goal_occurrences }

      Similar to :tacn:`remember`, but instead of failing because of uninstantiated
      variables, generates existential variables for them.

.. tacn:: pose @alias_definition
          pose @one_term {? @as_name }
   :name: pose; _

   Similar to :tacn:`set`.  Adds a :term:`local definition <context-local definition>`
   to the context but without doing any replacement.

   .. tacn:: epose @alias_definition
             epose @one_term {? @as_name }
      :name: epose; _

      Similar to :tacn:`pose`, but instead of failing because of uninstantiated
      variables, generates existential variables for them.

.. todo: the following title seems inappropriate.  How about something
   more like "Introducing new hypotheses", as in adding arbitrary terms rather
   than transformations of existing terms??  But then I think the tactics in the
   previous section (set, remember, pose, maybe decompose) should be moved into
   this section.  But maybe hard to make the section seem like an crisp, intuitive grouping.
   I can do the moving that after we've reviewed all the text.  WDYT?

   See https://github.com/coq/coq/pull/16498#discussion_r989928078

.. _controllingtheproofflow:

Controlling the proof flow
------------------------------

.. tacn:: assert ( @ident : @type ) {? by @ltac_expr3 }
          assert ( @ident := @term )
          assert @one_type {? @as_ipat } {? by @ltac_expr3 }
   :name: assert; _; _

   Adds a new hypothesis to the current subgoal and a new subgoal before
   it to prove the hypothesis.  Then, if :n:`@ltac_expr3`
   is specified, it applies that tactic to fully prove the new subgoal (and
   otherwise fails).

   The first form adds a new hypothesis named :n:`@ident` of type :n:`@type`.
   (This corresponds to the cut rule of sequent calculus.)

   The second form is equivalent to :n:`assert (@ident : @type) by exact (@term)` where
   :n:`@type` is the type of :n:`@term`.  It is also equivalent to using
   :tacn:`pose proof`. If the head of :n:`@term` is :n:`@ident`, the tactic
   is equivalent to :tacn:`specialize`.

   In the third form, if :n:`@as_ipat` isn't specified, the tactic adds the
   hypothesis :n:`@one_type` with a fresh name.  Otherwise, it transforms the
   hypothesis as specified by :n:`@as_ipat` and adds the resulting new hypotheses
   and goals.  See :ref:`intropatterns`.

   .. exn:: The term "@type" has type "@type__1" which should be Set, Prop or Type.

      Occurs when the argument :n:`@type` (in the first form) or :n:`@one_type`
      (in the third form) is not of type :g:`Prop`, :g:`Set` nor :g:`Type`.

   .. exn:: Proof is not complete.
      :name: Proof is not complete. (assert)

      :n:`@ltac_expr3` was not able to prove the new hypothesis.

   .. tacn:: eassert ( @ident : @type ) {? by @ltac_expr3 }
             eassert ( @ident := @term )
             eassert @one_type {? @as_ipat } {? by @ltac_expr3 }
      :name: eassert; _; _

      Unlike :tacn:`assert`, the :n:`@type`, :n:`@term` or :n:`@one_type` in
      :tacn:`eassert` may contain :gdef:`holes <hole>`, denoted by :n:`_`,
      for which the tactic will create existential variables.  This lets you
      avoid specifying the asserted statement completely before starting to
      prove it.

.. tacn:: enough ( @ident : @type ) {? by @ltac_expr3 }
          enough @one_type {? @as_ipat } {? by @ltac_expr3 }
   :name: enough; _

   Adds a new hypothesis to the current subgoal and a new subgoal after it
   to prove the hypothesis.

   The first form adds a new hypothesis :n:`@ident : @type`
   and :n:`@type` as the new subgoal.  Then, if :n:`@ltac_expr3` is
   specified, it applies that tactic to prove the current subgoal
   with the added hypothesis (and otherwise fails).

   In the second form, if :n:`@as_ipat` isn't specified, the tactic adds a new
   hypothesis :n:`@one_type` with a name chosen by Rocq.  Otherwise, it transforms
   :n:`@one_type` as specified by :n:`@as_ipat` and adds the resulting new hypotheses.
   The :n:`@as_ipat` may also expand the current subgoal into multiple subgoals.
   Then, if :n:`@ltac_expr3` is specified, it is applied to and must succeed on all
   of them.

   .. tacn:: eenough ( @ident : @type ) {? by @ltac_expr3 }
             eenough @one_type {? @as_ipat } {? by @ltac_expr3 }
      :name: eenough; _

      Unlike :tacn:`enough`, the :n:`@type` and :n:`@one_type` in
      :tacn:`eenough` may contain :term:`holes <hole>`, denoted by :n:`_`,
      for which the tactic will create existential variables.  This lets you
      avoid specifying the asserted statement completely until you start to use
      the hypothesis or later start to prove the statement.

.. tacn:: cut @one_type

   Implements the non-dependent case of the :ref:`App <app_rule>` typing rule,
   the Modus Ponens inference rule.  It is equivalent to
   :n:`enough (@ident: @one_type). revert @ident.`
   This tactic is generally considered obsolete but it is still widely
   used in old scripts.

.. tacn:: pose proof @term {? @as_ipat }
          pose proof ( @ident := @term )
   :name: pose proof; _

   The first form behaves like :n:`assert @one_type {? @as_ipat } by exact @term`
   where :token:`one_type` is the type of :token:`term`.

   .. Théo notes it's odd that the first form uses @term instead of @one_term

   The second form is equivalent to :n:`assert (@ident := @term)`.

   .. tacn:: epose proof @term {? @as_ipat }
             epose proof ( @ident := @term )
      :name: epose proof; _

      While :tacn:`pose proof` expects that no existential variables are generated by
      the tactic, :tacn:`epose proof` removes this constraint.

.. tacn:: specialize @one_term_with_bindings {? @as_ipat }

   Specializes a term (typically a hypothesis or a lemma) by applying arguments to it.

   *First*, the tactic generates a modified term:
   If the :term:`head constant` of :n:`@one_term` (in :n:`@one_term_with_bindings`)
   has the type `forall ...`, the tactic replaces one or more of the
   quantified variables in the type with arguments provided by
   :n:`@one_term_with_bindings`, either in the form of a
   :ref:`function application <function_application>` (which may be partial),
   such as `(H 1)`, or with named or numbered binders, such as `H with (n:=1)`.

   If the :term:`head constant` has a :term:`non-dependent product` type such as
   `A -> B -> C`, the tactic eliminates one or more of the premises
   (doing :term:`forward reasoning`).

   Uninstantiated arguments are inferred by unification, if possible, or otherwise
   left quantified in the resulting term.

   *Then*, If the :term:`head constant` is a hypothesis :n:`H`, the resulting
   term replaces that hypothesis.  Specifying :n:`@as_ipat` will leave the original
   hypothesis unchanged and will introduce new hypotheses as specified by the
   :token:`simple_intropattern`.  If :n:`H` appears in the conclusion or another
   hypothesis, you must use :n:`@as_ipat` to give a fresh hypothesis name.

   If the head constant is a lemma or theorem, the resulting term
   is added as a new premise of the goal so that the behavior is similar
   to that of :tacn:`generalize`.  In this case, you can use :n:`@as_ipat` to
   immediately introduce the modified term as one or more hypotheses.

   .. exn:: Cannot change @ident, it is used in hypothesis @ident.
      :undocumented:

   .. exn:: Cannot change @ident, it is used in conclusion.
      :undocumented:

   .. example:: partial application in :tacn:`specialize`

      .. rocqtop:: reset none

         Goal (forall n m: nat, n + m = m + n) -> True.

      .. rocqtop:: out

         intros.

      .. rocqtop:: all

         specialize (H 1). (* equivalent to: specialize H with (n := 1) *)

   .. example:: :tacn:`specialize` with a non-dependent product

      Compare this to a similar :ref:`example <apply_forward>` that uses
      :tacn:`apply`.  :tacn:`specialize` won't introduce new goals as
      :tacn:`apply` can.

      .. rocqtop:: reset none

         Goal forall A B C: Prop, B -> (A -> B -> C) -> True.
         Proof.

      .. rocqtop:: out

         intros A B C H0 H1.

      .. rocqtop:: all

         specialize H1 with (2:=H0).

   .. tacn:: specialize_eqs @ident
      :undocumented:

.. tacn:: generalize {+ @one_term }
          generalize {+, @pattern_occs {? @as_name } }
   :name: generalize; _

   For each :n:`@one_term` (which may be in the :n:`@pattern_occs`), replaces the
   goal `G` with `forall (x:T), G'`,
   where :n:`@one_term` is a subterm of `G` of type `T` and `G'` is obtained
   by replacing all occurrences of :n:`@one_term` with `x` within `G`.  `x` is
   a fresh variable chosen based on `T`.  Specifying multiple :n:`@one_term`\s is
   equivalent to :n:`generalize @one_term__n; … ; generalize @one_term__1`.
   (Note they are processed *right to left*.)

   :n:`@as_name`
     The name to use for `x` instead of a fresh name.

   .. example::

      .. rocqtop:: reset none

         Goal forall x y:nat, 0 <= x + y + y.
         Proof. intros *.

      .. rocqtop:: out

         Show.

      .. rocqtop:: all abort

         generalize (x + y + y).   (* get a simpler goal that can be proven by induction *)

   .. tacn:: generalize dependent @one_term

      Generalizes :n:`@one_term` and all hypotheses that depend on :n:`@one_term`. It
      clears the generalized hypotheses.

   .. tacn:: dependent generalize_eqs @ident
      :undocumented:

   .. tacn:: dependent generalize_eqs_vars @ident
      :undocumented:

   .. tacn:: generalize_eqs @ident
      :undocumented:

   .. tacn:: generalize_eqs_vars @ident
      :undocumented:

.. tacn:: evar ( @ident : @type )
          evar @one_type
   :name: evar; _

   The :n:`evar` tactic creates a new :term:`local definition <context-local definition>`
   named :n:`@ident` with type :n:`@type` or :n:`@one_type` in the context.
   The body of this binding is a fresh existential variable.  If the second
   form is used, Rocq chooses the name.

.. tacn:: instantiate ( @ident := @term )
          instantiate ( @natural := @term ) {? @hloc }
   :name: instantiate; _

   .. insertprodn hloc hloc

   .. prodn::
      hloc ::= in %|- *
      | in @ident
      | in ( type of @ident )
      | in ( value of @ident )

   The first form refines (see :tacn:`refine`) an existential variable
   :n:`@ident` with the term :n:`@term`. It is equivalent to
   :n:`only [@ident]: refine @term`.

   .. note:: To be able to refer to an existential variable by name, the user
             must have given the name explicitly (see :ref:`Existential-Variables`).

   .. note:: When you are referring to hypotheses which you did not name
             explicitly, be aware that Rocq may make a different decision on how to
             name the variable in the current goal and in the context of the
             existential variable. This can lead to surprising behaviors.

   The second form refines an existential variable selected by its position.  The
   :n:`@natural` argument is the position of the existential variable
   *from right to left* in the goal.  (Use the :n:`@hloc` clause
   to select an existential variable in a
   hypothesis.)  Counting starts at 1 and multiple occurrences of the
   same existential variable are counted multiple times.  Using this form
   is discouraged because slight changes to the goal may change the needed index,
   causing a maintenance issue.

   Advanced users may want to define and use an Ltac tactic to get more consistent
   behavior, such as:

   .. rocqdoc::

      Ltac instantiate_ltac_variable ev term :=
        let H := fresh in
        pose ev as H;
        instantiate (1 := term) in (value of H);
        clear H.

   :n:`in @ident`
     Selects the hypothesis :n:`@ident`.

   :n:`in %|- *`
     Selects the goal.  This is the default behavior.

   :n:`in ( type of @ident )`
     Selects existential variables in the type of the
     :term:`local definition <context-local definition>` :n:`@ident`.
     (The body is not included.)

   :n:`in ( value of @ident )`
     Selects existential variables in the body of the
     :term:`local definition <context-local definition>` :n:`@ident`.
     (The type is not included.)

.. tacn:: absurd @one_type

   :n:`@one_type` is any proposition
   :g:`P` of type :g:`Prop`. This tactic applies False elimination, that is it
   deduces the current goal from False, and generates as subgoals :g:`∼P` and
   :g:`P`. It is very useful in proofs by cases, where some cases are
   impossible. In most cases, :g:`P` or :g:`∼P` is one of the hypotheses of the
   local context.

.. tacn:: contradiction {? @one_term_with_bindings }

   Tries to prove the current goal by finding a contradiction.

   If :n:`@one_term_with_bindings` is not provided (the most common use case),
   the tactic first does an :tacn:`intros`.  The tactic then proves the goal if

   - the updated context has a pair of hypotheses where one is the negation of
     the other (e.g. :n:`P` and not :n:`~P`), or
   - there is a hypothesis with an empty inductive type (e.g. :n:`False`), or
   - there is a hypothesis :n:`~P` where `P` is a singleton inductive type
     (e.g. :n:`True` or :n:`x=x`) provable by `Goal P. constructor.`

   If :n:`@one_term_with_bindings` is provided, its type
   must be a negation, such as :n:`~P`,
   or an empty inductive type, such as :n:`False`.
   If the type is a negation and :n:`P` is a hypothesis in the context,
   the goal is proven.  If the type is a negation and :n:`P` is not in
   the context, the goal is replaced with :n:`P`.  If the type is :n:`False`
   or another empty inductive type, the goal is proven.
   Otherwise the tactic fails.  (If there is a hypothesis
   `P` and you want to replace the goal with `~P`, use the :tacn:`contradict`
   tactic.  If there are hypotheses `H1 : P` and `H2 : ~P`, use `contradiction`
   without arguments or `contradiction H2` since `contradiction H1` won't work.)

   Use the :tacn:`discriminate` tactic to prove the current goal when there
   is a hypothesis with an impossible structural equality such as
   :n:`0 = 1`.

.. example:: :tacn:`contradiction` tactic

   Simple examples.  To see more detail, add `intros` after each `Goal`.

   .. rocqtop:: reset in

      Inductive F :=. (* Another empty inductive type *)

      Goal F -> False.
      contradiction.
      Qed.

      Goal forall (A : Prop), A -> ~A -> False.
      contradiction.
      Qed.

      Goal forall (A : Type) (x : A), ~(x = x) -> False.
      contradiction.
      Qed.

   Apply a fact from the standard library:

   .. rocqtop:: none

      Axiom lt_irrefl : forall x, ~ (x < x).

   .. rocqtop:: in

      Goal forall (A : Prop), 0 < 0 -> A.

   .. rocqtop:: all

      intros.
      contradiction (lt_irrefl 0).
      Qed.

.. tacn:: contradict @ident

   Transforms the specified hypothesis :n:`@ident` and the goal in order to
   prove that the hypothesis is false. For :n:`contradict H`, the
   current goal and context are transformed as shown.  (For brevity,
   `⊢` is used to separate hypotheses from the goal; it is equivalent to the
   dividing line shown in a context.):

   + `H: ~A ⊢ B` becomes `⊢ A`
   + `H: ~A ⊢ ~B` becomes `H: B ⊢ A`
   + `H: A ⊢ B` becomes `⊢ ~A`
   + `H: A ⊢ ~B` becomes `H: B ⊢ ~A`

.. tacn:: exfalso

   Implements the “ex falso quodlibet” logical principle: an
   elimination of False is performed on the current goal, and the user is
   then required to prove that False is indeed provable in the current
   context.

Classical tactics
-----------------

In order to ease the proving process, when the ``Classical`` module is
loaded, a few more tactics are available. Make sure to load the module
using the :cmd:`Require Import` command.

.. tacn:: classical_left
          classical_right

   These tactics are the analog of :tacn:`left` and :tacn:`right`
   but using classical logic. They can only be used for
   disjunctions. Use :tacn:`classical_left` to prove the left part of the
   disjunction with the assumption that the negation of right part holds.
   Use :tacn:`classical_right` to prove the right part of the disjunction with
   the assumption that the negation of left part holds.

Performance-oriented tactic variants
------------------------------------

.. todo: move the following adjacent to the `exact` tactic?

.. tacn:: exact_no_check @one_term

   For advanced usage. Similar to :tacn:`exact` :n:`@term`, but as an optimization,
   it skips checking that :n:`@term` has the goal's type, relying on the kernel
   check instead. See :tacn:`change_no_check` for more explanation.

   .. example::

      .. rocqtop:: all abort

         Goal False.
           exact_no_check I.
         Fail Qed.

   .. tacn:: vm_cast_no_check @one_term

      For advanced usage. Similar to :tacn:`exact_no_check` :n:`@term`, but additionally
      instructs the kernel to use :tacn:`vm_compute` to compare the
      goal's type with the :n:`@term`'s type.

      .. example::

        .. rocqtop:: all abort

            Goal False.
              vm_cast_no_check I.
            Fail Qed.

   .. tacn:: native_cast_no_check @one_term

      for advanced usage. similar to :tacn:`exact_no_check` :n:`@term`, but additionally
      instructs the kernel to use :tacn:`native_compute` to compare the goal's
      type with the :n:`@term`'s type.

      .. example::

        .. rocqtop:: all abort

            Goal False.
              native_cast_no_check I.
            Fail Qed.
