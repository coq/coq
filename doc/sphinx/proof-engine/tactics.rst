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

   This option controls the default selector, used when no selector is
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
  the ``n``-th non dependent premise of :n:`@term__tac`.

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

.. prodn::
   intropattern_list ::= {* @intropattern }
   intropattern ::= *
   | **
   | @simple_intropattern
   simple_intropattern ::= @simple_intropattern_closed {* % @term0 }
   simple_intropattern_closed ::= @naming_intropattern
   | _
   | @or_and_intropattern
   | @rewriting_intropattern
   | @injection_intropattern
   naming_intropattern ::= @ident
   | ?
   | ?@ident
   or_and_intropattern ::= [ {*| @intropattern_list } ]
   | ( {*, @simple_intropattern } )
   | ( {*& @simple_intropattern } )
   rewriting_intropattern ::= ->
   | <-
   injection_intropattern ::= [= @intropattern_list ]
   or_and_intropattern_loc ::= @or_and_intropattern
   | ident

Note that the intro pattern syntax varies between tactics.
Most tactics use :n:`@simple_intropattern` in the grammar.
:tacn:`destruct`, :tacn:`edestruct`, :tacn:`induction`,
:tacn:`einduction`, :tacn:`case`, :tacn:`ecase` and the various
:tacn:`inversion` tactics use :n:`@or_and_intropattern_loc`, while
:tacn:`intros` and :tacn:`eintros` use :n:`@intropattern_list`.
The :n:`eqn:` construct in various tactics uses :n:`@naming_intropattern`.

**Naming patterns**

Use these elementary patterns to specify a name:

* :n:`@ident` — use the specified name
* :n:`?` — let Coq choose a name
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

* :n:`[ {+| @intropattern_list} ]` — splits an inductive type that has
  :ref:`multiple constructors <intropattern_cons_note>`
  such as :n:`A \/ B`
  into multiple subgoals.  The number of :token:`intropattern_list` must be the same as the number of
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

.. _occurrencessets:

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

   Tactics that select a specific hypothesis H to apply to other hypotheses,
   such as :tacn:`rewrite` `H in * |-`, won't apply H to itself.

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

.. tacn:: exact @one_term

   This tactic applies to any goal. It gives directly the exact proof
   term of the goal. Let ``T`` be our goal, let ``p`` be a term of type ``U`` then
   ``exact p`` succeeds iff ``T`` and ``U`` are convertible (see
   :ref:`Conversion-rules`).

   .. exn:: Not an exact proof.
      :undocumented:

   .. tacn:: eexact @one_term

      This tactic behaves like :tacn:`exact` but is able to handle terms and
      goals with existential variables.

.. tacn:: assumption

   This tactic looks in the local context for a hypothesis whose type is
   convertible to the goal. If it is the case, the subgoal is proved.
   Otherwise, it fails.

   .. exn:: No such assumption.
      :undocumented:

   .. tacn:: eassumption

      This tactic behaves like :tacn:`assumption` but is able to handle
      goals with existential variables.

.. tacn:: refine @one_term

   This tactic applies to any goal. It behaves like :tacn:`exact` with a big
   difference: the user can leave some holes (denoted by ``_``
   or :n:`(_ : @type)`) in the term. :tacn:`refine` will generate as many
   subgoals as there are remaining holes in the elaborated term. The type
   of holes must be either synthesized by the system or declared by an explicit cast
   like ``(_ : nat -> Prop)``. Any subgoal that
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

   .. tacn:: simple refine @one_term

      This tactic behaves like refine, but it does not shelve any subgoal. It does
      not perform any beta-reduction either.

   .. tacn:: notypeclasses refine @one_term

      This tactic behaves like :tacn:`refine` except it performs type checking without
      resolution of typeclasses.

   .. tacn:: simple notypeclasses refine @one_term

      This tactic behaves like the combination of :tacn:`simple refine` and
      :tacn:`notypeclasses refine`: it performs type checking without resolution of
      typeclasses, does not perform beta reductions or shelve the subgoals.

   :opt:`Debug` ``"unification"`` enables printing traces of
   unification steps used during elaboration/typechecking and the
   :tacn:`refine` tactic. ``"ho-unification"`` prints information
   about higher order heuristics.

.. tacn:: apply {+, @constr_with_bindings_arg } {? @in_hyp_as }

   .. insertprodn in_hyp_as as_ipat

   .. prodn::
      in_hyp_as ::= in {+, @ident {? @as_ipat } }
      as_ipat ::= as @simple_intropattern

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

   .. tacv:: apply {+, @term}

      This is a shortcut for :n:`apply @term__1; [.. | ... ; [ .. | apply @term__n] ... ]`,
      i.e. for the successive applications of :n:`@term`:sub:`i+1` on the last subgoal
      generated by :n:`apply @term__i` , starting from the application of :n:`@term__1`.

   .. tacn:: eapply {+, @constr_with_bindings_arg } {? @in_hyp_as }

      The tactic :tacn:`eapply` behaves like :tacn:`apply` but it does not fail when no
      instantiations are deducible for some variables in the premises. Rather, it
      turns these variables into existential variables which are variables still to
      instantiate (see :ref:`Existential-Variables`). The instantiation is
      intended to be found later in the proof.

   .. tacn:: rapply @one_term

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

   .. tacn:: simple apply {+, @constr_with_bindings_arg } {? @in_hyp_as }

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
      :name: simple apply XXXX; simple eapply

      This summarizes the different syntaxes for :tacn:`apply` and :tacn:`eapply`.

   .. tacn:: lapply @one_term

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

.. flag:: Universal Lemma Under Conjunction

   This flag, which preserves compatibility with versions of Coq prior to
   8.4 is also available for :n:`apply @term in @ident` (see :tacn:`apply … in`).

.. tacv:: apply @term in @ident
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

.. tacn:: constructor {? @nat_or_var } {? with @bindings }

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

   .. tacn:: split {? with @bindings }

      This applies only if :g:`I` has a single constructor. It is then
      equivalent to :n:`constructor 1 {? with @bindings }`. It is
      typically used in the case of a conjunction :math:`A \wedge B`.

      .. tacn:: exists {? {+, @bindings } }

         This applies only if :g:`I` has a single constructor. It is then equivalent
         to :n:`intros; constructor 1 with @bindings.` It is typically used in
         the case of an existential quantification :math:`\exists x, P(x).`

      .. tacv:: exists {+, @bindings }

         This iteratively applies :n:`exists @bindings`.

      .. exn:: Not an inductive goal with 1 constructor.
         :undocumented:

   .. tacn:: left {? with @bindings }
             right {? with @bindings }

      These tactics apply only if :g:`I` has two constructors, for
      instance in the case of a disjunction :math:`A \vee B`.
      Then, they are respectively equivalent to
      :n:`constructor 1 {? with @bindings }` and
      :n:`constructor 2 {? with @bindings }`.

      .. exn:: Not an inductive goal with 2 constructors.
         :undocumented:

   .. tacn:: econstructor {? @nat_or_var {? with @bindings } }
             eexists {? {+, @bindings } }
             esplit {? with @bindings }
             eleft {? with @bindings }
             eright {? with @bindings }

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

.. tacn:: intro {? @ident } {? @where }

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

   .. tacn:: intros {* @intropattern }

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
      followed by the appropriate call to :tacn:`move` `… after …`,
      :tacn:`move … before …`, :tacn:`move … at top`,
      or :tacn:`move … at bottom`.

      .. note::

         :n:`intro at bottom` is a synonym for :n:`intro` with no argument.

      .. exn:: No such hypothesis: @ident.
         :undocumented:

.. tacn:: intros {* @intropattern }

   Introduces one or more variables or hypotheses from the goal by matching the
   intro patterns.  See the description in :ref:`intropatterns`.

.. tacn:: eintros {* @intropattern }

   Works just like :tacn:`intros` except that it creates existential variables
   for any unresolved variables rather than failing.

.. tacn:: clear @natural

   This tactic erases the hypothesis named :n:`@ident` in the local context of
   the current goal. As a consequence, :n:`@ident` is no more displayed and no
   more usable in the proof development.

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: @ident is used in the conclusion.
      :undocumented:

   .. exn:: @ident is used in the hypothesis @ident.
      :undocumented:

   .. tacn:: clear {* @ident }

      This is equivalent to :n:`clear @ident. ... clear @ident.`

   .. tacv:: clear - {+ @ident}

      This variant clears all the hypotheses except the ones depending in the
      hypotheses named :n:`{+ @ident}` and in the goal.

   .. tacv:: clear

      This variants clears all the hypotheses except the ones the goal depends on.

   .. tacv:: clear dependent @ident

      This clears the hypothesis :token:`ident` and all the hypotheses that
      depend on it.

   .. tacn:: clearbody {+ @ident }

      This tactic expects :n:`{+ @ident}` to be local definitions and clears
      their respective bodies.
      In other words, it turns the given definitions into assumptions.

      .. exn:: @ident is not a local definition.
         :undocumented:

.. tacn:: revert {+ @ident }

   This applies to any goal with variables :n:`{+ @ident}`. It moves the hypotheses
   (possibly defined) to the goal, if this respects dependencies. This tactic is
   the inverse of :tacn:`intro`.

   .. exn:: No such hypothesis.
      :undocumented:

   .. exn:: @ident__1 is used in the hypothesis @ident__2.
      :undocumented:

   .. tacn:: revert dependent @ident

      This moves to the goal the hypothesis :token:`ident` and all the
      hypotheses that depend on it.

.. tacn:: move @ident {? @where }

   .. insertprodn where where

   .. prodn::
      where ::= at top
      | at bottom
      | after @ident
      | before @ident

   This moves the hypothesis named :n:`@ident` in the local context after
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
      named :n:`@ident__2`.  As for :tacn:`move` `… after …`, dependencies
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

.. tacn:: rename {+, @ident__1 into @ident__2 }

   For each pair of :n:`ident`\s, renames hypothesis :n:`@ident__1` into :n:`@ident__2`
   in the current context. The name of the hypothesis in the proof-term, however, is left
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

.. tacn:: set @bindings_with_parameters {? @occurrences }

   .. insertprodn bindings_with_parameters simple_binder

   .. prodn::
      bindings_with_parameters ::= ( @ident {* @simple_binder } := @term )
      simple_binder ::= @name
      | ( {+ @name } : @term )

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

   .. tacn:: eset @bindings_with_parameters {? @occurrences }
             eset @one_term {? @as_name } {? @occurrences }
      :name: eset; _

      .. insertprodn as_name as_name

      .. prodn::
         as_name ::= as @ident

      While the different variants of :tacn:`set` expect that no existential
      variables are generated by the tactic, :tacn:`eset` removes this
      constraint. In practice, this is relevant only when :tacn:`eset` is
      used as a synonym of :tacn:`epose`, i.e. when the :token:`term` does
      not occur in the goal.

.. tacn:: remember @one_term {? @as_name } {? @eqn_ipat } {? @clause_dft_all }

   .. insertprodn clause_dft_all eqn_ipat

   .. prodn::
      clause_dft_all ::= in @goal_occurrences
      eqn_ipat ::= eqn : @naming_intropattern

   This behaves as :n:`set (@ident := @term) in *`, using a logical
   (Leibniz’s) equality instead of a local definition.
   Use :n:`@naming_intropattern` to name or split up the new equation.

   .. tacv:: remember @term as @ident__1 {? eqn:@naming_intropattern } in @goal_occurrences

      This is a more general form of :tacn:`remember` that remembers the
      occurrences of :token:`term` specified by an occurrence set.

   .. tacn:: eremember @one_term {? @as_name } {? @eqn_ipat } {? @clause_dft_all }

      While the different variants of :tacn:`remember` expect that no
      existential variables are generated by the tactic, :tacn:`eremember`
      removes this constraint.

.. tacn:: pose @bindings_with_parameters

   This adds the local definition :n:`@ident := @term` to the current context
   without performing any replacement in the goal or in the hypotheses. It is
   equivalent to :n:`set (@ident := @term) in |-`.

   .. tacv:: pose (@ident {* @binder } := @term)

      This is equivalent to :n:`pose (@ident := fun {* @binder } => @term)`.

   .. tacv:: pose @term

      This behaves as :n:`pose (@ident := @term)` but :token:`ident` is
      generated by Coq.

   .. tacn:: epose @bindings_with_parameters
             epose @one_term {? @as_name }
      :name: epose; _

      While the different variants of :tacn:`pose` expect that no
      existential variables are generated by the tactic, :tacn:`epose`
      removes this constraint.

.. tacn:: decompose [ {+ @one_term } ] @one_term

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

   .. tacn:: decompose sum @one_term

      This decomposes sum types (like :g:`or`).

   .. tacv:: decompose record @term

      This decomposes record types (inductive types with one constructor,
      like :g:`and` and :g:`exists` and those defined with the :cmd:`Record`
      command.


.. _controllingtheproofflow:

Controlling the proof flow
------------------------------

.. tacn:: assert ( @ident : @term ) {? by @ltac_expr3 }
          assert ( @ident := @term )
   :name: assert; _

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

.. tacn:: eassert @one_term {? @as_ipat } {? by @ltac_expr3 }

   While the different variants of :tacn:`assert` expect that no existential
   variables are generated by the tactic, :tacn:`eassert` removes this constraint.
   This lets you avoid specifying the asserted statement completely before starting
   to prove it.

.. tacn:: pose proof @term {? @as_ipat }

   This tactic behaves like :n:`assert @type {? as @simple_intropattern} by exact @term`
   where :token:`type` is the type of :token:`term`. In particular,
   :n:`pose proof @term as @ident` behaves as :n:`assert (@ident := @term)`
   and :n:`pose proof @term as @simple_intropattern` is the same as applying the
   :token:`simple_intropattern` to :token:`term`.

.. tacn:: epose proof @term {? @as_ipat }

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

.. tacn:: enough ( @ident : @term ) {? by @ltac_expr3 }

   This adds a new hypothesis of name :token:`ident` asserting :token:`type` to the
   goal the tactic :tacn:`enough` is applied to. A new subgoal stating :token:`type` is
   inserted after the initial goal rather than before it as :tacn:`assert` would do.

.. tacv:: enough @type

   This behaves like :n:`enough (@ident : @type)` with the name :token:`ident` of
   the hypothesis generated by Coq.

.. tacn:: enough @one_term {? @as_ipat } {? by @ltac_expr3 }

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

.. tacn:: cut @one_term

   This tactic applies to any goal. It implements the non-dependent case of
   the “App” rule given in :ref:`typing-rules`. (This is Modus Ponens inference
   rule.) :n:`cut U` transforms the current goal :g:`T` into the two following
   subgoals: :g:`U -> T` and :g:`U`. The subgoal :g:`U -> T` comes first in the
   list of remaining subgoal to prove.

.. tacn:: specialize @one_term {? with @bindings } {? as @simple_intropattern }
   :name: specialize

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

.. tacn:: generalize @one_term {? at @occs_nums } {? @as_name } {* , @pattern_occs {? @as_name } }
          generalize @one_term {? {+ @one_term } }
   :name: generalize; _

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

.. tacn:: evar ( @ident : @term )

   The :n:`evar` tactic creates a new local definition named :n:`@ident` with type
   :n:`@term` in the context. The body of this binding is a fresh existential
   variable.

.. tacn:: instantiate ( @ident := @term )
          instantiate ( @integer := @term ) {? @hloc }
   :name: instantiate; _

   .. insertprodn hloc hloc

   .. prodn::
      hloc ::= in %|- *
      | in @ident
      | in ( Type of @ident )
      | in ( Value of @ident )
      | in ( type of @ident )
      | in ( value of @ident )

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

   This tactic allows temporarily skipping a subgoal so as to
   progress further in the rest of the proof. A proof containing admitted
   goals cannot be closed with :cmd:`Qed` but only with :cmd:`Admitted`.

.. todo : belongs in this chapter of proof-mode? .. tacn:: give_up

   Synonym of :tacn:`admit`.

.. tacn:: absurd @one_term

   This tactic applies to any goal. The argument term is any proposition
   :g:`P` of type :g:`Prop`. This tactic applies False elimination, that is it
   deduces the current goal from False, and generates as subgoals :g:`∼P` and
   :g:`P`. It is very useful in proofs by cases, where some cases are
   impossible. In most cases, :g:`P` or :g:`∼P` is one of the hypotheses of the
   local context.

.. tacn:: contradiction {? @one_term {? with @bindings } }

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

   This tactic allows manipulating negated hypothesis and goals. The name
   :n:`@ident` should correspond to a hypothesis. With :n:`contradict H`, the
   current goal and context is transformed in the following way:

   + H:¬A ⊢ B becomes ⊢ A
   + H:¬A ⊢ ¬B becomes H: B ⊢ A
   + H: A ⊢ B becomes ⊢ ¬A
   + H: A ⊢ ¬B becomes H: B ⊢ ¬A

.. tacn:: exfalso

   This tactic implements the “ex falso quodlibet” logical principle: an
   elimination of False is performed on the current goal, and the user is
   then required to prove that False is indeed provable in the current
   context. This tactic is a macro for :n:`elimtype False`.

.. _CaseAnalysisAndInduction:

Case analysis and induction
-------------------------------

The tactics presented in this section implement induction or case
analysis on inductive or co-inductive objects (see :ref:`inductive-definitions`).

.. tacn:: destruct @induction_clause_list

   .. insertprodn induction_clause_list opt_clause

   .. prodn::
      induction_clause_list ::= {+, @induction_clause } {? using @one_term {? with @bindings } } {? @opt_clause }
      induction_clause ::= @destruction_arg {? @as_or_and_ipat } {? @eqn_ipat } {? @opt_clause }
      opt_clause ::= in @goal_occurrences
      | at @occs_nums

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

   .. tacn:: edestruct @induction_clause_list

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

.. tacn:: case @induction_clause_list

   The tactic :n:`case` is a more basic tactic to perform case analysis without
   recursion. It behaves as :n:`elim @term` but using a case-analysis
   elimination principle and not a recursive one.

.. tacv:: case @term with @bindings

   Analogous to :n:`elim @term with @bindings` above.

.. tacn:: ecase @induction_clause_list

   In case the type of :n:`@term` has dependent premises, or dependent premises
   whose values are not inferable from the :n:`with @bindings` clause,
   :n:`ecase` turns them into existential variables to be resolved later on.

.. tacn:: simple destruct {| @ident | @natural }

   This tactic behaves as :n:`intros until @ident; case @ident` when :n:`@ident`
   is a quantified variable of the goal.

.. tacv:: simple destruct @natural

   This tactic behaves as :n:`intros until @natural; case @ident` where :n:`@ident`
   is the name given by :n:`intros until @natural` to the :n:`@natural` -th
   non-dependent premise of the goal.

.. tacn:: case_eq @induction_clause_list

   The tactic :n:`case_eq` is a variant of the :n:`case` tactic that allows to
   perform case analysis on a term without completely forgetting its original
   form. This is done by generating equalities between the original form of the
   term and the outcomes of the case analysis.

.. tacn:: induction @induction_clause_list

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
   disjunctive/conjunctive introduction pattern (see :tacn:`intros`). For
   instance, for an inductive type with  one constructor, the pattern notation
   :n:`(p`:sub:`1` :n:`, ... , p`:sub:`n` :n:`)` can be used instead of
   :n:`[ p`:sub:`1` :n:`... p`:sub:`n` :n:`]`.

.. tacv:: induction @term with @bindings

   This behaves like :tacn:`induction` providing explicit instances for the
   premises of the type of :n:`term` (see :ref:`bindings`).

.. tacn:: einduction @induction_clause_list

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

.. tacn:: elim @constr_with_bindings_arg {? using @one_term {? with @bindings } }

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

.. tacn:: eelim @constr_with_bindings_arg {? using @one_term {? with @bindings } }

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

.. tacn:: elimtype @one_term

   The argument :token:`type` must be inductively defined. :n:`elimtype I` is
   equivalent to :n:`cut I. intro Hn; elim Hn; clear Hn.` Therefore the
   hypothesis :g:`Hn` will not appear in the context(s) of the subgoal(s).
   Conversely, if :g:`t` is a :n:`@term` of (inductive) type :g:`I` that does
   not occur in the goal, then :n:`elim t` is equivalent to
   :n:`elimtype I; 2:exact t.`

.. tacn:: simple induction {| @ident | @natural }

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

   This performs the generalization of the instance :n:`@ident` but uses
   ``destruct`` instead of induction on the generalized hypothesis. This gives
   results equivalent to ``inversion`` or ``dependent inversion`` if the
   hypothesis is dependent.

See also the larger example of :tacn:`dependent induction`
and an explanation of the underlying technique.

.. seealso:: :tacn:`functional induction`

.. tacn:: discriminate {? @destruction_arg }

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

.. tacn:: ediscriminate {? @destruction_arg }
          ediscriminate {? @destruction_arg }
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

.. tacn:: injection {? @destruction_arg } {? as {* @simple_intropattern } }

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

   .. tacn:: einjection {? @destruction_arg } {? as {* @simple_intropattern } }
      :name: einjection

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

.. tacn:: inversion {| @ident | @natural } using @one_term {? in {+ @ident } }
          inversion {| @ident | @natural } {? @as_or_and_ipat } {? in {+ @ident } }
   :name: inversion; _

   .. insertprodn as_or_and_ipat equality_intropattern

   .. prodn::
      as_or_and_ipat ::= as @or_and_intropattern_loc
      | as @equality_intropattern
      equality_intropattern ::= ->
      | <-
      | [= {* @intropattern } ]

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

.. tacn:: inversion_clear {| @ident | @natural } {? @as_or_and_ipat } {? in {+ @ident } }

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

.. todo PR: expand "dependent" tactic in editing

.. tacv:: dependent inversion @ident

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

.. tacn:: simple inversion {| @ident | @natural } {? @as_or_and_ipat } {? in {+ @ident } }

   It is a very primitive inversion tactic that derives all the necessary
   equalities but it does not simplify the constraints as ``inversion`` does.

.. tacv:: simple inversion @ident as @or_and_intropattern_loc

   This allows naming the hypotheses introduced in the context by
   ``simple inversion``.

.. tacv:: inversion @ident using @ident
   :name: inversion ... using ...

   .. todo using … instead of ... in the name above gives a Sphinx error, even though
      this works just find for :tacn:`move` `… after …`

   Let :n:`@ident` have type :g:`(I t)` (:g:`I` an inductive predicate) in the
   local context, and :n:`@ident` be a (dependent) inversion lemma. Then, this
   tactic refines the current goal with the specified lemma.

.. tacv:: inversion @ident using @ident in {+ @ident}

   This tactic behaves as generalizing :n:`{+ @ident}`, then doing
   :n:`inversion @ident using @ident`.

.. tacn:: inversion_sigma

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

.. tacn:: fix @ident @natural {? with {+ @fixdecl } }

   .. insertprodn fixdecl struct_annot

   .. prodn::
      fixdecl ::= ( @ident {* @simple_binder } {? @struct_annot } : @term )
      struct_annot ::= %{ struct @name %}

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

.. tacn:: cofix @ident {? with {+ @cofixdecl } }

   .. insertprodn cofixdecl cofixdecl

   .. prodn::
      cofixdecl ::= ( @ident {* @simple_binder } : @term )

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

.. tacn:: constr_eq @one_term @one_term

   This tactic checks whether its arguments are equal modulo alpha
   conversion, casts and universe constraints. It may unify universes.

.. exn:: Not equal.
   :undocumented:

.. exn:: Not equal (due to universes).
   :undocumented:

.. tacn:: constr_eq_strict @one_term @one_term

   This tactic checks whether its arguments are equal modulo alpha
   conversion, casts and universe constraints. It does not add new
   constraints.

.. exn:: Not equal.
   :undocumented:

.. exn:: Not equal (due to universes).
   :undocumented:

.. tacn:: unify @one_term @one_term {? with @ident }

   This tactic checks whether its arguments are unifiable, potentially
   instantiating existential variables.

.. exn:: Unable to unify @term with @term.
   :undocumented:

.. tacv:: unify @term @term with @ident

   Unification takes the transparency information defined in the hint database
   :n:`@ident` into account (see :ref:`the hints databases for auto and eauto <thehintsdatabasesforautoandeauto>`).

.. tacn:: is_evar @one_term

   This tactic checks whether its argument is a current existential
   variable. Existential variables are uninstantiated variables generated
   by :tacn:`eapply` and some other tactics.

.. exn:: Not an evar.
   :undocumented:

.. tacn:: has_evar @one_term

   This tactic checks whether its argument has an existential variable as
   a subterm. Unlike context patterns combined with ``is_evar``, this tactic
   scans all subterms, including those under binders.

.. exn:: No evars.
   :undocumented:

.. tacn:: is_var @one_term

   This tactic checks whether its argument is a variable or hypothesis in
   the current local context.

.. exn:: Not a variable or hypothesis.
   :undocumented:

Equality
--------


.. tacn:: f_equal

   This tactic applies to a goal of the form :g:`f a`:sub:`1` :g:`... a`:sub:`n`
   :g:`= f′a′`:sub:`1` :g:`... a′`:sub:`n`.  Using :tacn:`f_equal` on such a goal
   leads to subgoals :g:`f=f′` and :g:`a`:sub:`1` = :g:`a′`:sub:`1` and so on up
   to :g:`a`:sub:`n` :g:`= a′`:sub:`n`. Amongst these subgoals, the simple ones
   (e.g. provable by :tacn:`reflexivity` or :tacn:`congruence`) are automatically
   solved by :tacn:`f_equal`.


.. tacn:: reflexivity

   This tactic applies to a goal that has the form :g:`t=u`. It checks that `t`
   and `u` are convertible and then solves the goal. It is equivalent to
   ``apply refl_equal``.

   .. exn:: The conclusion is not a substitutive equation.
      :undocumented:

   .. exn:: Unable to unify ... with ...
      :undocumented:


.. tacn:: symmetry {? in @goal_occurrences }

   This tactic applies to a goal that has the form :g:`t=u` and changes it into
   :g:`u=t`.


.. tacv:: symmetry in @ident

   If the statement of the hypothesis ident has the form :g:`t=u`, the tactic
   changes it to :g:`u=t`.


.. tacn:: transitivity @one_term

   This tactic applies to a goal that has the form :g:`t=u` and transforms it
   into the two subgoals :n:`t=@term` and :n:`@term=u`.

   .. tacn:: etransitivity

      This tactic behaves like :tacn:`transitivity`, using a fresh evar instead of
      a concrete :token:`term`.


Equality and inductive sets
---------------------------

We describe in this section some special purpose tactics dealing with
equality and inductive sets or types. These tactics use the
equality :g:`eq:forall (A:Type), A->A->Prop`, simply written with the infix
symbol :g:`=`.

.. tacn:: decide equality

   This tactic solves a goal of the form :g:`forall x y : R, {x = y} + {~ x = y}`,
   where :g:`R` is an inductive type such that its constructors do not take
   proofs or functions as arguments, nor objects in dependent types. It
   solves goals of the form :g:`{x = y} + {~ x = y}` as well.

.. tacn:: compare @one_term @one_term

   This tactic compares two given objects :n:`@term` and :n:`@term` of an
   inductive datatype. If :g:`G` is the current goal, it leaves the sub-
   goals :n:`@term =@term -> G` and :n:`~ @term = @term -> G`. The type of
   :n:`@term` and :n:`@term` must satisfy the same restrictions as in the
   tactic ``decide equality``.

.. tacn:: simplify_eq {? @destruction_arg }

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

.. tacn:: esimplify_eq {? @destruction_arg }
          esimplify_eq {? @destruction_arg }
   :name: esimplify_eq; _

   This works the same as :tacn:`simplify_eq` but if the type of :n:`@term`, or the
   type of the hypothesis referred to by :n:`@natural`, has uninstantiated
   parameters, these parameters are left as existential variables.

.. tacv:: simplify_eq

   If the current goal has form :g:`t1 <> t2`, it behaves as
   :n:`intro @ident; simplify_eq @ident`.

.. tacn:: dependent rewrite {? {| -> | <- } } @one_term {? in @ident }
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

   These tactics are the analog of :tacn:`left` and :tacn:`right`
   but using classical logic. They can only be used for
   disjunctions. Use :tacn:`classical_left` to prove the left part of the
   disjunction with the assumption that the negation of right part holds.
   Use :tacn:`classical_right` to prove the right part of the disjunction with
   the assumption that the negation of left part holds.

Delaying solving unification constraints
----------------------------------------

.. tacn:: solve_constraints
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

   Specifies the prefix to use when generating names.

Performance-oriented tactic variants
------------------------------------

.. todo: move the following adjacent to the `exact` tactic in the rewriting chapter?

.. tacn:: exact_no_check @one_term

   For advanced usage. Similar to :tacn:`exact` :n:`@term`, but as an optimization,
   it skips checking that :n:`@term` has the goal's type, relying on the kernel
   check instead. See :tacn:`change_no_check` for more explanation.

   .. example::

      .. coqtop:: all abort

         Goal False.
           exact_no_check I.
         Fail Qed.

   .. tacn:: vm_cast_no_check @one_term

      For advanced usage. Similar to :tacn:`exact_no_check` :n:`@term`, but additionally
      instructs the kernel to use :tacn:`vm_compute` to compare the
      goal's type with the :n:`@term`'s type.

      .. example::

        .. coqtop:: all abort

            Goal False.
              vm_cast_no_check I.
            Fail Qed.

   .. tacn:: native_cast_no_check @one_term

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
