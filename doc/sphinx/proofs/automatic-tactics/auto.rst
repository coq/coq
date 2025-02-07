.. _automation:

=========================
Programmable proof search
=========================

Tactics
-------

.. tacn:: auto {? @nat_or_var } {? @auto_using } {? @hintbases }

   .. insertprodn auto_using hintbases

   .. prodn::
      auto_using ::= using {+, @one_term }
      hintbases ::= with *
      | with {+ @ident }

   Implements a Prolog-like resolution procedure to solve the
   current goal. It first tries to solve the goal using the :tacn:`assumption`
   tactic, then it reduces the goal to an atomic one using :tacn:`intros` and
   introduces the newly generated hypotheses as hints. Then it looks at
   the list of tactics associated with the head symbol of the goal and
   tries to apply one of them.  This process is recursively applied to the
   generated subgoals.

   Within each hintbase, lower cost tactics are tried before higher-cost
   tactics.  When multiple hintbases are specified, all hints in the
   first database are tried before any in the second database (and so forth)
   regardless of their cost (unlike :tacn:`eauto` and :tacn:`typeclasses eauto`).

   :n:`@nat_or_var`
     Specifies the maximum search depth.  The default is 5.

   :n:`using {+, @one_term }`

      Uses lemmas :n:`{+, @one_term }` in addition to hints. If :n:`@one_term` is an
      inductive type, the collection of its constructors are added as hints.

      Note that hints passed through the `using` clause are used in the same
      way as if they were passed through a hint database. Consequently,
      they use a weaker version of :tacn:`apply` and :n:`auto using @one_term`
      may fail where :n:`apply @one_term` succeeds.

      .. todo
         Given that this can be seen as counter-intuitive, it could be useful
         to have an option to use full-blown :tacn:`apply` for lemmas passed
         through the `using` clause. Contributions welcome!

   :n:`with *`
     Use all existing hint databases. Using this variant is highly discouraged
     in finished scripts since it is both slower and less robust than explicitly
     selecting the required databases.

   :n:`with {+ @ident }`
     Use the hint databases :n:`{+ @ident}` in addition to the database ``core``.
     Use the fake database `nocore` to omit `core`.

   If no `with` clause is given, :tacn:`auto` only uses the hypotheses of the
   current goal and the hints of the database named ``core``.

   :tacn:`auto` generally either completely solves the goal or
   leaves it unchanged.  Use :tacn:`solve` `[ auto ]` if you want a failure
   when they don't solve the goal.  :tacn:`auto` will fail if :tacn:`fail`
   or :tacn:`gfail` are invoked directly or indirectly, in which case setting
   the :flag:`Ltac Debug` may help you debug the failure.

   .. warning::

      :tacn:`auto` uses a weaker version of :tacn:`apply` that is closer to
      :tacn:`simple apply` so it is expected that sometimes :tacn:`auto` will
      fail even if applying manually one of the hints would succeed.

   .. seealso::
      :ref:`hintdatabases` for the list of
      pre-defined databases and the way to create or extend a database.

   .. tacn:: info_auto {? @nat_or_var } {? @auto_using } {? @hintbases }

      Behaves like :tacn:`auto` but shows the tactics it uses to solve the goal. This
      variant is very useful for getting a better understanding of automation, or
      to know what lemmas/assumptions were used.

   .. tacn:: debug auto {? @nat_or_var } {? @auto_using } {? @hintbases }

      Behaves like :tacn:`auto` but shows the tactics it tries to solve the goal,
      including failing paths.

.. tacn:: trivial {? @auto_using } {? @hintbases }
          debug trivial {? @auto_using } {? @hintbases }
          info_trivial {? @auto_using } {? @hintbases }

   Like :tacn:`auto`, but is not recursive
   and only tries hints with zero cost. Typically used to solve goals
   for which a lemma is already available in the specified :n:`hintbases`.

.. flag:: Info Auto
          Debug Auto
          Info Trivial
          Debug Trivial

   These :term:`flags <flag>` enable printing of informative or debug information for
   the :tacn:`auto` and :tacn:`trivial` tactics.

.. tacn:: eauto {? @nat_or_var } {? @auto_using } {? @hintbases }

   Generalizes :tacn:`auto`. While :tacn:`auto` does not try
   resolution hints which would leave existential variables in the goal,
   :tacn:`eauto` will try them.  Also, :tacn:`eauto` internally uses :tacn:`eassumption`
   instead of :tacn:`assumption` and a tactic similar to :tacn:`simple eapply`
   instead of a tactic similar to :tacn:`simple apply`.
   As a consequence, :tacn:`eauto` can solve goals such as:

   .. example::

      .. rocqtop:: all

         Hint Resolve ex_intro : core.
         Goal forall P:nat -> Prop, P 0 -> exists n, P n.
         eauto.

      `ex_intro` is declared as a hint so the proof succeeds.

   .. seealso:: :ref:`hintdatabases`

   .. tacn:: info_eauto {? @nat_or_var } {? @auto_using } {? @hintbases }

      The various options for :tacn:`info_eauto` are the same as for :tacn:`info_auto`.

   :tacn:`eauto` uses the following flags:

   .. flag:: Info Eauto
             Debug Eauto
      :undocumented:

   .. tacn:: debug eauto {? @nat_or_var } {? @auto_using } {? @hintbases }

      Behaves like :tacn:`eauto` but shows the tactics it tries to solve the goal,
      including failing paths.

.. tacn:: autounfold {? @hintbases } {? @simple_occurrences }

   Unfolds constants that were declared through a :cmd:`Hint Unfold`
   in the given databases.

   :n:`@simple_occurrences`
     Performs the unfolding in the specified occurrences.

.. tacn:: autounfold_one {? @hintbases } {? in @ident }
   :undocumented:

.. tacn:: autorewrite {? * } with {+ @ident } {? @occurrences } {? using @ltac_expr }

   `*`
     If present, rewrite all occurrences whose side conditions are solved.

     .. todo: This may not always work as described, see #4976 #7672 and
        https://github.com/coq/coq/issues/1933#issuecomment-337497938 as
        mentioned here: https://github.com/coq/coq/pull/13343#discussion_r527801604

   :n:`with {+ @ident }`
     Specifies the rewriting rule bases to use.

   :n:`@occurrences`
     Performs rewriting in the specified occurrences.  Note: the `at` clause
     is currently not supported.

     .. exn:: The "at" syntax isn't available yet for the autorewrite tactic.

        Appears when there is an `at` clause on the conclusion.

   :n:`using @ltac_expr`
     :token:`ltac_expr` is applied to the main subgoal after each rewriting step.

   Applies rewritings according to the rewriting rule bases :n:`{+ @ident }`.

   For each rule base, applies each rewriting to the main subgoal until
   it fails. Once all the rules have been processed, if the main subgoal has
   changed then the rules
   of this base are processed again. If the main subgoal has not changed then
   the next base is processed. For the bases, the behavior is very similar to
   the processing of the rewriting rules.

   The rewriting rule bases are built with the :cmd:`Hint Rewrite`
   command.

.. warning::

   This tactic may loop if you build non-terminating rewriting systems.

.. seealso::

   :cmd:`Hint Rewrite` for feeding the database of lemmas used by
   :tacn:`autorewrite` and :tacn:`autorewrite` for examples showing the use of this tactic.
   Also see :ref:`strategies4rewriting`.

Here are two examples of ``autorewrite`` use. The first one ( *Ackermann
function*) shows actually a quite basic use where there is no
conditional rewriting. The second one ( *Mac Carthy function*)
involves conditional rewritings and shows how to deal with them using
the optional tactic of the ``Hint Rewrite`` command.

.. example:: Ackermann function

   .. rocqtop:: in reset

      Parameter Ack : nat -> nat -> nat.

   .. rocqtop:: in

      Axiom Ack0 : forall m:nat, Ack 0 m = S m.
      Axiom Ack1 : forall n:nat, Ack (S n) 0 = Ack n 1.
      Axiom Ack2 : forall n m:nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

   .. rocqtop:: in

      Global Hint Rewrite Ack0 Ack1 Ack2 : base0.

   .. rocqtop:: all

      Lemma ResAck0 : Ack 3 2 = 29.

   .. rocqtop:: all

      autorewrite with base0 using try reflexivity.

.. example:: MacCarthy function

   This example requires the Stdlib library.

   .. rocqtop:: in reset extra-stdlib

      From Stdlib Require Import Arith Lia.

   .. rocqtop:: in extra-stdlib

      Parameter g : nat -> nat -> nat.

   .. rocqtop:: in extra-stdlib

      Axiom g0 : forall m:nat, g 0 m = m.
      Axiom g1 : forall n m:nat, (n > 0) -> (m > 100) -> g n m = g (pred n) (m - 10).
      Axiom g2 : forall n m:nat, (n > 0) -> (m <= 100) -> g n m = g (S n) (m + 11).

   .. rocqtop:: in extra-stdlib

      Global Hint Rewrite g0 g1 g2 using lia : base1.

   .. rocqtop:: in extra-stdlib

      Lemma Resg0 : g 1 110 = 100.

   .. rocqtop:: out extra-stdlib

      Show.

   .. rocqtop:: all extra-stdlib

      autorewrite with base1 using reflexivity || simpl.

   .. rocqtop:: none extra-stdlib

      Qed.

   .. rocqtop:: all extra-stdlib

      Lemma Resg1 : g 1 95 = 91.

   .. rocqtop:: all extra-stdlib

      autorewrite with base1 using reflexivity || simpl.

   .. rocqtop:: none extra-stdlib

      Qed.

.. tacn:: easy

   This tactic tries to solve the current goal by a number of standard closing steps.
   In particular, it tries to close the current goal using the closing tactics
   :tacn:`trivial`, :tacn:`reflexivity`, :tacn:`symmetry`, :tacn:`contradiction`
   and :tacn:`inversion` of hypothesis.
   If this fails, it tries introducing variables and splitting and-hypotheses,
   using the closing tactics afterwards, and splitting the goal using
   :tacn:`split` and recursing.

   This tactic solves goals that belong to many common classes; in particular, many cases of
   unsatisfiable hypotheses, and simple equality goals are usually solved by this tactic.

.. tacn:: now @ltac_expr

   Run :n:`@tactic` followed by :tacn:`easy`. This is a notation for :n:`@tactic; easy`.

.. _hintdatabases:

Hint databases
--------------

Hints used by :tacn:`auto`, :tacn:`eauto` and other tactics are stored in hint
databases.  Each database maps head symbols to a list of hints.  Use the
:cmd:`Print Hint` command to view a database.

Each hint has a cost and an optional pattern. Hints with lower
cost are tried first.  (Cost is not used to limit the scope of searches.)
:tacn:`auto` tries a hint when the conclusion of the current goal matches its
pattern or when the hint has no pattern.

Creating hint databases
```````````````````````

Hint databases can be created with the :cmd:`Create HintDb` command or implicitly
by adding a hint to an unknown database.  We recommend you always use :cmd:`Create HintDb`
and then imediately use :cmd:`Hint Constants` and :cmd:`Hint Variables` to make
those settings explicit.

Note that the default transparency
settings differ between these two methods of creation.  Databases created with
:cmd:`Create HintDb` have the default setting `Transparent` for both `Variables`
and `Constants`, while implicitly created databases have the `Opaque` setting.

.. cmd:: Create HintDb @ident {? discriminated }

   If there is no hint database named :n:`@name`, creates a new hint database
   with that name.  Otherwise, does nothing.  The database is
   implemented by a Discrimination Tree (DT) that serves as a filter to select
   the lemmas that will be applied. When discriminated, the DT uses
   transparency information to decide if a constant should considered rigid for
   filtering, making the retrieval more efficient. By contrast, undiscriminated
   databases treat all constants as transparent, resulting in a larger
   number of selected lemmas to be applied, and thus putting more pressure on
   unification.

   By default, hint databases are undiscriminated.

   .. warn:: @ident already exists and is {? not } discriminated
      :name: mismatched-hint-db

      `Create HintDb` will not change whether a pre-existing database
      is discriminated.


Hint databases defined in the Rocq standard library
```````````````````````````````````````````````````

Several hint databases are defined in the Rocq standard library. The
database contains all hints declared
to belong to it in the currently loaded modules.
In particular, requiring new modules may extend the database.
At Rocq startup, only the core database is nonempty and ready to be used immediately.

:core: This special database is automatically used by ``auto``, except when
       pseudo-database ``nocore`` is given to ``auto``. The core database
       contains only basic lemmas about negation, conjunction, and so on.
       Most of the hints in this database come from the Init and Logic directories.

:arith: all lemmas about Peano’s arithmetic proved in the
        directories Init and Arith.

:zarith: lemmas about binary signed integers from the
         directories theories/ZArith. The database also contains
         high-cost hints that call :tacn:`lia` on equations and
         inequalities in ``nat`` or ``Z``.

:bool: lemmas about booleans, mostly from directory theories/Bool.

:datatypes: lemmas about lists, streams and so on that are mainly proved
            in the Lists subdirectory.

:sets: lemmas about sets and relations from the directories Sets and
       Relations.

:typeclass_instances: special database containing all typeclass instances declared in the
                      environment, including those used for ``setoid_rewrite``,
                      from the Classes directory.

:fset: internal database for the implementation of the ``FSets`` library.

:ordered_type: lemmas about ordered types (as defined in the legacy ``OrderedType`` module),
               mainly used in the ``FSets`` and ``FMaps`` libraries.

You are advised not to put your own hints in the core database, but
use one or more databases specific to your development.

.. _creating_hints:

Creating Hints
--------------

   The various `Hint` commands share these elements:

   :n:`{? : {+ @ident } }` specifies the hint database(s) to add to.
   *(Deprecated since version 8.10:* If no :token:`ident`\s
   are given, the hint is added to the `core` database.)

   Hints in hint databases are ordered, which is the order in which they're
   tried, as shown by the :cmd:`Print HintDb` command.
   Hints with lower costs are tried first.  Hints with the same cost are tried
   in reverse of their order of definition, i.e., last to first.

   Outside of sections, these commands support the :attr:`local`, :attr:`export`
   and :attr:`global` attributes. :attr:`export` is the default.

   Inside sections, some commands only support the :attr:`local` attribute. These are
   :cmd:`Hint Immediate`, :cmd:`Hint Resolve`, :cmd:`Hint Constructors`,
   :cmd:`Hint Unfold`, :cmd:`Hint Extern` and :cmd:`Hint Rewrite`.
   :attr:`local` is the default for all hint commands inside sections.

   + :attr:`local` hints are never visible from other modules, even if they
     :cmd:`Import` or :cmd:`Require` the current module.

   + :attr:`export` hints are visible from other modules when they :cmd:`Import` the current
     module, but not when they only :cmd:`Require` it.

   + :attr:`global` hints are visible from other modules when they :cmd:`Import` or
     :cmd:`Require` the current module.

   .. versionchanged:: 8.18

      The default value for hint locality outside sections is
      now :attr:`export`. It used to be :attr:`global`.

   The `Hint` commands are:

   .. cmd:: Hint Resolve {+ {| @qualid | @one_term } } {? @hint_info } {? : {+ @ident } }
            Hint Resolve {| -> | <- } {+ @qualid } {? @natural } {? : {+ @ident } }
      :name: Hint Resolve; _

      .. insertprodn hint_info one_pattern

      .. prodn::
         hint_info ::= %| {? @natural } {? @one_pattern }
         one_pattern ::= @one_term

      The first form adds each :n:`@qualid` as a hint with the head symbol of the type of
      :n:`@qualid` to the specified hint databases (:n:`@ident`\s). The cost of the hint is the number of
      subgoals generated by :tacn:`simple apply` :n:`@qualid` or, if specified, :n:`@natural`. The
      associated pattern is inferred from the conclusion of the type of
      :n:`@qualid` or, if specified, the given :n:`@one_pattern`.

      If the inferred type
      of :n:`@qualid` does not start with a product, :tacn:`exact` :n:`@qualid` is added
      to the hint list.  If the type can be reduced to a type starting with a product,
      :tacn:`simple apply` :n:`@qualid` is also added to the hints list.

      If the inferred type of :n:`@qualid` contains a dependent
      quantification on a variable which occurs only in the premises of the type
      and not in its conclusion, no instance could be inferred for the variable by
      unification with the goal. In this case, the hint is only used by
      :tacn:`eauto` / :tacn:`typeclasses eauto`, but not by :tacn:`auto`.  A
      typical hint that would only be used by :tacn:`eauto` is a transitivity
      lemma.

      :n:`{| -> | <- }`
        The second form adds the left-to-right (`->`) or right-ot-left implication (`<-`)
        of an equivalence as a hint (informally
        the hint will be used as, respectively, :tacn:`apply` :n:`-> @qualid` or
        :tacn:`apply` :n:`<- @qualid`,
        although as mentioned before, the tactic actually used is a restricted version of
        :tacn:`apply`).

      :n:`@one_term`
        Permits declaring a hint without declaring a new
        constant first. This is deprecated.

         .. warn:: Declaring arbitrary terms as hints is fragile and deprecated; it is recommended to declare a toplevel constant instead
            :undocumented:

      .. exn:: @qualid cannot be used as a hint

         The head symbol of the type of :n:`@qualid` is a bound variable
         such that this tactic cannot be associated with a constant.

   .. cmd:: Hint Immediate {+ {| @qualid | @one_term } } {? : {+ @ident } }

      For each specified :n:`@qualid`, adds the tactic :tacn:`simple apply` :n:`@qualid;`
      :tacn:`solve` :n:`[` :tacn:`trivial` :n:`]` to the hint list
      associated with the head symbol of the type of :n:`@qualid`. This
      tactic will fail if all the subgoals generated by :tacn:`simple apply` :n:`@qualid` are
      not solved immediately by the :tacn:`trivial` tactic (which only tries tactics
      with cost 0). This command is useful for theorems such as the symmetry of
      equality or :g:`n+1=m+1 -> n=m` that we may want to introduce with limited
      use in order to avoid useless proof search. The cost of this tactic (which
      never generates subgoals) is always 1, so that it is not used by :tacn:`trivial`
      itself.

   .. cmd:: Hint Constructors {+ @qualid } {? : {+ @ident } }

      For each :n:`@qualid` that is an inductive type, adds all its constructors as
      hints of type ``Resolve``. Then, when the conclusion of current goal has the form
      :n:`(@qualid ...)`, :tacn:`auto` will try to apply each constructor.

      .. exn:: @qualid is not an inductive type
         :undocumented:

   .. cmd:: Hint Unfold {+ @qualid } {? : {+ @ident } }

      For each :n:`@qualid`, adds the tactic :tacn:`unfold` :n:`@qualid` to the
      hint list that will only be used when the :term:`head constant` of the goal is :token:`qualid`.
      Its cost is 4.

   .. cmd:: Hint {| Transparent | Opaque } {+ @qualid } {? : {+ @ident } }
      :name: Hint Transparent; Hint Opaque

      Adds transparency hints to the database, making each :n:`@qualid`
      a transparent or opaque constant during resolution. This information is used
      during unification of the goal with any lemma in the database and inside the
      discrimination network to relax or constrain it in the case of discriminated
      databases.

      .. exn:: Cannot coerce @qualid to an evaluable reference.
         :undocumented:

   .. cmd:: Hint {| Constants | Projections | Variables } {| Transparent | Opaque } {? : {+ @ident } }
      :name: Hint Constants; Hint Projections; Hint Variables

      Sets the transparency flag for constants, projections or variables for the specified hint
      databases.
      These flags affect the unification of hints in the database.
      We advise using this just after a :cmd:`Create HintDb` command.

   .. cmd:: Hint Extern @natural {? @one_pattern } => @ltac_expr {? : {+ @ident } }

      Extends :tacn:`auto` with tactics other than :tacn:`apply` and
      :tacn:`unfold`. :n:`@natural` is the cost, :n:`@one_pattern` is the pattern
      to match and :n:`@ltac_expr` is the action to apply.

      **Usage tip**: tactics that can succeed even if they don't change the context,
      such as most of the :ref:`conversion tactics <applyingconversionrules>`, should
      be prefaced with :tacn:`progress` to avoid needless repetition of the tactic.

      **Usage tip**: Use a :cmd:`Hint Extern` with no pattern to do
      pattern matching on hypotheses using ``match goal with``
      inside the tactic.

      .. example::

         .. rocqtop:: in

            Hint Extern 4 (~(_ = _)) => discriminate : core.

         Now, when the head of the goal is a disequality, ``auto`` will try
         discriminate if it does not manage to solve the goal with hints with a
         cost less than 4.

      One can even use some sub-patterns of the pattern in
      the tactic script. A sub-pattern is a question mark followed by an
      identifier, like ``?X1`` or ``?X2``. Here is an example:

      .. example::

         .. rocqtop:: reset all

            Require Import ListDef.
            Hint Extern 5 ({?X1 = ?X2} + {?X1 <> ?X2}) =>
              generalize  X1, X2; decide equality : eqdec.
            Goal forall a b:list (nat * nat), {a = b} + {a <> b}.
            info_auto.

   .. cmd:: Hint Cut [ @hints_regexp ] {? : {+ @ident } }

      .. DISABLED insertprodn hints_regexp hints_regexp

      .. prodn::
         hints_regexp ::= {+ @qualid }   (hint or instance identifier)
         | _   (any hint)
         | @hints_regexp | @hints_regexp   (disjunction)
         | @hints_regexp @hints_regexp   (sequence)
         | @hints_regexp *   (Kleene star)
         | emp   (empty)
         | eps   (epsilon)
         | ( @hints_regexp )

      Used to cut the proof search tree according to a regular
      expression that matches the paths to be cut.


      During proof search, the path of
      successive successful hints on a search branch is recorded as a
      list of identifiers for the hints (note that :cmd:`Hint Extern`\s do not have
      an associated identifier).
      For each hint :n:`@qualid` in the hint database, the current path `p`
      extended with :n:`@qualid`
      is matched against the current cut expression `c` associated with the
      hint database.  If the match succeeds the hint is *not* applied.

      :n:`Hint Cut @hints_regexp` sets the cut expression
      to :n:`c | @hints_regexp`.  The initial cut expression is `emp`.

      The output of :cmd:`Print HintDb` shows the cut expression.

      .. warning::

         The regexp matches the entire path. Most hints will start with a
         leading `( _* )` to match the tail of the path. (Note that `(_*)`
         misparses since `*)` would end a comment.)

      .. warning::

         There is no operator precedence during parsing, one can
         check with :cmd:`Print HintDb` to verify the current cut expression.

      .. warning::

         These hints currently only apply to typeclass proof search and the
         :tacn:`typeclasses eauto` tactic.

   .. cmd:: Hint Mode @qualid {+ {| + | ! | - } } {? : {+ @ident } }

      Sets an optional mode of resolution for the identifier :n:`@qualid`. When
      proof search has a goal that ends in an application of :n:`@qualid` to
      arguments :n:`@arg ... @arg`, the mode tells if the hints associated with
      :n:`@qualid` can be applied or not, depending on a criterion on the arguments.
      A mode specification is a list of ``+``, ``!`` or ``-`` items that specify if
      an argument of the identifier is to be treated as an input (``+``), if its
      head only is an input (``!``) or an output (``-``) of the identifier.
      Mode ``-`` matches any term, mode ``+`` matches a
      term if and only if it does not contain existential variables, while mode ``!``
      matches a term if and only if the *head* of the term is not an existential variable.
      The head of a term is understood here as the applicative head, recursively,
      ignoring casts. For a mode declaration to match a list of arguments, each argument should
      match its corresponding mode.

      :cmd:`Hint Mode` is especially useful for typeclasses, when one does not want
      to support default instances and wants to avoid ambiguity in general. Setting a parameter
      of a class as an input forces proof search to be driven by that index of the class,
      with ``!`` allowing existentials to appear in the index but not at its head.

   .. note::

      + Multiple modes can be declared for a single identifier.  In that
        case only one mode needs to match the arguments for the hints to be applied.

      + If you want to add hints such as :cmd:`Hint Transparent`,
        :cmd:`Hint Cut`, or :cmd:`Hint Mode`, for typeclass
        resolution, do not forget to put them in the
        ``typeclass_instances`` hint database.

   .. warn:: This hint is not local but depends on a section variable. It will disappear when the section is closed.

      A hint with a non-local attribute was added inside a section, but it
      refers to a local variable that will go out of scope when closing the
      section. As a result the hint will not survive either.

   .. example:: Logic programming with addition on natural numbers

      This example illustrates the use of modes to control how resolutions
      can be triggered during proof search.

      .. rocqtop:: all reset

         Parameter plus : nat -> nat -> nat -> Prop.
         Hint Mode plus ! - - : plus.
         Hint Mode plus - ! - : plus.

      .. rocqtop:: in

         Axiom plus0l : forall m : nat, plus 0 m m.
         Axiom plus0r : forall n : nat, plus n 0 n.
         Axiom plusSl : forall n m r : nat, plus n m r -> plus (S n) m (S r).
         Axiom plusSr : forall n m r : nat, plus n m r -> plus m (S m) (S r).
         Hint Resolve plus0l plus0r plusSl plusSr : plus.

      The previous commands define the addition predicate and set its mode so it
      can resolve goals if and only if one of the first two arguments is headed
      by a constructor or constant. The last argument of the predicate will be
      the inferred result.

      .. rocqtop:: all

         Goal exists x y, plus x y 12.
         Proof. eexists ?[x], ?[y].
            Fail typeclasses eauto with plus.
            instantiate (y := 1).
            typeclasses eauto with plus.
         Defined.

      In the proof script, the first call to :tacn:`typeclasses eauto` fails as the two
      arguments are headed by an existential variable, while when we instantiate the second
      argument with ``1``, typeclass resolution succeeds as the second declared mode is matched,
      and instantiates ``x`` with ``11``.

.. cmd:: Hint Rewrite {? {| -> | <- } } {+ @one_term } {? using @ltac_expr } {? : {+ @ident } }

   :n:`{? using @ltac_expr }`
     If specified, :n:`@ltac_expr` is applied to the generated subgoals, except for the
     main subgoal.

   :n:`{| -> | <- }`
     Arrows specify the orientation; left to right (:n:`->`) or right to left (:n:`<-`).
     If no arrow is given, the default orientation is left to right (:n:`->`).

   Adds the terms :n:`{+ @one_term }` (their types must be
   equalities) to the rewriting bases :n:`{*  @ident }`.
   Note that the rewriting bases are distinct from the :tacn:`auto`
   hint bases and that :tacn:`auto` does not take them into account.

   .. cmd:: Print Rewrite HintDb @ident

      This command displays all rewrite hints contained in :n:`@ident`.

.. cmd:: Remove Hints {+ @qualid } {? : {+ @ident } }

   Removes the hints associated with the :n:`{+ @qualid }` in databases
   :n:`{+ @ident}`.  Note: hints created with :cmd:`Hint Extern` currently
   can't be removed.  The best workaround for this is to make the hints
   non-global and carefully select which modules you import.

.. cmd:: Print Hint {? {| * | @reference } }

   :n:`*`
     Display all declared hints.

   :n:`@reference`
     Display all hints associated with the head symbol :n:`@reference`.

   Displays tactics from the hints list.  The default is to show hints that
   apply to the conclusion of the current goal.  The other forms with :n:`*`
   and :n:`@reference` can be used even if no proof is open.

   Each hint has a cost that is a nonnegative
   integer and an optional pattern. The hints with lower cost are tried first.

.. cmd:: Print HintDb @ident

   This command displays all hints from database :n:`@ident`.  Hints
   in each group ("For ... ->") are shown in the order in which they will be tried
   (first to last).  The groups are shown ordered alphabetically on the last component of
   the symbol name.  Note that hints with the same cost are tried in
   reverse of the order they're defined in, i.e., last to first.

Hint locality
`````````````

As explained at the beginning of :ref:`creating_hints`, hints outside sections have three
possible localities: :attr:`local`, :attr:`export`, and :attr:`global`,
with :attr:`export` now being the default. The default used to
be :attr:`global`, so old code bases may still use it. The following
option may be useful to help transition hints from the :attr:`global`
to the :attr:`export` locality, as it can provide an over-approximation
of where these hints are used:

.. opt:: Loose Hint Behavior {| "Lax" | "Warn" | "Strict" }

   This :term:`option` accepts three values:

   - "Lax": no scope errors or warnings are generated for hints. This is the default.

   - "Warn": outputs a warning when a non-imported hint is used. Note that this
     is an over-approximation, because a hint may be triggered by a run that
     will eventually fail and backtrack, resulting in the hint not being
     actually useful for the proof.

   - "Strict": fails when a non-imported hint is used, with the same caveats
     as "Warn".

.. _tactics-implicit-automation:

Setting implicit automation tactics
-----------------------------------

.. cmd:: Proof with @ltac_expr {? using @section_var_expr }

   Starts a proof in which :token:`ltac_expr` is applied to the active goals
   after each tactic that ends with `...` instead of the usual single period.
   ":n:`@tactic...`" is equivalent to ":n:`@tactic; @ltac_expr.`".

   .. seealso:: :cmd:`Proof` in :ref:`proof-editing-mode`.
