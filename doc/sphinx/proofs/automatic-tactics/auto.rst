.. _automation:

=========================
Programmable proof search
=========================

.. tacn:: auto
   :name: auto

   This tactic implements a Prolog-like resolution procedure to solve the
   current goal. It first tries to solve the goal using the :tacn:`assumption`
   tactic, then it reduces the goal to an atomic one using :tacn:`intros` and
   introduces the newly generated hypotheses as hints. Then it looks at
   the list of tactics associated to the head symbol of the goal and
   tries to apply one of them (starting from the tactics with lower
   cost). This process is recursively applied to the generated subgoals.

   By default, :tacn:`auto` only uses the hypotheses of the current goal and
   the hints of the database named ``core``.

   .. warning::

      :tacn:`auto` uses a weaker version of :tacn:`apply` that is closer to
      :tacn:`simple apply` so it is expected that sometimes :tacn:`auto` will
      fail even if applying manually one of the hints would succeed.

   .. tacv:: auto @natural

      Forces the search depth to be :token:`natural`. The maximal search depth
      is 5 by default.

   .. tacv:: auto with {+ @ident}

      Uses the hint databases :n:`{+ @ident}` in addition to the database ``core``.

      .. note::

         Use the fake database `nocore` if you want to *not* use the `core`
         database.

   .. tacv:: auto with *

      Uses all existing hint databases. Using this variant is highly discouraged
      in finished scripts since it is both slower and less robust than the variant
      where the required databases are explicitly listed.

   .. seealso::
      :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>` for the list of
      pre-defined databases and the way to create or extend a database.

   .. tacv:: auto using {+ @qualid__i} {? with {+ @ident } }

      Uses lemmas :n:`@qualid__i` in addition to hints. If :n:`@qualid` is an
      inductive type, it is the collection of its constructors which are added
      as hints.

      .. note::

         The hints passed through the `using` clause are used in the same
         way as if they were passed through a hint database. Consequently,
         they use a weaker version of :tacn:`apply` and :n:`auto using @qualid`
         may fail where :n:`apply @qualid` succeeds.

         Given that this can be seen as counter-intuitive, it could be useful
         to have an option to use full-blown :tacn:`apply` for lemmas passed
         through the `using` clause. Contributions welcome!

   .. tacv:: info_auto

      Behaves like :tacn:`auto` but shows the tactics it uses to solve the goal. This
      variant is very useful for getting a better understanding of automation, or
      to know what lemmas/assumptions were used.

   .. tacv:: debug auto
      :name: debug auto

      Behaves like :tacn:`auto` but shows the tactics it tries to solve the goal,
      including failing paths.

   .. tacv:: {? info_}auto {? @natural} {? using {+ @qualid}} {? with {+ @ident}}

      This is the most general form, combining the various options.

.. tacv:: trivial
   :name: trivial

   This tactic is a restriction of :tacn:`auto` that is not recursive
   and tries only hints that cost `0`. Typically it solves trivial
   equalities like :g:`X=X`.

   .. tacv:: trivial with {+ @ident}
             trivial with *
             trivial using {+ @qualid}
             debug trivial
             info_trivial
             {? info_}trivial {? using {+ @qualid}} {? with {+ @ident}}
      :name: _; _; _; debug trivial; info_trivial; _
      :undocumented:

.. note::
  :tacn:`auto` and :tacn:`trivial` either solve completely the goal or
  else succeed without changing the goal. Use :g:`solve [ auto ]` and
  :g:`solve [ trivial ]` if you would prefer these tactics to fail when
  they do not manage to solve the goal.

.. flag:: Info Auto
          Debug Auto
          Info Trivial
          Debug Trivial

   These flags enable printing of informative or debug information for
   the :tacn:`auto` and :tacn:`trivial` tactics.

.. tacn:: eauto
   :name: eauto

   This tactic generalizes :tacn:`auto`. While :tacn:`auto` does not try
   resolution hints which would leave existential variables in the goal,
   :tacn:`eauto` does try them (informally speaking, it internally uses a tactic
   close to :tacn:`simple eapply` instead of a tactic close to :tacn:`simple apply`
   in the case of :tacn:`auto`). As a consequence, :tacn:`eauto`
   can solve such a goal:

   .. example::

      .. coqtop:: all

         Hint Resolve ex_intro : core.
         Goal forall P:nat -> Prop, P 0 -> exists n, P n.
         eauto.

      Note that ``ex_intro`` should be declared as a hint.


   .. tacv:: {? info_}eauto {? @natural} {? using {+ @qualid}} {? with {+ @ident}}

      The various options for :tacn:`eauto` are the same as for :tacn:`auto`.

   :tacn:`eauto` also obeys the following flags:

   .. flag:: Info Eauto
             Debug Eauto
      :undocumented:

   .. seealso:: :ref:`The Hints Databases for auto and eauto <thehintsdatabasesforautoandeauto>`


.. tacn:: autounfold with {+ @ident}
   :name: autounfold

   This tactic unfolds constants that were declared through a :cmd:`Hint Unfold`
   in the given databases.

.. tacv:: autounfold with {+ @ident} in @goal_occurrences

   Performs the unfolding in the given clause (:token:`goal_occurrences`).

.. tacv:: autounfold with *

   Uses the unfold hints declared in all the hint databases.

.. tacn:: autorewrite with {+ @ident}
   :name: autorewrite

   This tactic carries out rewritings according to the rewriting rule
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

.. tacv:: autorewrite with {+ @ident} in @goal_occurrences

  Performs all the rewriting in the clause :n:`@goal_occurrences`.

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

.. cmd:: Hint @hint_definition : {+ @ident}

   The general command to add a hint to some databases :n:`{+ @ident}`.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export`
   locality attributes. When no locality is explictly given, the
   command is :attr:`local` inside a section and :attr:`global` otherwise.

   + :attr:`local` hints are never visible from other modules, even if they
     require or import the current module. Inside a section, the :attr:`local`
     attribute is useless since hints do not survive anyway to the closure of
     sections.

   + :attr:`export` are visible from other modules when they import the current
     module. Requiring it is not enough. This attribute is only effective for
     the :cmd:`Hint Resolve`, :cmd:`Hint Immediate`, :cmd:`Hint Unfold` and
     :cmd:`Hint Extern` variants of the command.

   + :attr:`global` hints are made available by merely requiring the current
     module.

   The various possible :production:`hint_definition`\s are given below.

   .. cmdv:: Hint @hint_definition

      No database name is given: the hint is registered in the ``core`` database.

      .. deprecated:: 8.10

   .. cmdv:: Hint Resolve @qualid {? | {? @natural} {? @pattern}} : @ident
      :name: Hint Resolve

      This command adds :n:`simple apply @qualid` to the hint list with the head
      symbol of the type of :n:`@qualid`. The cost of that hint is the number of
      subgoals generated by :n:`simple apply @qualid` or :n:`@natural` if specified. The
      associated :n:`@pattern` is inferred from the conclusion of the type of
      :n:`@qualid` or the given :n:`@pattern` if specified. In case the inferred type
      of :n:`@qualid` does not start with a product the tactic added in the hint list
      is :n:`exact @qualid`. In case this type can however be reduced to a type
      starting with a product, the tactic :n:`simple apply @qualid` is also stored in
      the hints list. If the inferred type of :n:`@qualid` contains a dependent
      quantification on a variable which occurs only in the premisses of the type
      and not in its conclusion, no instance could be inferred for the variable by
      unification with the goal. In this case, the hint is added to the hint list
      of :tacn:`eauto` instead of the hint list of auto and a warning is printed. A
      typical example of a hint that is used only by :tacn:`eauto` is a transitivity
      lemma.

      .. exn:: @qualid cannot be used as a hint

         The head symbol of the type of :n:`@qualid` is a bound variable
         such that this tactic cannot be associated to a constant.

   .. cmdv:: Hint Resolve {+ @qualid} : @ident

      Adds each :n:`Hint Resolve @qualid`.

   .. cmdv:: Hint Resolve -> @qualid : @ident

      Adds the left-to-right implication of an equivalence as a hint (informally
      the hint will be used as :n:`apply <- @qualid`, although as mentioned
      before, the tactic actually used is a restricted version of
      :tacn:`apply`).

   .. cmdv:: Hint Resolve <- @qualid

      Adds the right-to-left implication of an equivalence  as a hint.

   .. cmdv:: Hint Immediate @qualid : @ident
      :name: Hint Immediate

      This command adds :n:`simple apply @qualid; trivial` to the hint list associated
      with the head symbol of the type of :n:`@ident` in the given database. This
      tactic will fail if all the subgoals generated by :n:`simple apply @qualid` are
      not solved immediately by the :tacn:`trivial` tactic (which only tries tactics
      with cost 0).This command is useful for theorems such as the symmetry of
      equality or :g:`n+1=m+1 -> n=m` that we may like to introduce with a limited
      use in order to avoid useless proof-search. The cost of this tactic (which
      never generates subgoals) is always 1, so that it is not used by :tacn:`trivial`
      itself.

   .. exn:: @qualid cannot be used as a hint
      :undocumented:

   .. cmdv:: Hint Immediate {+ @qualid} : @ident

      Adds each :n:`Hint Immediate @qualid`.

   .. cmdv:: Hint Constructors @qualid : @ident
      :name: Hint Constructors

      If :token:`qualid` is an inductive type, this command adds all its constructors as
      hints of type ``Resolve``. Then, when the conclusion of current goal has the form
      :n:`(@qualid ...)`, :tacn:`auto` will try to apply each constructor.

      .. exn:: @qualid is not an inductive type
         :undocumented:

   .. cmdv:: Hint Constructors {+ @qualid} : @ident

      Extends the previous command for several inductive types.

   .. cmdv:: Hint Unfold @qualid : @ident
      :name: Hint Unfold

      This adds the tactic :n:`unfold @qualid` to the hint list that will only be
      used when the head constant of the goal is :token:`qualid`.
      Its cost is 4.

   .. cmdv:: Hint Unfold {+ @qualid}

      Extends the previous command for several defined constants.

   .. cmdv:: Hint Transparent {+ @qualid} : @ident
             Hint Opaque {+ @qualid} : @ident
      :name: Hint Transparent; Hint Opaque

      This adds transparency hints to the database, making :n:`@qualid`
      transparent or opaque constants during resolution. This information is used
      during unification of the goal with any lemma in the database and inside the
      discrimination network to relax or constrain it in the case of discriminated
      databases.

   .. cmdv:: Hint Variables {| Transparent | Opaque } : @ident
             Hint Constants {| Transparent | Opaque } : @ident
      :name: Hint Variables; Hint Constants

      This sets the transparency flag used during unification of
      hints in the database for all constants or all variables,
      overwriting the existing settings of opacity. It is advised
      to use this just after a :cmd:`Create HintDb` command.

   .. cmdv:: Hint Extern @natural {? @pattern} => @tactic : @ident
      :name: Hint Extern

      This hint type is to extend :tacn:`auto` with tactics other than :tacn:`apply` and
      :tacn:`unfold`. For that, we must specify a cost, an optional :n:`@pattern` and a
      :n:`@tactic` to execute.

      .. example::

         .. coqtop:: in

            Hint Extern 4 (~(_ = _)) => discriminate : core.

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

   .. cmdv:: Hint Cut @regexp : @ident
      :name: Hint Cut

      .. warning::

         These hints currently only apply to typeclass proof search and the
         :tacn:`typeclasses eauto` tactic.

      This command can be used to cut the proof-search tree according to a regular
      expression matching paths to be cut. The grammar for regular expressions is
      the following. Beware, there is no operator precedence during parsing, one can
      check with :cmd:`Print HintDb` to verify the current cut expression:

      .. prodn::
         regexp ::= @ident   (hint or instance identifier)
         | _   (any hint)
         | @regexp | @regexp   (disjunction)
         | @regexp @regexp   (sequence)
         | @regexp *   (Kleene star)
         | emp   (empty)
         | eps   (epsilon)
         | ( @regexp )

      The `emp` regexp does not match any search path while `eps`
      matches the empty path. During proof search, the path of
      successive successful hints on a search branch is recorded, as a
      list of identifiers for the hints (note that :cmd:`Hint Extern`\’s do not have
      an associated identifier).
      Before applying any hint :n:`@ident` the current path `p` extended with
      :n:`@ident` is matched against the current cut expression `c` associated to
      the hint database. If matching succeeds, the hint is *not* applied. The
      semantics of :n:`Hint Cut @regexp` is to set the cut expression
      to :n:`c | regexp`, the initial cut expression being `emp`.

   .. cmdv:: Hint Mode @qualid {* {| + | ! | - } } : @ident
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
      needs to match the arguments for the hints to be applied. The head of a term
      is understood here as the applicative head, or the match or projection
      scrutinee’s head, recursively, casts being ignored. :cmd:`Hint Mode` is
      especially useful for typeclasses, when one does not want to support default
      instances and avoid ambiguity in general. Setting a parameter of a class as an
      input forces proof-search to be driven by that index of the class, with ``!``
      giving more flexibility by allowing existentials to still appear deeper in the
      index but not at its head.

   .. note::

      + One can use a :cmd:`Hint Extern` with no pattern to do
        pattern matching on hypotheses using ``match goal with``
        inside the tactic.

      + If you want to add hints such as :cmd:`Hint Transparent`,
        :cmd:`Hint Cut`, or :cmd:`Hint Mode`, for typeclass
        resolution, do not forget to put them in the
        ``typeclass_instances`` hint database.


Hint databases defined in the |Coq| standard library
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Several hint databases are defined in the |Coq| standard library. The
actual content of a database is the collection of hints declared
to belong to this database in each of the various modules currently
loaded. Especially, requiring new modules may extend the database.
At |Coq| startup, only the core database is nonempty and can be used.

:core: This special database is automatically used by ``auto``, except when
       pseudo-database ``nocore`` is given to ``auto``. The core database
       contains only basic lemmas about negation, conjunction, and so on.
       Most of the hints in this database come from the Init and Logic directories.

:arith: This database contains all lemmas about Peano’s arithmetic proved in the
        directories Init and Arith.

:zarith: contains lemmas about binary signed integers from the
         directories theories/ZArith. The database also contains
         high-cost hints that call :tacn:`lia` on equations and
         inequalities in ``nat`` or ``Z``.

:bool: contains lemmas about booleans, mostly from directory theories/Bool.

:datatypes: is for lemmas about lists, streams and so on that are mainly proved
            in the Lists subdirectory.

:sets: contains lemmas about sets and relations from the directories Sets and
       Relations.

:typeclass_instances: contains all the typeclass instances declared in the
                      environment, including those used for ``setoid_rewrite``,
                      from the Classes directory.

:fset: internal database for the implementation of the ``FSets`` library.

:ordered_type: lemmas about ordered types (as defined in the legacy ``OrderedType`` module),
               mainly used in the ``FSets`` and ``FMaps`` libraries.

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
   (left to right). Notice that the rewriting bases are distinct from the :tacn:`auto`
   hint bases and that :tacn:`auto` does not take them into account.

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

.. cmd:: Hint Rewrite {? {| -> | <- } } {+ @one_term } {? using @ltac_expr } {? : {* @ident } }

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
module ``A`` is required (using e.g. ``Require A.``).

As of today, hints only have a binary behavior regarding locality, as
described above: either they disappear at the end of a section scope,
or they remain global forever. This causes a scalability issue,
because hints coming from an unrelated part of the code may badly
influence another development. It can be mitigated to some extent
thanks to the :cmd:`Remove Hints` command,
but this is a mere workaround and has some limitations (for instance, external
hints cannot be removed).

A proper way to fix this issue is to bind the hints to their module scope, as
for most of the other objects |Coq| uses. Hints should only be made available when
the module they are defined in is imported, not just required. It is very
difficult to change the historical behavior, as it would break a lot of scripts.
We propose a smooth transitional path by providing the :opt:`Loose Hint Behavior`
option which accepts three flags allowing for a fine-grained handling of
non-imported hints.

.. opt:: Loose Hint Behavior {| "Lax" | "Warn" | "Strict" }
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


   .. cmdv:: Proof with @tactic using {+ @ident}

      Combines in a single line ``Proof with`` and ``Proof using``, see :ref:`proof-editing-mode`

   .. cmdv:: Proof using {+ @ident} with @tactic

      Combines in a single line ``Proof with`` and ``Proof using``, see :ref:`proof-editing-mode`
