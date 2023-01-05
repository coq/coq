.. _typeclasses:

Typeclasses
===========

Typeclasses are types whose values Coq can automatically infer by using user
declared instances. It allows for a form of programmatic proof or term search.

This chapter presents a quick reference of the commands related to typeclasses.
Additional helpful information can be found in the paper introducing typeclasses
to Coq :cite:`sozeau08` and the literature on type classes in Haskell.


Typeclass and instance declarations
-----------------------------------

The syntax for typeclasses and instance declarations is the same as the record
syntax of Coq:

.. coqdoc::

  Class classname (p1 : t1) ⋯ (pn : tn) [: sort] := { f1 : u1 ; ⋯ ; fm : um }.

  Instance instancename q1 ⋯ qm : classname p1 ⋯ pn := { f1 := t1 ; ⋯ ; fm := tm }.

The ``pi : ti`` variables are called the *parameters* of the typeclass and
the ``fi : ti`` are called the *methods*. Each typeclass definition gives
rise to a corresponding record declaration and each instance is a
regular definition whose name is given by `instancename` and type is an
instantiation of the record type.

We’ll use the following example typeclass in the rest of the chapter:

.. coqtop:: none

   Set Warnings "-deprecated-instance-without-locality".

.. coqtop:: in

   Class EqDec (A : Type) :=
     { eqb : A -> A -> bool ;
       eqb_leibniz : forall x y, eqb x y = true -> x = y }.

This typeclass implements a boolean equality test which is compatible with
Leibniz equality on some type. An example implementation is:

.. coqtop:: in

   Instance unit_EqDec : EqDec unit :=
     { eqb x y := true ;
       eqb_leibniz x y H :=
         match x, y return x = y with
         | tt, tt => eq_refl tt
         end }.

Using the :attr:`refine` attribute, if the term is not sufficient to
finish the definition (e.g. due to a missing field or non-inferable
hole) it must be finished in proof mode. If it is sufficient a trivial
proof mode with no open goals is started.

.. coqtop:: in

   #[refine] Instance unit_EqDec' : EqDec unit := { eqb x y := true }.
   Proof. intros [] [];reflexivity. Defined.

Note that if you finish the proof with :cmd:`Qed` the entire instance
will be opaque, including the fields given in the initial term.

Alternatively, in :flag:`Program Mode` if one does not give all the
members in the Instance declaration, Coq generates obligations for the
remaining fields, e.g.:

.. coqtop:: in

   Require Import Program.Tactics.
   Program Instance eq_bool : EqDec bool :=
     { eqb x y := if x then y else negb y }.

.. coqtop:: all

   Next Obligation.
     destruct x ; destruct y ; (discriminate || reflexivity).
   Defined.

One has to take care that the transparency of every field is
determined by the transparency of the :cmd:`Instance` proof. One can
use alternatively the :attr:`program` attribute to get richer
facilities for dealing with obligations.


Binding typeclasses
-------------------

Once a typeclass is declared, one can use it in typeclass binders:

.. coqtop:: all

   Definition neqb {A} {eqa : EqDec A} (x y : A) := negb (eqb x y).

When one calls a typeclass method, a constraint is generated that is
satisfied only in contexts where the appropriate instances can be
found. In the example above, a constraint ``EqDec A`` is generated and
satisfied by ``eqa : EqDec A``. In case no satisfying constraint can be
found, an error is raised:

.. coqtop:: all

   Fail Definition neqb' (A : Type) (x y : A) := negb (eqb x y).

The algorithm used to solve constraints is a variant of the :tacn:`eauto`
tactic that does proof search with a set of lemmas (the instances). It
will use local hypotheses as well as declared lemmas in
the ``typeclass_instances`` database. Hence the example can also be
written:

.. coqtop:: all

   Definition neqb' A (eqa : EqDec A) (x y : A) := negb (eqb x y).

However, the generalizing binders should be used instead as they have
particular support for typeclasses:

+ They automatically set the maximally implicit status for typeclass
  arguments, making derived functions as easy to use as typeclass methods.
  In the example above, ``A`` and ``eqa`` should be set maximally implicit.
+ They support implicit quantification on partially applied typeclasses
  (:ref:`implicit-generalization`). Any argument not given as part of a typeclass
  binder will be automatically generalized.
+ They also support implicit quantification on :ref:`superclasses`.


Following the previous example, one can write:

.. coqtop:: all

   Generalizable Variables A B C.

   Definition neqb_implicit `{eqa : EqDec A} (x y : A) := negb (eqb x y).

Here ``A`` is implicitly generalized, and the resulting function is
equivalent to the one above.

Parameterized instances
-----------------------

One can declare parameterized instances as in Haskell simply by giving
the constraints as a binding context before the instance, e.g.:

.. coqtop:: in

   Program Instance prod_eqb `(EA : EqDec A, EB : EqDec B) : EqDec (A * B) :=
     { eqb x y := match x, y with
                  | (la, ra), (lb, rb) => andb (eqb la lb) (eqb ra rb)
                  end }.

.. coqtop:: none

   Admit Obligations.

These instances are used just as well as lemmas in the instance hint
database.

.. _contexts:

Sections and contexts
---------------------

To ease developments parameterized by many instances, one can use the
:cmd:`Context` command to introduce the parameters into the :term:`local context`,
which works similarly to the command :cmd:`Variable`, except it accepts any
binding context as an argument, so variables can be implicit, and
:ref:`implicit-generalization` can be used.
For example:

.. coqtop:: all

   Section EqDec_defs.

   Context `{EA : EqDec A}.

.. coqtop:: in

   #[ global, program ] Instance option_eqb : EqDec (option A) :=
     { eqb x y := match x, y with
            | Some x, Some y => eqb x y
            | None, None => true
            | _, _ => false
            end }.
   Admit Obligations.

.. coqtop:: all

   End EqDec_defs.

   About option_eqb.

Here the :attr:`global` attribute redeclares the instance at the end of the
section, once it has been generalized by the context variables it
uses.

.. seealso:: Section :ref:`section-mechanism`

Building hierarchies
--------------------

.. _superclasses:

Superclasses
~~~~~~~~~~~~

One can also parameterize typeclasses by other typeclasses, generating a
hierarchy of typeclasses and superclasses. In the same way, we give the
superclasses as a binding context:

.. coqtop:: all

   Class Ord `(E : EqDec A) := { le : A -> A -> bool }.

Contrary to Haskell, we have no special syntax for superclasses, but
this declaration is equivalent to:

.. coqdoc::

    Class `(E : EqDec A) => Ord A :=
      { le : A -> A -> bool }.


This declaration means that any instance of the ``Ord`` typeclass must have
an instance of ``EqDec``. The parameters of the subclass contain at
least all the parameters of its superclasses in their order of
appearance (here A is the only one). As we have seen, ``Ord`` is encoded
as a record type with two parameters: a type ``A`` and an ``E`` of type
``EqDec A``. However, one can still use it as if it had a single
parameter inside generalizing binders: the generalization of
superclasses will be done automatically.

.. coqtop:: all

   Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).

To specify sharing of structures, you may want to explicitly specify the
superclasses. You can do this directly in regular binders, and with the ``!``
modifier before typeclass binders. For example:

.. coqtop:: all

   Definition lt `{eqa : EqDec A, !Ord eqa} (x y : A) := andb (le x y) (neqb x y).

The ``!`` modifier switches how Coq interprets a binder. In particular, it uses
the implicit arguments mechanism if available, as shown in the example.

Substructures
~~~~~~~~~~~~~

.. index:: :> (substructure)

Substructures are components of a typeclass which are themselves instances of a
typeclass. They often arise when using typeclasses for logical properties, e.g.:

.. coqtop:: none

   Require Import Relation_Definitions.

.. coqtop:: in

   Class Reflexive (A : Type) (R : relation A) :=
     reflexivity : forall x, R x x.

   Class Transitive (A : Type) (R : relation A) :=
     transitivity : forall x y z, R x y -> R y z -> R x z.

This declares singleton typeclasses for reflexive and transitive relations,
(see the :ref:`singleton class <singleton-class>` variant for an
explanation). These may be used as parts of other typeclasses:

.. coqtop:: all

   Class PreOrder (A : Type) (R : relation A) :=
     { PreOrder_Reflexive :: Reflexive A R ;
       PreOrder_Transitive :: Transitive A R }.

The syntax ``::`` indicates that each ``PreOrder`` can be seen as a
``Reflexive`` relation. So each time a reflexive relation is needed, a
preorder can be used instead. This is very similar to the coercion
mechanism of ``Structure`` declarations. The implementation simply
declares each projection as an instance.

One can also declare existing objects or structure projections using
the :cmd:`Existing Instance` command to achieve the same effect.


Command summary
---------------

.. cmd:: Class @record_definition
         Class @ident_decl {* @binder } {? : @sort } := @constructor

   The first form declares a record and makes the record a typeclass with
   parameters :n:`{* @binder }` and the listed record fields.

   .. _singleton-class:

   The second form declares a *singleton* typeclass with a single projection.
   This singleton typeclass is a so-called *definitional typeclass*, represented simply
   as a definition ``ident binders := term`` and whose instances are
   themselves objects of this type.

   Definitional typeclasses are not wrapped
   inside records, and the trivial projection of an instance of such a
   typeclass is convertible to the instance itself. This can be useful to
   make instances of existing objects easily and to reduce proof size by
   not inserting useless trivial projections. The typeclass :term:`constant` itself is
   declared rigid during resolution so that the typeclass abstraction is
   maintained.

   The `>` in
   :token:`record_definition` currently does nothing. In a future version, it will
   create coercions as it does when used in :cmd:`Record` commands.

   Like any command declaring a record, this command supports the
   :attr:`universes(polymorphic)`, :attr:`universes(template)`,
   :attr:`universes(cumulative)` and :attr:`private(matching)` attributes.

   .. note::
      Don't confuse typeclasses with "coercion classes", described in
      `implicit coercions<classes-implicit-coercions>`.

   When record syntax is used, this command also supports the
   :attr:`projections(primitive)` :term:`attribute`.

   .. cmd:: Existing Class @qualid

      Declares a typeclass from a previously declared :term:`constant` or
      inductive definition. No methods or instances are defined.

      .. warn:: @ident is already declared as a typeclass

         This command has no effect when used on a typeclass.

.. _warn-future-coercion-class-field:

   .. warn:: A coercion will be introduced instead of an instance in future versions when using ':>' in 'Class' declarations. Replace ':>' with '::' (or use '#[global] Existing Instance field.' for compatibility with Coq < 8.17).

      In future versions, :g:`:>` will declare a :ref:`coercion<coercions>`, as
      it does for other :cmd:`Record` commands. To eliminate the warning, use
      :g:`::` instead.

   .. warn:: Ignored instance declaration for “@ident”: “@term” is not a class

      Using the ``::`` (or deprecated ``:>``) syntax with a right-hand-side that
      is not itself a Class has no effect (apart from emitting this warning).

.. cmd:: Instance {? @ident_decl {* @binder } } : @type {? @hint_info } {? {| := %{ {* @field_val } %} | := @term } }

   Declares a typeclass instance named :token:`ident_decl` of the typeclass
   :n:`@type` with the specified parameters and with
   fields defined by :token:`field_val`, where each field must be a declared field of
   the typeclass.

   Adds one or more :token:`binder`\s to declare a parameterized instance. :token:`hint_info`
   may be used to specify the hint priority, where 0 is the highest priority as for
   :tacn:`auto` hints. If the priority is not specified, the default is the number
   of non-dependent binders of the instance.  If :token:`one_pattern` is given, terms
   matching that pattern will trigger use of the instance.  Otherwise,
   use is triggered based on the conclusion of the type.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export`
   locality attributes.

   .. deprecated:: 8.14

      The default value for instance locality will change in a future release.
      Instances added outside of sections without an explicit locality are
      deprecated. We recommend using :attr:`export` where possible. This warning
      is treated as an error by default.

   Like :cmd:`Definition`, it also supports the :attr:`program`
   attribute to switch the type checking to `Program` (chapter
   :ref:`programs`) and to use the obligation mechanism to manage missing
   fields.

   Finally, it supports the lighter :attr:`refine` attribute:

   .. attr:: refine

      This :term:`attribute` can be used to leave holes or not provide all
      fields in the definition of an instance and open the tactic mode
      to fill them.  It works exactly as if no :term:`body` had been given and
      the :tacn:`refine` tactic has been used first.

   .. cmd:: Declare Instance @ident_decl {* @binder } : @term {? @hint_info }

      In a :cmd:`Module Type`, declares that a corresponding concrete
      instance should exist in any implementation of this :cmd:`Module Type`. This
      is similar to the distinction between :cmd:`Parameter` vs. :cmd:`Definition`, or
      between :cmd:`Declare Module` and :cmd:`Module`.


   .. cmd:: Existing Instance @qualid {? @hint_info }
            Existing Instances {+ @qualid } {? %| @natural }

      Adds a :term:`constant` whose type ends with
      an applied typeclass to the instance database with an optional
      priority :token:`natural`.  It can be used for redeclaring instances at the end of
      sections, or declaring structure projections as instances. This is
      equivalent to ``Hint Resolve ident : typeclass_instances``, except it
      registers instances for :cmd:`Print Instances`.

.. cmd:: Print Instances @reference

   Shows the list of instances associated with the typeclass :token:`reference`.

.. cmd:: Print Typeclasses

   Shows the list of declared typeclasses.

.. tacn:: typeclasses eauto {? {| bfs | dfs | best_effort } } {? @nat_or_var } {? with {+ @ident } }

   This proof search tactic uses the resolution engine that is run
   implicitly during type checking, known as *typeclass search*. This tactic uses a
   different resolution
   engine than :tacn:`eauto` and :tacn:`auto`. The main differences are the following:

   + Unlike :tacn:`eauto` and :tacn:`auto`, the resolution is done entirely in
     the proof engine, meaning that backtracking is
     available among dependent subgoals, and shelving goals is supported.
     ``typeclasses eauto`` is a multi-goal tactic. It analyses the dependencies
     between subgoals to avoid backtracking on subgoals that are entirely
     independent.

   + The transparency information of databases is used consistently for
     all hints declared in them. It is always used when calling the
     unifier. When considering local hypotheses, we use the transparent
     state of the first hint database given. Using an empty database
     (created with :cmd:`Create HintDb` for example) with unfoldable variables and
     :term:`constants <constant>` as the first argument of ``typeclasses eauto`` hence makes
     resolution with the local hypotheses use full conversion during
     unification.

   + The mode hints (see :cmd:`Hint Mode`) associated with a typeclass are
     taken into account by :tacn:`typeclasses eauto`. When a goal
     does not match any of the declared modes for its head (if any),
     instead of failing like :tacn:`eauto`, the goal is suspended and
     resolution proceeds on the remaining goals.
     If after one run of resolution, there remain suspended goals,
     resolution is launched against on them, until it reaches a fixed
     point when the set of remaining suspended goals does not change.
     Using `solve [typeclasses eauto]` can be used to ensure that
     no suspended goals remain.

   + When considering local hypotheses, we use the union of all the modes
     declared in the given databases.

   + The tactic may produce more than one success when used in
     backtracking tactics such as `typeclasses eauto; ...`.
     See :tacn:`ltac-seq`.

   + Use the :cmd:`Typeclasses eauto` command to customize the behavior of
     this tactic.

   :n:`{| bfs | dfs}`
     Specifies whether to use breadth-first search or depth-first search.
     The default is depth-first search, which can be changed with the
     :flag:`Typeclasses Iterative Deepening` flag.

   .. _TypeclassesEautoBestEffort:

   :n:`best_effort`
     If the `best_effort` option is given and resolution fails, `typeclasses eauto`
     returns the first partial solution in which all remaining subgoals fall into one
     of these categories:

     - Stuck goals: the head of the goal has at least one associated declared mode
       and the constraint does not match any mode declared for its head. These goals
       are shelved.

     - Mode failures: the head of the constraint has at least one matching declared mode,
       but the constraint couldn't be solved. These goals are left as subgoals of
       :n:`typeclasses eauto best_effort`.

     During type inference, typeclass resolution always uses the `best_effort` option:
     in case of failure, it constructs a partial solution for the goals and gives
     a more informative error message. It can be used the same way in interactive proofs
     to check which instances/hints are missing for a typeclass resolution to succeed.

   :n:`@nat_or_var`
     Specifies the maximum depth of the search.

      .. warning::
         The semantics for the limit :n:`@nat_or_var`
         are different than for :tacn:`auto`. By default, if no limit is given, the
         search is unbounded. Unlike :tacn:`auto`, introduction steps count against
         the limit, which might result in larger limits being necessary when
         searching with :tacn:`typeclasses eauto` than with :tacn:`auto`.

   :n:`with {+ @ident }`
     Runs resolution with the specified hint databases. It treats
     typeclass subgoals the same as other subgoals (no shelving of
     non-typeclass goals in particular), while allowing shelved goals
     to remain at any point during search.

     When :n:`with` is not specified, :tacn:`typeclasses eauto` uses
     the ``typeclass_instances`` database by default (instead of ``core``).
     Dependent subgoals are automatically shelved, and shelved goals can
     remain after resolution ends (following the behavior of Coq 8.5).

     .. note::
        ``all:once (typeclasses eauto)`` faithfully
        mimics what happens during typeclass resolution when it is called
        during refinement/type inference, except that *only* declared typeclass
        subgoals are considered at the start of resolution during type
        inference, while ``all`` can select non-typeclass subgoals as well. It might
        move to ``all:typeclasses eauto`` in future versions when the
        refinement engine will be able to backtrack.

.. tacn:: autoapply @one_term with @ident

   The tactic ``autoapply`` applies :token:`one_term` using the transparency information
   of the hint database :token:`ident`, and does *no* typeclass resolution. This can
   be used in :cmd:`Hint Extern`’s for typeclass instances (in the hint
   database ``typeclass_instances``) to allow backtracking on the typeclass
   subgoals created by the lemma application, rather than doing typeclass
   resolution locally at the hint application time.

.. _TypeclassesTransparent:

Typeclasses Transparent, Typeclasses Opaque
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Typeclasses Transparent {+ @qualid }

   Makes :token:`qualid` transparent during typeclass
   resolution.
   A shortcut for :cmd:`Hint Transparent` :n:`{+ @qualid } : typeclass_instances`

.. cmd:: Typeclasses Opaque {+ @qualid }

   Make :token:`qualid` opaque for typeclass search.
   A shortcut for :cmd:`Hint Opaque` :n:`{+ @qualid } : typeclass_instances`.

   It is useful when some :term:`constants <constant>` prevent some unifications and make
   resolution fail. It is also useful to declare constants which
   should never be unfolded during proof search, like fixpoints or
   anything which does not look like an abbreviation. This can
   additionally speed up proof search as the typeclass map can be
   indexed by such rigid constants (see
   :ref:`hintdatabases`).

By default, all :term:`constants <constant>` and local variables are considered transparent. One
should take care not to make opaque any constant that is used to abbreviate a
type, like:

.. coqdoc::
   Definition relation A := A -> A -> Prop.

.. versionadded:: 8.15

   :cmd:`Typeclasses Transparent` and :cmd:`Typeclasses Opaque`
   support locality attributes like :cmd:`Hint <Hint Opaque>` commands.

.. deprecated:: 8.15

   The default value for typeclass transparency hints will change in a future
   release. Hints added outside of sections without an explicit
   locality are now deprecated. We recommend using :attr:`export`
   where possible.

Settings
~~~~~~~~

.. flag:: Typeclasses Dependency Order

   This :term:`flag` (off by default) respects the dependency order
   between subgoals, meaning that subgoals on which other subgoals depend
   come first, while the non-dependent subgoals were put before
   the dependent ones previously (Coq 8.5 and below). This can result in
   quite different performance behaviors of proof search.

.. flag:: Typeclasses Limit Intros

   This :term:`flag` (on by default) controls the ability to apply hints while
   avoiding (functional) eta-expansions in the generated proof term. It
   does so by allowing hints that conclude in a product to apply to a
   goal with a matching product directly, avoiding an introduction.

   .. warning::

      This can be expensive as it requires rebuilding hint
      clauses dynamically, and does not benefit from the invertibility
      status of the product introduction rule, resulting in potentially more
      expensive proof search (i.e. more useless backtracking).

.. flag:: Typeclass Resolution For Conversion

   This :term:`flag` (on by default) controls the use of typeclass resolution
   when a unification problem cannot be solved during elaboration/type
   inference. With this flag on, when a unification fails, typeclass
   resolution is tried before launching unification once again.


.. flag:: Typeclasses Strict Resolution

   Typeclass declarations introduced when this :term:`flag` is set have a
   stricter resolution behavior (the flag is off by default). When
   looking for unifications of a goal with an instance of this typeclass, we
   “freeze” all the existentials appearing in the goals, meaning that
   they are considered rigid during unification and cannot be
   instantiated.


.. flag:: Typeclasses Unique Solutions

   When a typeclass resolution is launched we ensure that it has a single
   solution or fail. This :term:`flag` ensures that the resolution is canonical, but
   can make proof search much more expensive.


.. flag:: Typeclasses Unique Instances

   Typeclass declarations introduced when this :term:`flag` is set have a more
   efficient resolution behavior (the flag is off by default). When a
   solution to the typeclass goal of this typeclass is found, we never
   backtrack on it, assuming that it is canonical.

.. flag:: Typeclasses Iterative Deepening

   When this :term:`flag` is set, the proof search strategy is breadth-first search.
   Otherwise, the search strategy is depth-first search.  The default is off.
   :cmd:`Typeclasses eauto` is another way to set this flag.

.. opt:: Typeclasses Depth @natural

   This :term:`option` sets the maximum proof search depth.  The default is unbounded.
   :cmd:`Typeclasses eauto` is another way to set this option.

.. flag:: Typeclasses Debug

   Controls whether typeclass resolution steps are shown during search.  Setting this :term:`flag`
   also sets :opt:`Typeclasses Debug Verbosity` to 1.  :cmd:`Typeclasses eauto`
   is another way to set this flag.

.. opt:: Typeclasses Debug Verbosity @natural

   Determines how much information is shown for typeclass resolution steps during search.
   1 is the default level.  2 shows additional information such as tried tactics and shelving
   of goals.  Setting this :term:`option` to 1 or 2 turns on the :flag:`Typeclasses Debug` flag; setting this
   option to 0 turns that flag off.

Typeclasses eauto
~~~~~~~~~~~~~~~~~

.. cmd:: Typeclasses eauto := {? debug } {? ( {| bfs | dfs } ) } {? @natural }

   Allows more global customization of the :tacn:`typeclasses eauto` tactic.
   The options are:

   ``debug``
     Sets debug mode. In debug mode, a trace of
     successfully applied tactics is printed. Debug mode can also
     be set with :flag:`Typeclasses Debug`.

   :n:`{| bfs | dfs }`
     Specifies whether to use breadth-first search or depth-first search.
     The default is depth-first search, which can be changed with the
     :flag:`Typeclasses Iterative Deepening` flag.

   :token:`natural`
     Sets the depth limit for the search. The limit can also be set with
     :opt:`Typeclasses Depth`.
