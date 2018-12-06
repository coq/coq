.. _typeclasses:

Type Classes
============

This chapter presents a quick reference of the commands related to type
classes. For an actual introduction to typeclasses, there is a
description of the system :cite:`sozeau08` and the literature on type
classes in Haskell which also applies.


Class and Instance declarations
-------------------------------

The syntax for class and instance declarations is the same as the record
syntax of Coq:

``Class Id (`` |p_1| ``:`` |t_1| ``) ⋯ (`` |p_n| ``:`` |t_n| ``) [:
sort] := {`` |f_1| ``:`` |u_1| ``; ⋮`` |f_m| ``:`` |u_m| ``}.``

``Instance ident : Id`` |p_1| ``⋯`` |p_n| ``:= {`` |f_1| ``:=`` |t_1| ``; ⋮`` |f_m| ``:=`` |t_m| ``}.``

The |p_i| ``:`` |t_i| variables are called the *parameters* of the class and
the |f_i| ``:`` |t_i| are called the *methods*. Each class definition gives
rise to a corresponding record declaration and each instance is a
regular definition whose name is given by ident and type is an
instantiation of the record type.

We’ll use the following example class in the rest of the chapter:

.. coqtop:: in

   Class EqDec (A : Type) := {
     eqb : A -> A -> bool ;
     eqb_leibniz : forall x y, eqb x y = true -> x = y }.

This class implements a boolean equality test which is compatible with
Leibniz equality on some type. An example implementation is:

.. coqtop:: in

   Instance unit_EqDec : EqDec unit :=
    { eqb x y := true ;
      eqb_leibniz x y H :=
            match x, y return x = y with tt, tt => eq_refl tt end }.

If one does not give all the members in the Instance declaration, Coq
enters the proof-mode and the user is asked to build inhabitants of
the remaining fields, e.g.:

.. coqtop:: in

   Instance eq_bool : EqDec bool :=
   { eqb x y := if x then y else negb y }.

.. coqtop:: all

   Proof. intros x y H.

.. coqtop:: all

   destruct x ; destruct y ; (discriminate || reflexivity).

.. coqtop:: all

   Defined.

One has to take care that the transparency of every field is
determined by the transparency of the :cmd:`Instance` proof. One can use
alternatively the :cmd:`Program Instance` variant which has richer facilities
for dealing with obligations.


Binding classes
---------------

Once a typeclass is declared, one can use it in class binders:

.. coqtop:: all

   Definition neqb {A} {eqa : EqDec A} (x y : A) := negb (eqb x y).

When one calls a class method, a constraint is generated that is
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
  arguments, making derived functions as easy to use as class methods.
  In the example above, ``A`` and ``eqa`` should be set maximally implicit.
+ They support implicit quantification on partially applied type
  classes (:ref:`implicit-generalization`). Any argument not given as part of a typeclass
  binder will be automatically generalized.
+ They also support implicit quantification on :ref:`superclasses`.


Following the previous example, one can write:

.. coqtop:: all

   Generalizable Variables A B C.

   Definition neqb_implicit `{eqa : EqDec A} (x y : A) := negb (eqb x y).

Here ``A`` is implicitly generalized, and the resulting function is
equivalent to the one above.

Parameterized Instances
-----------------------

One can declare parameterized instances as in Haskell simply by giving
the constraints as a binding context before the instance, e.g.:

.. coqtop:: in

   Instance prod_eqb `(EA : EqDec A, EB : EqDec B) : EqDec (A * B) :=
   { eqb x y := match x, y with
                | (la, ra), (lb, rb) => andb (eqb la lb) (eqb ra rb)
                end }.

.. coqtop:: none

   Abort.

These instances are used just as well as lemmas in the instance hint
database.

Sections and contexts
---------------------

To ease the parametrization of developments by typeclasses, we provide a new
way to introduce variables into section contexts, compatible with the implicit
argument mechanism. The new command works similarly to the :cmd:`Variables`
vernacular, except it accepts any binding context as argument. For example:

.. coqtop:: all

   Section EqDec_defs.

     Context `{EA : EqDec A}.

     Global Instance option_eqb : EqDec (option A) :=
     { eqb x y := match x, y with
            | Some x, Some y => eqb x y
            | None, None => true
            | _, _ => false
            end }.
     Admitted.

   End EqDec_defs.

   About option_eqb.

Here the Global modifier redeclares the instance at the end of the
section, once it has been generalized by the context variables it
uses.


Building hierarchies
--------------------

.. _superclasses:

Superclasses
~~~~~~~~~~~~

One can also parameterize classes by other classes, generating a
hierarchy of classes and superclasses. In the same way, we give the
superclasses as a binding context:

.. coqtop:: all

   Class Ord `(E : EqDec A) := { le : A -> A -> bool }.

Contrary to Haskell, we have no special syntax for superclasses, but
this declaration is equivalent to:

::

    Class `(E : EqDec A) => Ord A :=
      { le : A -> A -> bool }.


This declaration means that any instance of the ``Ord`` class must have
an instance of ``EqDec``. The parameters of the subclass contain at
least all the parameters of its superclasses in their order of
appearance (here A is the only one). As we have seen, ``Ord`` is encoded
as a record type with two parameters: a type ``A`` and an ``E`` of type
``EqDec A``. However, one can still use it as if it had a single
parameter inside generalizing binders: the generalization of
superclasses will be done automatically.

.. coqtop:: all

   Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).

In some cases, to be able to specify sharing of structures, one may
want to give explicitly the superclasses. It is is possible to do it
directly in regular binders, and using the ``!`` modifier in class
binders. For example:

.. coqtop:: all

   Definition lt `{eqa : EqDec A, ! Ord eqa} (x y : A) := andb (le x y) (neqb x y).

The ``!`` modifier switches the way a binder is parsed back to the regular
interpretation of Coq. In particular, it uses the implicit arguments
mechanism if available, as shown in the example.

Substructures
~~~~~~~~~~~~~

.. index:: :> (substructure)

Substructures are components of a class which are instances of a class
themselves. They often arise when using classes for logical
properties, e.g.:

.. coqtop:: none

   Require Import Relation_Definitions.

.. coqtop:: in

   Class Reflexive (A : Type) (R : relation A) :=
     reflexivity : forall x, R x x.

   Class Transitive (A : Type) (R : relation A) :=
     transitivity : forall x y z, R x y -> R y z -> R x z.

This declares singleton classes for reflexive and transitive relations,
(see the :ref:`singleton class <singleton-class>` variant for an
explanation). These may be used as parts of other classes:

.. coqtop:: all

   Class PreOrder (A : Type) (R : relation A) :=
   { PreOrder_Reflexive :> Reflexive A R ;
     PreOrder_Transitive :> Transitive A R }.

The syntax ``:>`` indicates that each ``PreOrder`` can be seen as a
``Reflexive`` relation. So each time a reflexive relation is needed, a
preorder can be used instead. This is very similar to the coercion
mechanism of ``Structure`` declarations. The implementation simply
declares each projection as an instance.

One can also declare existing objects or structure projections using
the Existing Instance command to achieve the same effect.


Summary of the commands
-----------------------

.. cmd:: Class @ident {? @binders} : {? @sort} := {? @ident} { {+; @ident :{? >} @term } }

   The :cmd:`Class` command is used to declare a typeclass with parameters
   ``binders`` and fields the declared record fields.

Variants:

.. _singleton-class:

.. cmd:: Class @ident {? @binders} : {? @sort} := @ident : @term

   This variant declares a *singleton* class with a single method.  This
   singleton class is a so-called definitional class, represented simply
   as a definition ``ident binders := term`` and whose instances are
   themselves objects of this type. Definitional classes are not wrapped
   inside records, and the trivial projection of an instance of such a
   class is convertible to the instance itself. This can be useful to
   make instances of existing objects easily and to reduce proof size by
   not inserting useless projections. The class constant itself is
   declared rigid during resolution so that the class abstraction is
   maintained.

.. cmd:: Existing Class @ident

   This variant declares a class a posteriori from a constant or
   inductive definition. No methods or instances are defined.

   .. warn:: @ident is already declared as a typeclass

      This command has no effect when used on a typeclass.

.. cmd:: Instance @ident {? @binders} : @class t1 … tn [| priority] := { field1 := b1 ; …; fieldi := bi }

   This command is used to declare a typeclass instance named
   :token:`ident` of the class :token:`class` with parameters ``t1`` to ``tn`` and
   fields ``b1`` to ``bi``, where each field must be a declared field of
   the class.  Missing fields must be filled in interactive proof mode.

   An arbitrary context of :token:`binders` can be put after the name of the
   instance and before the colon to declare a parameterized instance. An
   optional priority can be declared, 0 being the highest priority as for
   :tacn:`auto` hints. If the priority is not specified, it defaults to the number
   of non-dependent binders of the instance.

.. cmdv:: Instance @ident {? @binders} : forall {? @binders}, @class @term__1 … @term__n [| priority] := @term

   This syntax is used for declaration of singleton class instances or
   for directly giving an explicit term of type :n:`forall @binders, @class
   @term__1 … @term__n`.  One need not even mention the unique field name for
   singleton classes.

.. cmdv:: Global Instance

   One can use the ``Global`` modifier on instances declared in a
   section so that their generalization is automatically redeclared
   after the section is closed.

.. cmdv:: Program Instance
   :name: Program Instance

   Switches the type checking to Program (chapter :ref:`programs`) and
   uses the obligation mechanism to manage missing fields.

.. cmdv:: Declare Instance
   :name: Declare Instance

   In a Module Type, this command states that a corresponding concrete
   instance should exist in any implementation of this Module Type. This
   is similar to the distinction between :cmd:`Parameter` vs. :cmd:`Definition`, or
   between :cmd:`Declare Module` and :cmd:`Module`.


Besides the :cmd:`Class` and :cmd:`Instance` vernacular commands, there are a
few other commands related to typeclasses.

.. cmd:: Existing Instance {+ @ident} [| priority]

   This command adds an arbitrary list of constants whose type ends with
   an applied typeclass to the instance database with an optional
   priority.  It can be used for redeclaring instances at the end of
   sections, or declaring structure projections as instances. This is
   equivalent to ``Hint Resolve ident : typeclass_instances``, except it
   registers instances for :cmd:`Print Instances`.

.. cmd:: Context @binders

   Declares variables according to the given binding context, which might
   use :ref:`implicit-generalization`.

.. tacn:: typeclasses eauto
   :name: typeclasses eauto

   This tactic uses a different resolution engine than :tacn:`eauto` and
   :tacn:`auto`. The main differences are the following:

   + Contrary to :tacn:`eauto` and :tacn:`auto`, the resolution is done entirely in
     the new proof engine (as of Coq 8.6), meaning that backtracking is
     available among dependent subgoals, and shelving goals is supported.
     ``typeclasses eauto`` is a multi-goal tactic. It analyses the dependencies
     between subgoals to avoid backtracking on subgoals that are entirely
     independent.

   + When called with no arguments, ``typeclasses eauto`` uses
     the ``typeclass_instances`` database by default (instead of core).
     Dependent subgoals are automatically shelved, and shelved goals can
     remain after resolution ends (following the behavior of Coq 8.5).

     .. note::
        As of Coq 8.6, ``all:once (typeclasses eauto)`` faithfully
        mimicks what happens during typeclass resolution when it is called
        during refinement/type inference, except that *only* declared class
        subgoals are considered at the start of resolution during type
        inference, while ``all`` can select non-class subgoals as well. It might
        move to ``all:typeclasses eauto`` in future versions when the
        refinement engine will be able to backtrack.

   + When called with specific databases (e.g. with), ``typeclasses eauto``
     allows shelved goals to remain at any point during search and treat
     typeclass goals like any other.

   + The transparency information of databases is used consistently for
     all hints declared in them. It is always used when calling the
     unifier. When considering local hypotheses, we use the transparent
     state of the first hint database given. Using an empty database
     (created with :cmd:`Create HintDb` for example) with unfoldable variables and
     constants as the first argument of ``typeclasses eauto`` hence makes
     resolution with the local hypotheses use full conversion during
     unification.


   .. cmdv:: typeclasses eauto @num

      .. warning::
         The semantics for the limit :n:`@num`
         is different than for auto. By default, if no limit is given, the
         search is unbounded. Contrary to :tacn:`auto`, introduction steps are
         counted, which might result in larger limits being necessary when
         searching with ``typeclasses eauto`` than with :tacn:`auto`.

   .. cmdv:: typeclasses eauto with {+ @ident}

      This variant runs resolution with the given hint databases. It treats
      typeclass subgoals the same as other subgoals (no shelving of
      non-typeclass goals in particular).

.. tacn:: autoapply @term with @ident
   :name: autoapply

   The tactic ``autoapply`` applies a term using the transparency information
   of the hint database ident, and does *no* typeclass resolution. This can
   be used in :cmd:`Hint Extern`’s for typeclass instances (in the hint
   database ``typeclass_instances``) to allow backtracking on the typeclass
   subgoals created by the lemma application, rather than doing typeclass
   resolution locally at the hint application time.

.. _TypeclassesTransparent:

Typeclasses Transparent, Typclasses Opaque
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Typeclasses Transparent {+ @ident}

   This command makes the identifiers transparent during typeclass
   resolution.

.. cmd:: Typeclasses Opaque {+ @ident}

   Make the identifiers opaque for typeclass search. It is useful when some
   constants prevent some unifications and make resolution fail. It is also
   useful to declare constants which should never be unfolded during
   proof-search, like fixpoints or anything which does not look like an
   abbreviation. This can additionally speed up proof search as the typeclass
   map can be indexed by such rigid constants (see
   :ref:`thehintsdatabasesforautoandeauto`).

By default, all constants and local variables are considered transparent. One
should take care not to make opaque any constant that is used to abbreviate a
type, like:

::

   relation A := A -> A -> Prop.

This is equivalent to ``Hint Transparent, Opaque ident : typeclass_instances``.


Options
~~~~~~~

.. flag:: Typeclasses Dependency Order

   This option (on by default since 8.6) respects the dependency order
   between subgoals, meaning that subgoals on which other subgoals depend
   come first, while the non-dependent subgoals were put before
   the dependent ones previously (Coq 8.5 and below). This can result in
   quite different performance behaviors of proof search.


.. flag:: Typeclasses Filtered Unification

   This option, available since Coq 8.6 and off by default, switches the
   hint application procedure to a filter-then-unify strategy. To apply a
   hint, we first check that the goal *matches* syntactically the
   inferred or specified pattern of the hint, and only then try to
   *unify* the goal with the conclusion of the hint. This can drastically
   improve performance by calling unification less often, matching
   syntactic patterns being very quick. This also provides more control
   on the triggering of instances. For example, forcing a constant to
   explicitely appear in the pattern will make it never apply on a goal
   where there is a hole in that place.


.. flag:: Typeclasses Limit Intros

   This option (on by default) controls the ability to apply hints while
   avoiding (functional) eta-expansions in the generated proof term. It
   does so by allowing hints that conclude in a product to apply to a
   goal with a matching product directly, avoiding an introduction.

   .. warning::

      This can be expensive as it requires rebuilding hint
      clauses dynamically, and does not benefit from the invertibility
      status of the product introduction rule, resulting in potentially more
      expensive proof-search (i.e. more useless backtracking).

.. flag:: Typeclass Resolution For Conversion

   This option (on by default) controls the use of typeclass resolution
   when a unification problem cannot be solved during elaboration/type
   inference. With this option on, when a unification fails, typeclass
   resolution is tried before launching unification once again.


.. flag:: Typeclasses Strict Resolution

   Typeclass declarations introduced when this option is set have a
   stricter resolution behavior (the option is off by default). When
   looking for unifications of a goal with an instance of this class, we
   “freeze” all the existentials appearing in the goals, meaning that
   they are considered rigid during unification and cannot be
   instantiated.


.. flag:: Typeclasses Unique Solutions

   When a typeclass resolution is launched we ensure that it has a single
   solution or fail. This ensures that the resolution is canonical, but
   can make proof search much more expensive.


.. flag:: Typeclasses Unique Instances

   Typeclass declarations introduced when this option is set have a more
   efficient resolution behavior (the option is off by default). When a
   solution to the typeclass goal of this class is found, we never
   backtrack on it, assuming that it is canonical.

.. flag:: Typeclasses Debug

   Controls whether typeclass resolution steps are shown during search.  Setting this flag
   also sets :opt:`Typeclasses Debug Verbosity` to 1.

.. opt:: Typeclasses Debug Verbosity @num
   :name: Typeclasses Debug Verbosity

   Determines how much information is shown for typeclass resolution steps during search.
   1 is the default level.  2 shows additional information such as tried tactics and shelving
   of goals.  Setting this option also sets :flag:`Typeclasses Debug`.

.. flag:: Refine Instance Mode

   This option allows to switch the behavior of instance declarations made through
   the Instance command.

   + When it is on (the default), instances that have unsolved holes in
     their proof-term silently open the proof mode with the remaining
     obligations to prove.

   + When it is off, they fail with an error instead.

Typeclasses eauto `:=`
~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Typeclasses eauto := {? debug} {? {dfs | bfs}} depth

   This command allows more global customization of the typeclass
   resolution tactic. The semantics of the options are:

   + ``debug`` In debug mode, the trace of successfully applied tactics is
     printed.

   + ``dfs, bfs`` This sets the search strategy to depth-first search (the
     default) or breadth-first search.

   + ``depth`` This sets the depth limit of the search.
