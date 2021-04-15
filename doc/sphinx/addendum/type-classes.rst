.. _typeclasses:

Typeclasses
===========

This chapter presents a quick reference of the commands related to type
classes. For an actual introduction to typeclasses, there is a
description of the system :cite:`sozeau08` and the literature on type
classes in Haskell which also applies.


Class and Instance declarations
-------------------------------

The syntax for class and instance declarations is the same as the record
syntax of Coq:

.. coqdoc::

  Class classname (p1 : t1) ⋯ (pn : tn) [: sort] := { f1 : u1 ; ⋯ ; fm : um }.

  Instance instancename q1 ⋯ qm : classname p1 ⋯ pn := { f1 := t1 ; ⋯ ; fm := tm }.

The ``pi : ti`` variables are called the *parameters* of the class and
the ``fi : ti`` are called the *methods*. Each class definition gives
rise to a corresponding record declaration and each instance is a
regular definition whose name is given by `instancename` and type is an
instantiation of the record type. The :cmd:`Class` command supports the
additional :attr:`mode` attribute to set a :ref:`mode of resolution <ClassMode>`
for queries of the class instances.

We’ll use the following example class in the rest of the chapter:

.. coqtop:: in

   #[mode="!"]
   Class EqDec (A : Type) :=
     { eqb : A -> A -> bool ;
       eqb_leibniz : forall x y, eqb x y = true -> x = y }.

This class implements a boolean equality test which is compatible with
Leibniz equality on some type.

.. note::
   The mode declaration "!" states that ``EqDec A`` class constraints can
   only be resolved when the index ``A`` is not an existential variable,
   preventing typeclass resolution to arbitrarily choose an instance in
   those cases. An even stricter choice is the mode "+" which prevents
   resolution if an existential variable appears at any position in ``A``,
   not just at the head.

An example implementation is:

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
it works similarly to the command :cmd:`Variable`, except it accepts any
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

One can also parameterize classes by other classes, generating a
hierarchy of classes and superclasses. In the same way, we give the
superclasses as a binding context:

.. coqtop:: all

   #[mode="! -"]
   Class Ord `(E : EqDec A) := { le : A -> A -> bool }.

Contrary to Haskell, we have no special syntax for superclasses, but
this declaration is equivalent to:

.. coqdoc::

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

The mode declaration states that resolution of `Ord A E` constraints
is restricted to cases where `A`'s head is determined, or equivalently
when `A` is not an existential variable, but `E` can be any term.

.. coqtop:: all

   Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).

In some cases, to be able to specify sharing of structures, one may
want to give explicitly the superclasses. It is is possible to do it
directly in regular binders, and using the ``!`` modifier in class
binders. For example:

.. coqtop:: all

   Definition lt `{eqa : EqDec A, ! Ord eqa} (x y : A) := andb (le x y) (neqb x y).

The ``!`` modifier switches the way a binder is parsed back to the usual
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

.. warn:: Ignored instance declaration for “@ident”: “@term” is not a class

   Using this ``:>`` syntax with a right-hand-side that is not itself a Class
   has no effect (apart from emitting this warning). In particular, is does not
   declare a coercion.

One can also declare existing objects or structure projections using
the Existing Instance command to achieve the same effect.


Summary of the commands
-----------------------

.. cmd:: Class @record_definition
         Class @singleton_class_definition

   .. insertprodn singleton_class_definition singleton_class_definition

   .. prodn::
      singleton_class_definition ::= {? > } @ident_decl {* @binder } {? : @sort } := @constructor

   The first form declares a record and makes the record a typeclass with parameters
   :n:`{* @binder }` and the listed record fields.

   .. _singleton-class:

   The second form declares a *singleton* class with a single method.  This
   singleton class is a so-called definitional class, represented simply
   as a definition ``ident binders := term`` and whose instances are
   themselves objects of this type. Definitional classes are not wrapped
   inside records, and the trivial projection of an instance of such a
   class is convertible to the instance itself. This can be useful to
   make instances of existing objects easily and to reduce proof size by
   not inserting useless projections. The class :term:`constant` itself is
   declared rigid during resolution so that the class abstraction is
   maintained.

   Like any command declaring a record, this command supports the
   :attr:`universes(polymorphic)`, :attr:`universes(template)`,
   :attr:`universes(cumulative)`, and :attr:`private(matching)`
   attributes. In addition, it supports the :attr:`mode` attribute.

   .. attr:: mode

      This attribute can be used to set the mode of resolution of the class
      at declaration time, using the same syntax as :cmd:`Hint Mode`,
      and is mostly equivalent to a `Hint Mode` declaration after the
      `Class` declaration, except that the `mode` declaration can survive
      section closing. The setting affects when typeclass resolution can be triggered
      on a constraint for the class, see :ref:`below <ClassMode>` for details.
      It is recommended to always set a mode when introducing a class or use
      a default mode.

   .. error: Discharging the class @ident would drop its mode declaration. Declare the class outside a section.

      If a :attr:`mode` attribute is given to a class inside a section, but no
      `default mode <TypeclassesDefaultMode>` is set, then this results in an error at section
      closing as we don't know how which mode the discharged variables for the class should have.

   .. cmd:: Existing Class @qualid

      This variant declares a class from a previously declared :term:`constant` or
      inductive definition. No methods or instances are defined. It also supports
      the :attr:`mode` attribute.

      .. warn:: @ident is already declared as a typeclass

         This command has no effect when used on a typeclass.

.. cmd:: Instance {? @ident_decl {* @binder } } : @type {? @hint_info } {? {| := %{ {* @field_def } %} | := @term } }

   Declares a typeclass instance named
   :token:`ident_decl` of the class :n:`@type` with the specified parameters and with
   fields defined by :token:`field_def`, where each field must be a declared field of
   the class.

   Adds one or more :token:`binder`\s to declare a parameterized instance. :token:`hint_info`
   may be used to specify the hint priority, where 0 is the highest priority as for
   :tacn:`auto` hints. If the priority is not specified, the default is the number
   of non-dependent binders of the instance.  If :token:`one_pattern` is given, terms
   matching that pattern will trigger use of the instance.  Otherwise,
   use is triggered based on the conclusion of the type.

   This command supports the :attr:`global` attribute that can be
   used on instances declared in a section so that their
   generalization is automatically redeclared when the section is
   closed.

   Like :cmd:`Definition`, it also supports the :attr:`program`
   attribute to switch the type checking to `Program` (chapter
   :ref:`programs`) and to use the obligation mechanism to manage missing
   fields.

   Finally, it supports the lighter :attr:`refine` attribute:

   .. attr:: refine

      This attribute can be used to leave holes or not provide all
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

   .. flag:: Instance Generalized Output

      .. deprecated:: 8.13

      Disabled by default, this provides compatibility with Coq
      version 8.12 and earlier.

      When enabled, the type of the instance is implicitly generalized
      over unbound and :ref:`generalizable <implicit-generalization>` variables as though surrounded by ``\`{}``.

.. cmd:: Print Instances @reference

   Shows the list of instances associated with the typeclass :token:`reference`.


.. tacn:: typeclasses eauto {? bfs } {? @nat_or_var } {? with {+ @ident } }

   This proof search tactic uses the resolution engine that is run
   implicitly during type checking. This tactic uses a different resolution
   engine than :tacn:`eauto` and :tacn:`auto`. The main differences are the
   following:

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

.. _ClassMode:

   + The mode hints (see :cmd:`Hint Mode`) associated with a class are
     taken into account by typeclass resolution and :tacn:`typeclasses eauto`.
     When a goal does not match any of the declared modes for its head (if any),
     instead of failing like :tacn:`eauto`, the goal is suspended and
     resolution proceeds on the remaining goals.
     If after one run of resolution, there remains suspended goals,
     resolution is launched against on them, until it reaches a fixed
     point when the set of remaining suspended goals does not change.
     Using `solve [typeclasses eauto]` can be used to ensure that
     no suspended goals remain.

   + When considering local hypotheses, we use the union of all the modes
     declared in the given databases.

   + Use the :cmd:`Typeclasses eauto` command to customize the behavior of
     this tactic.

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
        during refinement/type inference, except that *only* declared class
        subgoals are considered at the start of resolution during type
        inference, while ``all`` can select non-class subgoals as well. It might
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
   :ref:`thehintsdatabasesforautoandeauto`).

By default, all :term:`constants <constant>` and local variables are considered transparent. One
should take care not to make opaque any constant that is used to abbreviate a
type, like:

.. coqdoc::
   Definition relation A := A -> A -> Prop.


Settings
~~~~~~~~

.. flag:: Typeclasses Dependency Order

   This flag (off by default) respects the dependency order
   between subgoals, meaning that subgoals on which other subgoals depend
   come first, while the non-dependent subgoals were put before
   the dependent ones previously (Coq 8.5 and below). This can result in
   quite different performance behaviors of proof search.

   .. _TypeclassesDefaultMode:

.. opt:: Typeclasses Default Mode {? ( {| "+" | "-" | "!" } ) }.

   This option (unset by default) controls the default mode declaration
   associated to a :cmd:`Class`. If set, the each class declaration uses
   this default mode for *all* its indices, unless an :attr:`mode` attribute
   is used to set the mode explicitly.

   .. warn:: Using inferred default mode declaration “mode” for “@ident”

      This (by default disabled) warning informs the user when a mode has been assigned
      automatically. It can be used to lint a library and ensure all typeclasses
      have been assigned explicit mode declarations.

.. flag:: Typeclasses Filtered Unification

   This flag, which is off by default, switches the
   hint application procedure to a filter-then-unify strategy. To apply a
   hint, we first check that the goal *matches* syntactically the
   inferred or specified pattern of the hint, and only then try to
   *unify* the goal with the conclusion of the hint. This can drastically
   improve performance by calling unification less often, matching
   syntactic patterns being very quick. This also provides more control
   on the triggering of instances. For example, forcing a :term:`constant` to
   explicitly appear in the pattern will make it never apply on a goal
   where there is a hole in that place.


.. flag:: Typeclasses Limit Intros

   This flag (on by default) controls the ability to apply hints while
   avoiding (functional) eta-expansions in the generated proof term. It
   does so by allowing hints that conclude in a product to apply to a
   goal with a matching product directly, avoiding an introduction.

   .. warning::

      This can be expensive as it requires rebuilding hint
      clauses dynamically, and does not benefit from the invertibility
      status of the product introduction rule, resulting in potentially more
      expensive proof search (i.e. more useless backtracking).

.. flag:: Typeclass Resolution For Conversion

   This flag (on by default) controls the use of typeclass resolution
   when a unification problem cannot be solved during elaboration/type
   inference. With this flag on, when a unification fails, typeclass
   resolution is tried before launching unification once again.


.. flag:: Typeclasses Strict Resolution

   Typeclass declarations introduced when this flag is set have a
   stricter resolution behavior (the flag is off by default). When
   looking for unifications of a goal with an instance of this class, we
   “freeze” all the existentials appearing in the goals, meaning that
   they are considered rigid during unification and cannot be
   instantiated.


.. flag:: Typeclasses Unique Solutions

   When a typeclass resolution is launched we ensure that it has a single
   solution or fail. This ensures that the resolution is canonical, but
   can make proof search much more expensive.


.. flag:: Typeclasses Unique Instances

   Typeclass declarations introduced when this flag is set have a more
   efficient resolution behavior (the flag is off by default). When a
   solution to the typeclass goal of this class is found, we never
   backtrack on it, assuming that it is canonical.

.. flag:: Typeclasses Iterative Deepening

   When this flag is set, the proof search strategy is breadth-first search.
   Otherwise, the search strategy is depth-first search.  The default is off.
   :cmd:`Typeclasses eauto` is another way to set this flag.

.. opt:: Typeclasses Depth @natural

   Sets the maximum proof search depth.  The default is unbounded.
   :cmd:`Typeclasses eauto` is another way to set this option.

.. flag:: Typeclasses Debug

   Controls whether typeclass resolution steps are shown during search.  Setting this flag
   also sets :opt:`Typeclasses Debug Verbosity` to 1.  :cmd:`Typeclasses eauto`
   is another way to set this flag.

.. opt:: Typeclasses Debug Verbosity @natural

   Determines how much information is shown for typeclass resolution steps during search.
   1 is the default level.  2 shows additional information such as tried tactics and shelving
   of goals.  Setting this option to 1 or 2 turns on the :flag:`Typeclasses Debug` flag; setting this
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

   ``dfs``, ``bfs``
     Sets the search strategy to depth-first
     search (the default) or breadth-first search. The search strategy
     can also be set with :flag:`Typeclasses Iterative Deepening`.

   :token:`natural`
     Sets the depth limit for the search. The limit can also be set with
     :opt:`Typeclasses Depth`.
