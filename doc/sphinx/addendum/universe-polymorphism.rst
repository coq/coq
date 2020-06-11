.. _polymorphicuniverses:

Polymorphic Universes
======================

:Author: Matthieu Sozeau

General Presentation
---------------------

.. warning::

   The status of Universe Polymorphism is experimental.

This section describes the universe polymorphic extension of |Coq|.
Universe polymorphism makes it possible to write generic definitions
making use of universes and reuse them at different and sometimes
incompatible universe levels.

A standard example of the difference between universe *polymorphic*
and *monomorphic* definitions is given by the identity function:

.. coqtop:: in

   Definition identity {A : Type} (a : A) := a.

By default, constant declarations are monomorphic, hence the identity
function declares a global universe (say ``Top.1``) for its domain.
Subsequently, if we try to self-apply the identity, we will get an
error:

.. coqtop:: all

   Fail Definition selfid := identity (@identity).

Indeed, the global level ``Top.1`` would have to be strictly smaller than
itself for this self-application to type check, as the type of
:g:`(@identity)` is :g:`forall (A : Type@{Top.1}), A -> A` whose type is itself
:g:`Type@{Top.1+1}`.

A universe polymorphic identity function binds its domain universe
level at the definition level instead of making it global.

.. coqtop:: in

   Polymorphic Definition pidentity {A : Type} (a : A) := a.

.. coqtop:: all

   About pidentity.

It is then possible to reuse the constant at different levels, like
so:

.. coqtop:: in

   Definition selfpid := pidentity (@pidentity).

Of course, the two instances of :g:`pidentity` in this definition are
different. This can be seen when the :flag:`Printing Universes` flag is on:

.. coqtop:: none

   Set Printing Universes.

.. coqtop:: all

   Print selfpid.

Now :g:`pidentity` is used at two different levels: at the head of the
application it is instantiated at ``Top.3`` while in the argument position
it is instantiated at ``Top.4``. This definition is only valid as long as
``Top.4`` is strictly smaller than ``Top.3``, as shown by the constraints. Note
that this definition is monomorphic (not universe polymorphic), so the
two universes (in this case ``Top.3`` and ``Top.4``) are actually global
levels.

When printing :g:`pidentity`, we can see the universes it binds in
the annotation :g:`@{Top.2}`. Additionally, when
:flag:`Printing Universes` is on we print the "universe context" of
:g:`pidentity` consisting of the bound universes and the
constraints they must verify (for :g:`pidentity` there are no constraints).

Inductive types can also be declared universes polymorphic on
universes appearing in their parameters or fields. A typical example
is given by monoids:

.. coqtop:: in

   Polymorphic Record Monoid := { mon_car :> Type; mon_unit : mon_car;
     mon_op : mon_car -> mon_car -> mon_car }.

.. coqtop:: in

   Print Monoid.

The Monoid's carrier universe is polymorphic, hence it is possible to
instantiate it for example with :g:`Monoid` itself. First we build the
trivial unit monoid in :g:`Set`:

.. coqtop:: in

   Definition unit_monoid : Monoid :=
     {| mon_car := unit; mon_unit := tt; mon_op x y := tt |}.

From this we can build a definition for the monoid of :g:`Set`\-monoids
(where multiplication would be given by the product of monoids).

.. coqtop:: in

   Polymorphic Definition monoid_monoid : Monoid.
     refine (@Build_Monoid Monoid unit_monoid (fun x y => x)).
   Defined.

.. coqtop:: all

   Print monoid_monoid.

As one can see from the constraints, this monoid is “large”, it lives
in a universe strictly higher than :g:`Set`.

Polymorphic, Monomorphic
-------------------------

.. attr:: universes(polymorphic)

   This attribute can be used to declare universe polymorphic
   definitions and inductive types.  There is also a legacy syntax
   using the ``Polymorphic`` prefix (see :n:`@legacy_attr`) which, as
   shown in the examples, is more commonly used.

.. flag:: Universe Polymorphism

   This flag is off by default.  When it is on, new declarations are
   polymorphic unless the :attr:`universes(monomorphic)` attribute is
   used.

.. attr:: universes(monomorphic)

   This attribute can be used to declare universe monomorphic
   definitions and inductive types (i.e. global universe constraints
   are produced), even when the :flag:`Universe Polymorphism` flag is
   on.  There is also a legacy syntax using the ``Monomorphic`` prefix
   (see :n:`@legacy_attr`).

Many other commands can be used to declare universe polymorphic or
monomorphic constants depending on whether the :flag:`Universe
Polymorphism` flag is on or the :attr:`universes(polymorphic)` or
:attr:`universes(monomorphic)` attributes are used:

- :cmd:`Lemma`, :cmd:`Axiom`, etc. can be used to declare universe
  polymorphic constants.

- Using the :attr:`universes(polymorphic)` attribute with the
  :cmd:`Section` command will locally set the polymorphism flag inside
  the section.

- :cmd:`Variable`, :cmd:`Context`, :cmd:`Universe` and
  :cmd:`Constraint` in a section support polymorphism. See
  :ref:`universe-polymorphism-in-sections` for more details.

- Using the :attr:`universes(polymorphic)` attribute with the
  :cmd:`Hint Resolve` or :cmd:`Hint Rewrite` commands will make
  :tacn:`auto` / :tacn:`rewrite` use the hint polymorphically, not at
  a single instance.

.. _cumulative:

Cumulative, NonCumulative
-------------------------

.. attr:: universes(cumulative)

   Polymorphic inductive types, coinductive types, variants and
   records can be declared cumulative using this attribute or the
   legacy ``Cumulative`` prefix (see :n:`@legacy_attr`) which, as
   shown in the examples, is more commonly used.

   This means that two instances of the same inductive type (family)
   are convertible based on the universe variances; they do not need
   to be equal.

   .. exn:: The cumulative and noncumulative attributes can only be used in a polymorphic context.

      Using this attribute requires being in a polymorphic context,
      i.e. either having the :flag:`Universe Polymorphism` flag on, or
      having used the :attr:`universes(polymorphic)` attribute as
      well.

   .. note::

      ``#[ universes(polymorphic), universes(cumulative) ]`` can be
      abbreviated into ``#[ universes(polymorphic, cumulative) ]``.

.. flag:: Polymorphic Inductive Cumulativity

   When this flag is on (it is off by default), it makes all
   subsequent *polymorphic* inductive definitions cumulative, unless
   the :attr:`universes(noncumulative)` attribute is used.  It has no
   effect on *monomorphic* inductive definitions.

.. attr:: universes(noncumulative)

   Declares the inductive type as non-cumulative even if the
   :flag:`Polymorphic Inductive Cumulativity` flag is on.  There is
   also a legacy syntax using the ``NonCumulative`` prefix (see
   :n:`@legacy_attr`).

   This means that two instances of the same inductive type (family)
   are convertible only if all the universes are equal.

Consider the examples below.

.. coqtop:: in

   Polymorphic Cumulative Inductive list {A : Type} :=
   | nil : list
   | cons : A -> list -> list.

.. coqtop:: all

   Print list.

When printing :g:`list`, the universe context indicates the subtyping
constraints by prefixing the level names with symbols.

Because inductive subtypings are only produced by comparing inductives
to themselves with universes changed, they amount to variance
information: each universe is either invariant, covariant or
irrelevant (there are no contravariant subtypings in |Coq|),
respectively represented by the symbols `=`, `+` and `*`.

Here we see that :g:`list` binds an irrelevant universe, so any two
instances of :g:`list` are convertible: :math:`E[Γ] ⊢ \mathsf{list}@\{i\}~A
=_{βδιζη} \mathsf{list}@\{j\}~B` whenever :math:`E[Γ] ⊢ A =_{βδιζη} B` and
this applies also to their corresponding constructors, when
they are comparable at the same type.

See :ref:`Conversion-rules` for more details on convertibility and subtyping.
The following is an example of a record with non-trivial subtyping relation:

.. coqtop:: all

   Polymorphic Cumulative Record packType := {pk : Type}.

:g:`packType` binds a covariant universe, i.e.

.. math::

   E[Γ] ⊢ \mathsf{packType}@\{i\} =_{βδιζη}
   \mathsf{packType}@\{j\}~\mbox{ whenever }~i ≤ j

An example of a proof using cumulativity
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. coqtop:: in reset

   Set Universe Polymorphism.
   Set Polymorphic Inductive Cumulativity.

   Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := eq_refl : eq x x.

   Definition funext_type@{a b e} (A : Type@{a}) (B : A -> Type@{b})
   := forall f g : (forall a, B a),
                   (forall x, eq@{e} (f x) (g x))
                   -> eq@{e} f g.

   Section down.
      Universes a b e e'.
      Constraint e' < e.
      Lemma funext_down {A B}
        (H : @funext_type@{a b e} A B) : @funext_type@{a b e'} A B.
      Proof.
        exact H.
      Defined.
   End down.

Cumulativity Weak Constraints
-----------------------------

.. flag:: Cumulativity Weak Constraints

   When set, which is the default, causes "weak" constraints to be produced
   when comparing universes in an irrelevant position. Processing weak
   constraints is delayed until minimization time. A weak constraint
   between `u` and `v` when neither is smaller than the other and
   one is flexible causes them to be unified. Otherwise the constraint is
   silently discarded.

   This heuristic is experimental and may change in future versions.
   Disabling weak constraints is more predictable but may produce
   arbitrary numbers of universes.


Global and local universes
---------------------------

Each universe is declared in a global or local environment before it
can be used. To ensure compatibility, every *global* universe is set
to be strictly greater than :g:`Set` when it is introduced, while every
*local* (i.e. polymorphically quantified) universe is introduced as
greater or equal to :g:`Set`.


Conversion and unification
---------------------------

The semantics of conversion and unification have to be modified a
little to account for the new universe instance arguments to
polymorphic references. The semantics respect the fact that
definitions are transparent, so indistinguishable from their bodies
during conversion.

This is accomplished by changing one rule of unification, the first-
order approximation rule, which applies when two applicative terms
with the same head are compared. It tries to short-cut unfolding by
comparing the arguments directly. In case the constant is universe
polymorphic, we allow this rule to fire only when unifying the
universes results in instantiating a so-called flexible universe
variables (not given by the user). Similarly for conversion, if such
an equation of applicative terms fail due to a universe comparison not
being satisfied, the terms are unfolded. This change implies that
conversion and unification can have different unfolding behaviors on
the same development with universe polymorphism switched on or off.


Minimization
-------------

Universe polymorphism with cumulativity tends to generate many useless
inclusion constraints in general. Typically at each application of a
polymorphic constant :g:`f`, if an argument has expected type :g:`Type@{i}`
and is given a term of type :g:`Type@{j}`, a :math:`j ≤ i` constraint will be
generated. It is however often the case that an equation :math:`j = i` would
be more appropriate, when :g:`f`\'s universes are fresh for example.
Consider the following example:

.. coqtop:: none

   Polymorphic Definition pidentity {A : Type} (a : A) := a.
   Set Printing Universes.

.. coqtop:: in

   Definition id0 := @pidentity nat 0.

.. coqtop:: all

   Print id0.

This definition is elaborated by minimizing the universe of :g:`id0` to
level :g:`Set` while the more general definition would keep the fresh level
:g:`i` generated at the application of :g:`id` and a constraint that :g:`Set` :math:`≤ i`.
This minimization process is applied only to fresh universe variables.
It simply adds an equation between the variable and its lower bound if
it is an atomic universe (i.e. not an algebraic max() universe).

.. flag:: Universe Minimization ToSet

   Turning this flag off (it is on by default) disallows minimization
   to the sort :g:`Set` and only collapses floating universes between
   themselves.

.. _explicit-universes:

Explicit Universes
-------------------

.. insertprodn universe_name univ_constraint

.. prodn::
   universe_name ::= @qualid
   | Set
   | Prop
   univ_annot ::= @%{ {* @universe_level } %}
   universe_level ::= Set
   | Prop
   | Type
   | _
   | @qualid
   univ_decl ::= @%{ {* @ident } {? + } {? %| {*, @univ_constraint } {? + } } %}
   univ_constraint ::= @universe_name {| < | = | <= } @universe_name

The syntax has been extended to allow users to explicitly bind names
to universes and explicitly instantiate polymorphic definitions.

.. cmd:: Universe @ident
         Polymorphic Universe @ident

   In the monorphic case, this command declares a new global universe
   named :token:`ident`, which can be referred to using its qualified name
   as well. Global universe names live in a separate namespace. The
   command supports the :attr:`universes(polymorphic)` attribute (or
   the ``Polymorphic`` prefix) only in sections, meaning the universe
   quantification will be discharged on each section definition
   independently.

   .. exn:: Polymorphic universes can only be declared inside sections, use Monomorphic Universe instead.
      :undocumented:

.. cmd:: Constraint @univ_constraint
         Polymorphic Constraint @univ_constraint

   This command declares a new constraint between named universes.

   If consistent, the constraint is then enforced in the global
   environment. Like :cmd:`Universe`, it can be used with the
   :attr:`universes(polymorphic)` attribute (or the ``Polymorphic``
   prefix) in sections only to declare constraints discharged at
   section closing time. One cannot declare a global constraint on
   polymorphic universes.

   .. exn:: Undeclared universe @ident.
      :undocumented:

   .. exn:: Universe inconsistency.
      :undocumented:

   .. exn:: Polymorphic universe constraints can only be declared inside sections, use Monomorphic Constraint instead
      :undocumented:

.. _printing-universes:

Printing universes
------------------

.. flag:: Printing Universes

   Turn this flag on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard flag, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. cmd:: Print {? Sorted } Universes {? Subgraph ( {* @qualid } ) } {? @string }
   :name: Print Universes

   This command can be used to print the constraints on the internal level
   of the occurrences of :math:`\Type` (see :ref:`Sorts`).

   The :n:`Subgraph` clause limits the printed graph to the requested names (adjusting
   constraints to preserve the implied transitive constraints between
   kept universes).

   The :n:`Sorted` clause makes each universe
   equivalent to a numbered label reflecting its level (with a linear
   ordering) in the universe hierarchy.

   :n:`@string` is an optional output filename.
   If :n:`@string` ends in ``.dot`` or ``.gv``, the constraints are printed in the DOT
   language, and can be processed by Graphviz tools. The format is
   unspecified if `string` doesn’t end in ``.dot`` or ``.gv``.

Polymorphic definitions
~~~~~~~~~~~~~~~~~~~~~~~

For polymorphic definitions, the declaration of (all) universe levels
introduced by a definition uses the following syntax:

.. coqtop:: in

   Polymorphic Definition le@{i j} (A : Type@{i}) : Type@{j} := A.

.. coqtop:: all

   Print le.

During refinement we find that :g:`j` must be larger or equal than :g:`i`, as we
are using :g:`A : Type@{i} <= Type@{j}`, hence the generated constraint. At the
end of a definition or proof, we check that the only remaining
universes are the ones declared. In the term and in general in proof
mode, introduced universe names can be referred to in terms. Note that
local universe names shadow global universe names. During a proof, one
can use :cmd:`Show Universes` to display the current context of universes.

It is possible to provide only some universe levels and let |Coq| infer the others
by adding a :g:`+` in the list of bound universe levels:

.. coqtop:: all

   Fail Definition foobar@{u} : Type@{u} := Type.
   Definition foobar@{u +} : Type@{u} := Type.
   Set Printing Universes.
   Print foobar.

This can be used to find which universes need to be explicitly bound in a given
definition.

Definitions can also be instantiated explicitly, giving their full
instance:

.. coqtop:: all

   Check (pidentity@{Set}).
   Monomorphic Universes k l.
   Check (le@{k l}).

User-named universes and the anonymous universe implicitly attached to
an explicit :g:`Type` are considered rigid for unification and are never
minimized. Flexible anonymous universes can be produced with an
underscore or by omitting the annotation to a polymorphic definition.

.. coqtop:: all

   Check (fun x => x) : Type -> Type.
   Check (fun x => x) : Type -> Type@{_}.

   Check le@{k _}.
   Check le.

.. flag:: Strict Universe Declaration

   Turning this flag off allows one to freely use
   identifiers for universes without declaring them first, with the
   semantics that the first use declares it. In this mode, the universe
   names are not associated with the definition or proof once it has been
   defined. This is meant mainly for debugging purposes.

.. flag:: Private Polymorphic Universes

   This flag, on by default, removes universes which appear only in
   the body of an opaque polymorphic definition from the definition's
   universe arguments. As such, no value needs to be provided for
   these universes when instantiating the definition. Universe
   constraints are automatically adjusted.

   Consider the following definition:

   .. coqtop:: all

      Lemma foo@{i} : Type@{i}.
      Proof. exact Type. Qed.
      Print foo.

   The universe :g:`Top.xxx` for the :g:`Type` in the body cannot be accessed, we
   only care that one exists for any instantiation of the universes
   appearing in the type of :g:`foo`. This is guaranteed when the
   transitive constraint ``Set <= Top.xxx < i`` is verified. Then when
   using the constant we don't need to put a value for the inner
   universe:

   .. coqtop:: all

      Check foo@{_}.

   and when not looking at the body we don't mention the private
   universe:

   .. coqtop:: all

      About foo.

   To recover the same behaviour with regard to universes as
   :g:`Defined`, the :flag:`Private Polymorphic Universes` flag may
   be unset:

   .. coqtop:: all

      Unset Private Polymorphic Universes.

      Lemma bar : Type. Proof. exact Type. Qed.
      About bar.
      Fail Check bar@{_}.
      Check bar@{_ _}.

   Note that named universes are always public.

   .. coqtop:: all

      Set Private Polymorphic Universes.
      Unset Strict Universe Declaration.

      Lemma baz : Type@{outer}. Proof. exact Type@{inner}. Qed.
      About baz.

.. _universe-polymorphism-in-sections:

Universe polymorphism and sections
----------------------------------

:cmd:`Variables`, :cmd:`Context`, :cmd:`Universe` and
:cmd:`Constraint` in a section support polymorphism. This means that
the universe variables and their associated constraints are discharged
polymorphically over definitions that use them. In other words, two
definitions in the section sharing a common variable will both get
parameterized by the universes produced by the variable declaration.
This is in contrast to a “mononorphic” variable which introduces
global universes and constraints, making the two definitions depend on
the *same* global universes associated to the variable.

It is possible to mix universe polymorphism and monomorphism in
sections, except in the following ways:

- no monomorphic constraint may refer to a polymorphic universe:

  .. coqtop:: all reset

     Section Foo.

       Polymorphic Universe i.
       Fail Constraint i = i.

  This includes constraints implicitly declared by commands such as
  :cmd:`Variable`, which may need to be used with universe
  polymorphism activated (locally by attribute or globally by option):

  .. coqtop:: all

     Fail Variable A : (Type@{i} : Type).
     Polymorphic Variable A : (Type@{i} : Type).

  (in the above example the anonymous :g:`Type` constrains polymorphic
  universe :g:`i` to be strictly smaller.)

- no monomorphic constant or inductive may be declared if polymorphic
  universes or universe constraints are present.

These restrictions are required in order to produce a sensible result
when closing the section (the requirement on constants and inductives
is stricter than the one on constraints, because constants and
inductives are abstracted by *all* the section's polymorphic universes
and constraints).
