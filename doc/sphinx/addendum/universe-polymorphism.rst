.. _polymorphicuniverses:

Polymorphic Universes
======================

:Author: Matthieu Sozeau

General Presentation
---------------------

.. warning::

   The status of Universe Polymorphism is experimental.

This section describes the universe polymorphic extension of Rocq.
Universe polymorphism makes it possible to write generic definitions
making use of universes and reuse them at different and sometimes
incompatible universe levels.

A standard example of the difference between universe *polymorphic*
and *monomorphic* definitions is given by the identity function:

.. rocqtop:: in

   Definition identity {A : Type} (a : A) := a.

By default, :term:`constant` declarations are monomorphic, hence the identity
function declares a global universe (automatically named ``identity.u0``) for its domain.
Subsequently, if we try to self-apply the identity, we will get an
error:

.. rocqtop:: all

   Fail Definition selfid := identity (@identity).

Indeed, the global level ``identity.u0`` would have to be strictly smaller than
itself for this self-application to type check, as the type of
:g:`(@identity)` is :g:`forall (A : Type@{identity.u0}), A -> A` whose type is itself
:g:`Type@{identity.u0+1}`.

A universe polymorphic identity function binds its domain universe
level at the definition level instead of making it global.

.. rocqtop:: in

   Polymorphic Definition pidentity {A : Type} (a : A) := a.

.. rocqtop:: all

   About pidentity.

It is then possible to reuse the constant at different levels, like
so:

.. rocqtop:: in

   Polymorphic Definition selfpid := pidentity (@pidentity).

Of course, the two instances of :g:`pidentity` in this definition are
different. This can be seen when the :flag:`Printing Universes` flag is on:

.. rocqtop:: all

   Set Printing Universes.
   Print selfpid.

Now :g:`pidentity` is used at two different levels: at the head of the
application it is instantiated at ``u`` while in the argument position
it is instantiated at ``u0``. This definition is only valid as long as
``u0`` is strictly smaller than ``u``, as shown by the constraints.
Note that if we made ``selfpid`` universe monomorphic, the two
universes (in this case ``u`` and ``u0``) would be declared in the
global universe graph with names ``selfpid.u0`` and ``selfpid.u1``.
Since the constraints would be global, ``Print selfpid.`` will
not show them, however they will be shown by :cmd:`Print Universes`.

When printing :g:`pidentity`, we can see the universes it binds in
the annotation :g:`@{u}`. Additionally, when
:flag:`Printing Universes` is on we print the "universe context" of
:g:`pidentity` consisting of the bound universes and the
constraints they must verify (for :g:`pidentity` there are no constraints).

Inductive types can also be declared universe polymorphic on
universes appearing in their parameters or fields. A typical example
is given by monoids. We first put ourselves in a mode where every declaration
is universe-polymorphic:

.. rocqtop:: in

   Set Universe Polymorphism.

.. rocqtop:: in

   Record Monoid := { mon_car :> Type; mon_unit : mon_car;
     mon_op : mon_car -> mon_car -> mon_car }.

A monoid is here defined by a carrier type, a unit in this type
and a binary operation.

.. rocqtop:: all

   Print Monoid.

The Monoid's carrier universe is polymorphic, hence it is possible to
instantiate it for example with :g:`Monoid` itself. First we build the
trivial unit monoid in any universe :g:`i >= Set`:

.. rocqtop:: in

   Definition unit_monoid@{i} : Monoid@{i} :=
     {| mon_car := unit; mon_unit := tt; mon_op x y := tt |}.

Here we are using the fact that :g:`unit : Set` and by cumulativity,
any polymorphic universe is greater or equal to `Set`.

From this we can build a definition for the monoid of monoids,
where multiplication is given by the product of monoids. To do so, we
first need to define a universe-polymorphic variant of pairs:

.. rocqtop:: in

  Record pprod@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i,j)} :=
    ppair { pfst : A; psnd : B }.

  Arguments ppair {A} {B}.
  Infix "**" := pprod (at level 40, left associativity) : type_scope.
  Notation "( x ; y ; .. ; z )" := (ppair .. (ppair x y) .. z) (at level 0) : core_scope.

The monoid of monoids uses the cartesian product of monoids as its operation:

.. rocqtop:: in

    Definition monoid_op@{i} (m m' : Monoid@{i}) (x y : mon_car m ** mon_car m') :
       mon_car m ** mon_car m' :=
      let (l, r) := x in
      let (l', r') := y in
      (mon_op m l l'; mon_op m' r r').

    Definition prod_monoid@{i} (m m' : Monoid@{i}): Monoid@{i} :=
      {| mon_car := (m ** m')%type;
         mon_unit := (mon_unit m; mon_unit m');
         mon_op := (monoid_op m m') |}.

    Definition monoids_monoid@{i j | i < j} : Monoid@{j} :=
      {| mon_car := Monoid@{i};
         mon_unit := unit_monoid@{i};
         mon_op := prod_monoid@{i} |}.

.. rocqtop:: all

   Print monoids_monoid.

As one can see from the constraints, this monoid is “large”, it lives
in a universe strictly higher than its objects, monoids in the universes :g:`i`.

Polymorphic, Monomorphic
-------------------------

.. attr:: universes(polymorphic{? = {| yes | no } })
   :name: universes(polymorphic); Polymorphic; Monomorphic

   This :term:`boolean attribute` can be used to control whether universe
   polymorphism is enabled in the definition of an inductive type.
   There is also a legacy syntax using the ``Polymorphic`` prefix (see
   :n:`@legacy_attr`) which, as shown in the examples, is more
   commonly used.

   When ``universes(polymorphic=no)`` is used, global universe constraints
   are produced, even when the :flag:`Universe Polymorphism` flag is
   on. There is also a legacy syntax using the ``Monomorphic`` prefix
   (see :n:`@legacy_attr`).

.. flag:: Universe Polymorphism

   This :term:`flag` is off by default.  When it is on, new declarations are
   polymorphic unless the :attr:`universes(polymorphic=no) <universes(polymorphic)>`
   attribute is used to override the default.

Many other commands can be used to declare universe polymorphic or
monomorphic :term:`constants <constant>` depending on whether the :flag:`Universe
Polymorphism` flag is on or the :attr:`universes(polymorphic)`
attribute is used:

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

.. attr:: universes(cumulative{? = {| yes | no } })
   :name: universes(cumulative); Cumulative; NonCumulative

   Polymorphic inductive types, coinductive types, variants and
   records can be declared cumulative using this :term:`boolean attribute`
   or the legacy ``Cumulative`` prefix (see :n:`@legacy_attr`) which, as
   shown in the examples, is more commonly used.

   This means that two instances of the same inductive type (family)
   are convertible based on the universe variances; they do not need
   to be equal.

   When the attribtue is off, the inductive type is non-cumulative
   even if the :flag:`Polymorphic Inductive Cumulativity` flag is on.
   There is also a legacy syntax using the ``NonCumulative`` prefix
   (see :n:`@legacy_attr`).

   This means that two instances of the same inductive type (family)
   are convertible only if all the universes are equal.

   .. exn:: The cumulative attribute can only be used in a polymorphic context.

      Using this attribute requires being in a polymorphic context,
      i.e. either having the :flag:`Universe Polymorphism` flag on, or
      having used the :attr:`universes(polymorphic)` attribute as
      well.

   .. note::

      :n:`#[ universes(polymorphic{? = yes }), universes(cumulative{? = {| yes | no } }) ]` can be
      abbreviated into :n:`#[ universes(polymorphic{? = yes }, cumulative{? = {| yes | no } }) ]`.

.. flag:: Polymorphic Inductive Cumulativity

   When this :term:`flag` is on (it is off by default), it makes all
   subsequent *polymorphic* inductive definitions cumulative, unless
   the :attr:`universes(cumulative=no) <universes(cumulative)>` attribute is
   used to override the default.  It has no effect on *monomorphic* inductive definitions.

Consider the examples below.

.. rocqtop:: in reset

   Polymorphic Cumulative Inductive list {A : Type} :=
   | nil : list
   | cons : A -> list -> list.

.. rocqtop:: all

   Set Printing Universes.
   Print list.

When printing :g:`list`, the universe context indicates the subtyping
constraints by prefixing the level names with symbols.

Because inductive subtypings are only produced by comparing inductives
to themselves with universes changed, they amount to variance
information: each universe is either invariant, covariant or
irrelevant (there are no contravariant subtypings in Rocq),
respectively represented by the symbols `=`, `+` and `*`.

Here we see that :g:`list` binds an irrelevant universe, so any two
instances of :g:`list` are convertible: :math:`E[Γ] ⊢ \mathsf{list}@\{i\}~A
=_{βδιζη} \mathsf{list}@\{j\}~B` whenever :math:`E[Γ] ⊢ A =_{βδιζη} B` and
this applies also to their corresponding constructors, when
they are comparable at the same type.

See :ref:`Conversion-rules` for more details on convertibility and subtyping.
The following is an example of a record with non-trivial subtyping relation:

.. rocqtop:: all

   Polymorphic Cumulative Record packType := {pk : Type}.
   About packType.

:g:`packType` binds a covariant universe, i.e.

.. math::

   E[Γ] ⊢ \mathsf{packType}@\{i\} =_{βδιζη}
   \mathsf{packType}@\{j\}~\mbox{ whenever }~i ≤ j

Looking back at the example of monoids, we can see that they are naturally
covariant for cumulativity:

.. rocqtop:: in

   Set Universe Polymorphism.

   Cumulative Record Monoid := {
     mon_car :> Type;
     mon_unit : mon_car;
     mon_op : mon_car -> mon_car -> mon_car }.

.. rocqtop:: all

   Set Printing Universes.
   Print Monoid.

This means that a monoid in a lower universe (like the unit monoid in set), can
be seen as a monoid in any higher universe, without introducing explicit lifting.

.. rocqtop:: in

   Definition unit_monoid : Monoid@{Set} :=
     {| mon_car := unit; mon_unit := tt; mon_op x y := tt |}.

.. rocqtop:: all

   Monomorphic Universe i.

   Check unit_monoid : Monoid@{i}.

Finally, invariant universes appear when there is no possible subtyping relation
between different instances of the inductive. Consider:

.. rocqtop:: in

   Polymorphic Cumulative Record monad@{i} := {
      m : Type@{i} -> Type@{i};
      unit : forall (A : Type@{i}), A -> m A }.

.. rocqtop:: all

   Set Printing Universes.
   Print monad.

The universe of :g:`monad` is invariant due to its use on the left side of an arrow in
the :g:`m` field: one cannot lift or lower the level of the type constructor to build a
monad in a higher or lower universe.

Specifying cumulativity
~~~~~~~~~~~~~~~~~~~~~~~

The variance of the universe parameters for a cumulative inductive may be specified by the user.

For the following type, universe ``a`` has its variance automatically
inferred (it is irrelevant), ``b`` is required to be irrelevant,
``c`` is covariant and ``d`` is invariant. With these annotations
``c`` and ``d`` have less general variances than would be inferred.

.. rocqtop:: all

   Polymorphic Cumulative Inductive Dummy@{a *b +c =d} : Prop := dummy.
   About Dummy.

Insufficiently restrictive variance annotations lead to errors:

.. rocqtop:: all

   Fail Polymorphic Cumulative Record bad@{*a} := {p : Type@{a}}.

.. example:: Demonstration of universe variances

   .. rocqtop:: in

      Set Printing Universes.
      Set Universe Polymorphism.
      Set Polymorphic Inductive Cumulativity.

      Inductive Invariant @{=u} : Type@{u}.
      Inductive Covariant @{+u} : Type@{u}.
      Inductive Irrelevant@{*u} : Type@{u}.

      Section Universes.
        Universe low high.
        Constraint low < high.

        (* An invariant universe blocks cumulativity from upper or lower levels. *)
        Axiom inv_low  : Invariant@{low}.
        Axiom inv_high : Invariant@{high}.
   .. rocqtop:: all

        Fail Check (inv_low : Invariant@{high}).
        Fail Check (inv_high : Invariant@{low}).
   .. rocqtop:: in

        (* A covariant universe allows cumulativity from a lower level. *)
        Axiom co_low  : Covariant@{low}.
        Axiom co_high : Covariant@{high}.
   .. rocqtop:: all

        Check (co_low : Covariant@{high}).
        Fail Check (co_high : Covariant@{low}).
   .. rocqtop:: in

        (* An irrelevant universe allows cumulativity from any level *)
        Axiom irr_low  : Irrelevant@{low}.
        Axiom irr_high : Irrelevant@{high}.
   .. rocqtop:: all

        Check (irr_low : Irrelevant@{high}).
        Check (irr_high : Irrelevant@{low}).
   .. rocqtop:: in

      End Universes.

.. example:: A proof using cumulativity

   .. rocqtop:: in reset

      Set Universe Polymorphism.
      Set Polymorphic Inductive Cumulativity.
      Set Printing Universes.

      Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := eq_refl : eq x x.

   .. rocqtop:: all

      Print eq.

   The universe of :g:`eq` is irrelevant here, hence proofs of equalities can
   inhabit any universe.  The universe must be big enough to fit `A`.

   .. rocqtop:: in

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Cumulativity Weak Constraints

   When set, which is the default, this :term:`flag` causes "weak" constraints to be produced
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

Each universe is declared in a global or local context before it
can be used. To ensure compatibility, every *global* universe is set
to be strictly greater than :g:`Set` when it is introduced, while every
*local* (i.e. polymorphically quantified) universe is introduced as
greater or equal to :g:`Set`.


Conversion and unification
---------------------------

The semantics of conversion and unification have to be modified a
little to account for the new universe instance arguments to
polymorphic references. The semantics respect the fact that
definitions are transparent, so indistinguishable from their :term:`bodies <body>`
during conversion.

This is accomplished by changing one rule of unification, the first-
order approximation rule, which applies when two applicative terms
with the same head are compared. It tries to short-cut unfolding by
comparing the arguments directly. In case the :term:`constant` is universe
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
polymorphic :term:`constant` :g:`f`, if an argument has expected type :g:`Type@{i}`
and is given a term of type :g:`Type@{j}`, a :math:`j ≤ i` constraint will be
generated. It is however often the case that an equation :math:`j = i` would
be more appropriate, when :g:`f`\'s universes are fresh for example.
Consider the following example:

.. rocqtop:: none

   Polymorphic Definition pidentity {A : Type} (a : A) := a.

.. rocqtop:: in

   Definition id0 := @pidentity nat 0.

.. rocqtop:: all

   Set Printing Universes.
   Print id0.

This definition is elaborated by minimizing the universe of :g:`id0` to
level :g:`Set` while the more general definition would keep the fresh level
:g:`i` generated at the application of :g:`id` and a constraint that :g:`Set` :math:`≤ i`.
This minimization process is applied only to fresh universe variables.
It simply adds an equation between the variable and its lower bound if
it is an atomic universe (i.e. not an algebraic max() universe).

.. flag:: Universe Minimization ToSet

   Turning this :term:`flag` off (it is on by default) disallows minimization
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
   univ_annot ::= @%{ {* @univ_level_or_quality } {? %| {* @univ_level_or_quality } } %}
   univ_level_or_quality ::= Set
   | SProp
   | Prop
   | Type
   | _
   | @qualid
   univ_decl ::= @%{ {? {* @ident } %| } {* @ident } {? + } {? %| {*, @univ_constraint } {? + } } %}
   cumul_univ_decl ::= @%{ {? {* @ident } %| } {* {? {| + | = | * } } @ident } {? + } {? %| {*, @univ_constraint } {? + } } %}
   univ_constraint ::= @universe_name {| < | = | <= } @universe_name

The syntax has been extended to allow users to explicitly bind names
to universes and explicitly instantiate polymorphic definitions.

.. cmd:: Universe {+ @ident }
         Universes {+ @ident }

   In the monomorphic case, declares new global universes
   with the given names.  Global universe names live in a separate namespace.
   The command supports the :attr:`universes(polymorphic)` attribute (or
   the ``Polymorphic`` legacy attribute) only in sections, meaning the universe
   quantification will be discharged for each section definition
   independently.

   .. exn:: Polymorphic universes can only be declared inside sections, use Monomorphic Universe instead.
      :undocumented:

.. cmd:: Constraint {+, @univ_constraint }

   Declares new constraints between named universes.

   If consistent, the constraints are then enforced in the global
   environment. Like :cmd:`Universe`, it can be used with the
   :attr:`universes(polymorphic)` attribute (or the ``Polymorphic``
   legacy attribute) in sections only to declare constraints discharged at
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

   Turn this :term:`flag` on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard flag, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. cmd:: Print {? Sorted } Universes {? Subgraph ( {* @debug_univ_name } ) } {? {| With | Without } Constraint Sources } {? @string }
   :name: Print Universes

   .. insertprodn debug_univ_name debug_univ_name

   .. prodn::
      debug_univ_name ::= @qualid
      | @string

   This command can be used to print the constraints on the internal level
   of the occurrences of :math:`\Type` (see :ref:`Sorts`).

   The :n:`Subgraph` clause limits the printed graph to the requested
   names (adjusting constraints to preserve the implied transitive
   constraints between kept universes). :n:`@debug_univ_name` is
   `:n:`@qualid` for named universes (e.g. `eq.u0`), and :n:`@string`
   for raw universe expressions (e.g. `"Stdlib.Init.Logic.1"`).

   By default when printing a subgraph `Print Universes` attempts to
   find and print the source of the constraints. This can be
   controlled by providing `With Constraint Sources` or `Without
   Constraint Sources`.

   .. rocqtop:: in

      Monomorphic Universes a b c.
      Monomorphic Definition make_a_le_b (F:Type@{b} -> Prop) (X:Type@{a}) := F X.
      Monomorphic Definition make_b_le_c (F:Type@{c} -> Prop) (X:Type@{b}) := F X.
      Monomorphic Definition make_c_le_a (F:Type@{a} -> Prop) (X:Type@{c}) := F X.

   .. rocqtop:: all

      Print Universes Subgraph (a c).

   .. coqrst gets confused if we use a < c as it thinks there's a prompt
      this isn't a problem with a = c (for some reason it's
      also not a problem with the implicit Set < a)

   .. note::

      The integer in raw universe expressions is extremely unstable,
      so raw universe expressions should not be used outside debugging sessions.

   The :n:`Sorted` clause makes each universe
   equivalent to a numbered label reflecting its level (with a linear
   ordering) in the universe hierarchy.

   :n:`@string` is an optional output filename.
   If :n:`@string` ends in ``.dot`` or ``.gv``, the constraints are printed in the DOT
   language, and can be processed by Graphviz tools. The format is
   unspecified if `string` doesn’t end in ``.dot`` or ``.gv``.
   If :n:`@string` is a relative filename, it refers to the directory
   specified by the command line option `-output-directory`, if set
   (see :ref:`command-line-options`) and otherwise, the current
   directory. Use :cmd:`Pwd` to display the current directory.

Polymorphic definitions
~~~~~~~~~~~~~~~~~~~~~~~

For polymorphic definitions, the declaration of (all) universe levels
introduced by a definition uses the following syntax:

.. rocqtop:: in

   Polymorphic Definition le@{i j} (A : Type@{i}) : Type@{j} := A.

.. rocqtop:: all

   Print le.

During refinement we find that :g:`j` must be larger or equal than :g:`i`, as we
are using :g:`A : Type@{i} <= Type@{j}`, hence the generated constraint. At the
end of a definition or proof, we check that the only remaining
universes are the ones declared. In the term and in general in proof
mode, introduced universe names can be referred to in terms. Note that
local universe names shadow global universe names. During a proof, one
can use :cmd:`Show Universes` to display the current context of universes.

It is possible to provide only some universe levels and let Rocq infer the others
by adding a :g:`+` in the list of bound universe levels:

.. rocqtop:: all

   Fail Definition foobar@{u} : Type@{u} := Type.
   Definition foobar@{u +} : Type@{u} := Type.
   Set Printing Universes.
   Print foobar.

This can be used to find which universes need to be explicitly bound in a given
definition.

Definitions can also be instantiated explicitly, giving their full
instance:

.. rocqtop:: all

   Check (pidentity@{Set}).
   Monomorphic Universes k l.
   Check (le@{k l}).

User-named universes and the anonymous universe implicitly attached to
an explicit :g:`Type` are considered rigid for unification and are never
minimized. Flexible anonymous universes can be produced with an
underscore or by omitting the annotation to a polymorphic definition.

.. rocqtop:: all

   Check (fun x => x) : Type -> Type.
   Check (fun x => x) : Type -> Type@{_}.

   Check le@{k _}.
   Check le.

.. flag:: Strict Universe Declaration

   Turning this :term:`flag` off allows one to freely use
   identifiers for universes without declaring them first, with the
   semantics that the first use declares it. In this mode, the universe
   names are not associated with the definition or proof once it has been
   defined. This is meant mainly for debugging purposes.

.. flag:: Private Polymorphic Universes

   This :term:`flag`, on by default, removes universes which appear only in
   the :term:`body` of an opaque polymorphic definition from the definition's
   universe arguments. As such, no value needs to be provided for
   these universes when instantiating the definition. Universe
   constraints are automatically adjusted.

   Consider the following definition:

   .. rocqtop:: in

      Lemma foo@{i} : Type@{i}.
      Proof. exact Type. Qed.

   .. rocqtop:: all

      Print foo.

   The universe :g:`Top.xxx` for the :g:`Type` in the :term:`body` cannot be accessed, we
   only care that one exists for any instantiation of the universes
   appearing in the type of :g:`foo`. This is guaranteed when the
   transitive constraint ``Set <= Top.xxx < i`` is verified. Then when
   using the :term:`constant` we don't need to put a value for the inner
   universe:

   .. rocqtop:: all

      Check foo@{_}.

   and when not looking at the :term:`body` we don't mention the private
   universe:

   .. rocqtop:: all

      About foo.

   To recover the same behavior with regard to universes as
   :g:`Defined`, the :flag:`Private Polymorphic Universes` flag may
   be unset:

   .. rocqtop:: in

      Unset Private Polymorphic Universes.

      Lemma bar : Type. Proof. exact Type. Qed.

   .. rocqtop:: all

      About bar.
      Fail Check bar@{_}.
      Check bar@{_ _}.

   Note that named universes are always public.

   .. rocqtop:: in

      Set Private Polymorphic Universes.
      Unset Strict Universe Declaration.

      Lemma baz : Type@{outer}. Proof. exact Type@{inner}. Qed.

   .. rocqtop:: all

      About baz.

.. _sort-polymorphism:

Sort polymorphism
-----------------

Quantifying over universes does not allow instantiation with `Prop` or `SProp`. For instance

.. rocqtop:: in reset

   Polymorphic Definition type@{u} := Type@{u}.

.. rocqtop:: all

   Fail Check type@{Prop}.

To be able to instantiate a sort with `Prop` or `SProp`, we must
quantify over :gdef:`sort qualities`. Definitions which quantify over
sort qualities are called :gdef:`sort polymorphic`.

All sort quality variables must be explicitly bound.

.. rocqtop:: all

   Polymorphic Definition sort@{s | u |} := Type@{s|u}.

To help the parser, both `|` in the :n:`@univ_decl` are required.

Sort quality variables of a sort polymorphic definition may be
instantiated by the concrete values `SProp`, `Prop` and `Type` or by a
bound variable.

Instantiating `s` in `Type@{s|u}` with the impredicative `Prop` or
`SProp` produces `Prop` or `SProp` respectively regardless of the
instantiation fof `u`.

.. rocqtop:: all

   Eval cbv in sort@{Prop|Set}.
   Eval cbv in sort@{Type|Set}.

When no explicit instantiation is provided or `_` is used, a temporary
variable is generated. Temporary sort variables are instantiated with
`Type` if not unified with another quality when universe minimization
runs (typically at the end of a definition).

:cmd:`Check` and :cmd:`Eval` run minimization so we cannot use them to
witness these temporary variables.

.. rocqtop:: in

   Goal True.
   Set Printing Universes.

.. rocqtop:: all abort

   let c := constr:(sort) in idtac c.

.. note::

   We recommend you do not name explicitly quantified sort variables
   `α` followed by a number as printing will not distinguish between
   your bound variables and temporary variables.

Sort polymorphic inductives may be declared when every instantiation
is valid.

Elimination at a given universe instance requires that elimination is
allowed at every ground instantiation of the sort variables in the
instance. Additionally if the output sort at the given universe
instance is sort polymorphic, the return type of the elimination must
be at the same quality. These restrictions ignore :flag:`Definitional
UIP`.

For instance

.. rocqtop:: all reset

   Set Universe Polymorphism.

   Inductive Squash@{s|u|} (A:Type@{s|u}) : Prop := squash (_:A).

Elimination to `Prop` and `SProp` is always allowed, so `Squash_ind`
and `Squash_sind` are automatically defined.

Elimination to `Type` is not allowed with variable `s`, because the
instantiation `s := Type` does not allow elimination to `Type`.

However elimination to `Type` or to a polymorphic sort with `s := Prop` is allowed:

.. rocqtop:: all

   Definition Squash_Prop_rect A (P:Squash@{Prop|_} A -> Type)
     (H:forall x, P (squash _ x))
     : forall s, P s
     := fun s => match s with squash _ x => H x end.

   Definition Squash_Prop_srect@{s|u +|} A (P:Squash@{Prop|_} A -> Type@{s|u})
     (H:forall x, P (squash _ x))
     : forall s, P s
     := fun s => match s with squash _ x => H x end.

.. note::

   Since inductive types with sort polymorphic output may only be
   polymorphically eliminated to the same sort quality, containers
   such as sigma types may be better defined as primitive records (which
   do not have this restriction) when possible.

   .. rocqtop:: all

      Set Primitive Projections.
      Record sigma@{s|u v|} (A:Type@{s|u}) (B:A -> Type@{s|v})
        : Type@{s|max(u,v)}
        := pair { pr1 : A; pr2 : B pr1 }.

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
the *same* global universes associated with the variable.

It is possible to mix universe polymorphism and monomorphism in
sections, except in the following ways:

- no monomorphic constraint may refer to a polymorphic universe:

  .. rocqtop:: all reset

     Section Foo.

       Polymorphic Universe i.
       Fail Constraint i = i.

  This includes constraints implicitly declared by commands such as
  :cmd:`Variable`, which may need to be used with universe
  polymorphism activated (locally by attribute or globally by option):

  .. rocqtop:: all

     Fail Variable A : (Type@{i} : Type).
     Polymorphic Variable A : (Type@{i} : Type).

  (in the above example the anonymous :g:`Type` constrains polymorphic
  universe :g:`i` to be strictly smaller.)

- no monomorphic :term:`constant` or inductive may be declared if polymorphic
  universes or universe constraints are present.

These restrictions are required in order to produce a sensible result
when closing the section (the requirement on :term:`constants <constant>` and inductive types
is stricter than the one on constraints, because constants and
inductives are abstracted by *all* the section's polymorphic universes
and constraints).
