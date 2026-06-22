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

   E[Γ] ⊢ \mathsf{packType}@\{i\} ≤_{βδιζη}
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

.. insertprodn universe_name sort_constraint

.. prodn::
   universe_name ::= @qualid
   | Set
   | Prop
   univ_annot ::= @%{ {* @univ_level_or_quality } {? {| %| | ; } {* @univ_level_or_quality } } %}
   univ_level_or_quality ::= 0
   | Set
   | SProp
   | Prop
   | Type
   | _
   | @qualid
   sort_quality_var ::= Prop
   | SProp
   | Type
   | @qualid
   univ_decl ::= @%{ {? {* @ident } {| %| | ; } } {* @ident } {? + } {? %| {*, @sort_constraint } {? + } } %}
   cumul_univ_decl ::= @%{ {? {* @ident } {| %| | ; } } {* {? {| + | = | * } } @ident } {? + } {? %| {*, @sort_constraint } {? + } } %}
   sort_constraint ::= @universe_name {| < | = | <= } @universe_name
   | @sort_quality_var -> @sort_quality_var

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

.. cmd:: Constraint {+, @sort_constraint }

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
~~~~~~~~~~~~~~~~~~

.. flag:: Printing Universes

   Turn this :term:`flag` on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard flag, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. flag:: Printing Sorts

   Turn this :term:`flag` on to display sort variables that are otherwise
   hidden, with universe level variables replaced by ``_``.  Sorts without
   sort variables (:g:`Type`, :g:`SProp`, :g:`Prop`, :g:`Set`) are printed
   as usual, while sorts at a sort variable are printed like ``Type@{s;_}``
   (or ``Type@{_}`` when :flag:`Printing Sort Qualities` is off).  Universe
   instances of polymorphic references are displayed when they contain sort
   qualities (with ``_`` in place of the universe levels) and stay hidden
   otherwise.  Compared to :flag:`Printing Universes`, this makes the sort
   structure visible without exposing internal universe level names.

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
   :n:`@qualid` for named universes (e.g. `eq.u0`), and :n:`@string`
   for raw universe expressions (e.g. `"Corelib.Init.Logic.1"`).

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
   semantics that the first use declares it. This is meant mainly for debugging purposes.

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

.. rocqtop:: all

   Polymorphic Definition sort@{s ; u} := Type@{s;u}.

.. note::

   The following deprecated syntax is equivalent:

   .. rocqtop:: all warn

      Polymorphic Definition sort'@{s | u |} := Type@{s|u}.

   To help the parser, both `|` in the :n:`@univ_decl` are required.

Sort quality variables of a sort polymorphic definition may be
instantiated by the concrete values `SProp`, `Prop` and `Type` or by a
bound variable.

Instantiating `s` in `Type@{s;u}` with the impredicative `Prop` or
`SProp` produces `Prop` or `SProp` respectively regardless of the
instantiation of `u`.

.. rocqtop:: all

   Eval cbv in sort@{Prop;Set}.
   Eval cbv in sort@{Type;Set}.

When no explicit instantiation is provided or `_` is used, a temporary
variable is generated. Temporary sort variables are instantiated with
`Type` if not unified with another quality when universe minimization
runs (typically at the end of a definition).

:cmd:`Check` and :cmd:`Eval` run minimization so we cannot use them to
witness these temporary variables.

.. rocqtop:: in

   Goal True.
   Proof.
   Set Printing Universes.

.. rocqtop:: all abort

   let c := constr:(sort) in idtac c.

.. note::

   We recommend you do not name explicitly quantified sort variables
   `α` followed by a number as printing will not distinguish between
   your bound variables and temporary variables.

Sort polymorphic inductives may be declared when every instantiation
is valid.

.. flag:: Collapse Sorts ToType

   When set, unbound sort variables are collapsed to `Type` during minimization of universes.
   Unsetting this flag will preserve sort variables during implicit elaboration of sort-polymorphic terms,
   if :flag:`Universe Polymorphism` is set.
   The flag is set by default.

   For instance, defining the `list` type, without explicit sorts, should elaborate two implicit ones:
   One for the type of parameter `A`, and one for the `list` type itself.

   .. rocqtop:: all

      Unset Collapse Sorts ToType.

      Inductive list (A : Type) : Type :=
      | nil : list A
      | cons : A -> list A -> list A.

      Set Printing Universes.
      About list.

      Set Collapse Sorts ToType.

   .. note::

      A constraint `Prop <= q` or `q <= Type` implies that `q = Prop`
      or `q = Type` (with either assignment satisfying both constraints since `Prop <= Type`).
      The choice of assignment can be delayed during :term:`type inference`
      but sort variables with such constraints must still get assigned to Prop or Type
      before the kernel can operate.

      If there is only a constraint `Prop <= q` then `q` will be set
      to Prop, otherwise it will be set to Type.

.. _elim-constraints:

Elimination of Sort-Polymorphic Inductives
------------------------------------------

Sort-polymorphic inductives follow rules for their elimination, both
when the target sort is polymorphic or not. We illustrate the first case
on the following example:

.. rocqtop:: all reset

   Set Universe Polymorphism.

   Inductive Squash@{s;u} (A:Type@{s;u}) : Prop := squash (_:A).

Here, elimination to `Prop` and `SProp` is always allowed, so `Squash_ind`
and `Squash_sind` are automatically defined.

Elimination to `Type` is not allowed with variable `s`, because the
instantiation `s := Type` does not allow elimination to `Type`.

However elimination to `Type` or to a polymorphic sort with `s := Prop` is allowed:

.. rocqtop:: all

   Definition Squash_Prop_rect A (P:Squash@{Prop;_} A -> Type)
     (H:forall x, P (squash _ x))
     : forall s, P s
     := fun s => match s with squash _ x => H x end.

   Definition Squash_Prop_srect@{s;u +} A (P:Squash@{Prop;_} A -> Type@{s;u})
     (H:forall x, P (squash _ x))
     : forall s, P s
     := fun s => match s with squash _ x => H x end.

In fact, for a given universe instance, elimination is allowed if:

- it is allowed for every ground instantiation of the sort variables in the instance, or

- the output sort at the given universe instance is sort polymorphic and
  the return type of the elimination is at the same quality.

For instance, for the following inductive, elimination is not allowed unless the target sort of
the inductive matches the sort it is eliminated to.

.. rocqtop:: all

   Inductive sum@{sl sr s;ul ur} (A:Type@{sl;ul}) (B:Type@{sr;ur}) : Type@{s;max(ul,ur)} :=
   | inl (_:A)
   | inr (_:B).

.. rocqtop:: none

   Arguments inl {_ _} _.
   Arguments inr {_ _} _.

.. rocqtop:: all

   Fail Definition sum_elim@{sl sr s s';ul ur u'|}
     (A:Type@{sl;ul}) (B:Type@{sr;ur}) (P:sum@{sl sr s;ul ur} A B -> Type@{s';u'})
     (fl : forall (x : A), P (inl x)) (fr : forall (y : B), P (inr y))
     (v : sum@{sl sr s;ul ur} A B) : P v :=
         match v with
         | inl x => fl x
         | inr y => fr y
         end.

As this greatly inhibits the possibilities of sort polymorphism, we have introduced *elimination
constraints* to manage these cases. Here, the annotation `s -> s'` can be added
to tell Rocq that the definition is allowed for *every* sorts `s`, `s'` such that `s` eliminates
into `s'`.

.. rocqtop:: all

   Definition sum_elim@{sl sr s s';ul ur u'|s -> s'}
     (A:Type@{sl;ul}) (B:Type@{sr;ur}) (P:sum@{sl sr s;ul ur} A B -> Type@{s';u'})
     (fl : forall (x : A), P (inl x)) (fr : forall (y : B), P (inr y))
     (v : sum@{sl sr s;ul ur} A B) : P v :=
         match v with
         | inl x => fl x
         | inr y => fr y
         end.

It means that `s` and `s'` can respectively be instantiated to e.g., `Type` and `Prop` or
`Prop` and `SProp`, but cannot be instantiated to e.g., `Prop` and `Type` or `SProp` and
`Prop`.

.. rocqtop:: all

   Check sum_elim@{_ _ Type Prop;_ _ _}.
   Check sum_elim@{_ _ Prop SProp;_ _ _}.
   Fail Check sum_elim@{_ _ Prop Type;_ _ _}.
   Fail Check sum_elim@{_ _ SProp Prop;_ _ _}.

.. note::

   As with universe level constraints, elimination constraints can be elaborated
   automatically if the constraints are denoted extensible with `+` **or** if they
   are totally omitted. In addition, when unsetting :flag:`Collapse Sorts ToType`,
   the definition may be left completely implicit, elaborating both sort variables and
   elimination constraints.
   For instance, the three following definitions are legal.

   .. rocqtop:: all

      Definition sum_elim_ext@{sl sr s s';ul ur u'|+}
        (A:Type@{sl;ul}) (B:Type@{sr;ur}) (P:sum@{sl sr s;ul ur} A B -> Type@{s';u'})
        (fl : forall (x : A), P (inl x)) (fr : forall (y : B), P (inr y))
        (v : sum@{sl sr s;ul ur} A B) : P v :=
            match v with
                | inl x => fl x
                | inr y => fr y
                end.

      Definition sum_elim_elab@{sl sr s s';ul ur u'}
        (A:Type@{sl;ul}) (B:Type@{sr;ur}) (P:sum@{sl sr s;ul ur} A B -> Type@{s';u'})
        (fl : forall (x : A), P (inl x)) (fr : forall (y : B), P (inr y))
        (v : sum@{sl sr s;ul ur} A B) : P v :=
            match v with
                | inl x => fl x
                | inr y => fr y
                end.

      Unset Collapse Sorts ToType.

      Definition sum_elim_implicit (A B : Type) (P : sum A B -> Type)
        (fl : forall (x : A), P (inl x)) (fr : forall (y : B), P (inr y))
        (v : sum A B) : P v :=
            match v with
                | inl x => fl x
                | inr y => fr y
                end.

.. note::

    These restrictions ignore :flag:`Definitional UIP`.

.. flag:: Printing Sort Qualities

   By default when :flag:`Printing Universes` is on, sorts at floating
   sort qualities will print their quality. Turning this :term:`flag` off will
   instead print them as though the quality was `Type` (which it will
   become at the end of the definition unless it is unified with
   another rigid quality).

Explicit Sorts
---------------

Similar to universes, fresh global sorts can be declared with the :cmd:`Sort`, and elimination
constraint on global sorts can be declared with the :cmd:`Constraint`.

.. cmd:: Sort {+ @ident }
         Sorts {+ @ident }

   In the monomorphic case, declares new global sort qualities
   with the given names.  Global quality names live in their own namespace.
   Inside sections, the command respects the `Universe Polymorphism` flag,
   either set globally or locally through the :attr:`universes(polymorphic)` attribute (or
   the ``Polymorphic`` legacy attribute), meaning the sort
   quantification will be discharged for each section definition
   independently. Polymorphic sort qualities are forbidden outside sections.

  .. exn:: Polymorphic sorts can only be declared inside sections, use #[universe(polymorphic=no)] Sort in order to declare a global sort.

    Generated when a :cmd:`Sort` command is issued outside a section with universe polymorphism set.
    Either scope the :cmd:`Sort` with an enclosing :cmd:`Section` or be explicit about creating a global sort
    by turning universe polymorphism off.

  .. exn:: Cannot declare global sort qualities inside module types.

    The :cmd:`Sort` command is not supported inside module types.

.. cmd:: Print Sorts

   Print the list of global named sorts in the current global environment. Use :cmd:`Show Universes` to print sort variables local to a proof context.

  .. rocqtop:: all

    Set Universe Polymorphism.

    (* A global sort named g. *)
    #[universes(polymorphic=no)]
    Sort g.

    Print Sorts.

    (* Universe of g-sorted type. *)
    Definition G@{l|} : Type@{l+1} := Type@{g;l}.

    Section LocalSorts.
      Sort u v w.

      Definition arr2@{l|} (A : Type@{u;l}) (B : Type@{v;l}) (C : Type@{w;l}) : Type@{w;l} :=
        A -> B -> C.

      Print Sorts.

      Sort x y.

      Definition arr1@{l|} (X : Type@{x;l}) (Y : Type@{y;l}) : Type@{y;l} :=
        X -> Y.

      Print Sorts.

    End LocalSorts.

    (* The sorts u, v, w, x and y are no longer present. *)
    Print Sorts.

    (* Equivalent definition of arr2 outside the section LocalSorts. *)
    Definition arr2'@{u v w ; l |} (A : Type@{u;l}) (B : Type@{v;l}) (C : Type@{w;l}) : Type@{w;l} :=
        A -> B -> C.

    (* All sort declarations of the section are bound, even the unused one. *)
    About arr1.

.. _Template-polymorphism:

Template polymorphism
---------------------

Template polymorphism is a variant of universe polymorphism for
inductive types (and inductive families) whose shape allows inferring
the universe instance from the parameters. Template polymorphic
inductives appear in terms without an explicit universe instance (for
instance if `prod` is template polymorphic then `prod nat nat` is a
fully explicit term, if it is universe polymorphic it would be
`prod@{Set Set} nat nat`).

Additionally template polymorphism implements sort polymorphism
restricted to the sorts `Prop` and `Type`
(for instance `prod True True : Prop`).

Template polymorphic inductive declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A template polymorphic inductive is polymorphic over some specific
universe levels and sort variables which are introduced by the inductive's declaration.
These levels are called "template (polymorphic) levels" and sorts.

A type of the shape `Type@{s;u}` or `forall ..., Type@{s;u}` (i.e. a
type of types or type families) is called an "arity". `Type@{s;u}` is
the "conclusion" of the arity. The type of an inductive is always an
arity, and for short we say "the inductive's conclusion" instead of
"the inductive's type's conclusion". Template polymorphism also
involves parameters of the inductive whose types are arities.

An inductive may be template polymorphic when

- it is the only inductive of its block (the combination of template
  polymorphism and mutual inductives is not supported).

- the template levels appear linearly in the conclusions of parameters
  which are arities. Such conclusions must have only that level as its universe
  (i.e. `Type@{s;u}` where `u` is a template level, not `Type@{s;max(u,v)}` or `Type@{u+1}`).
  Each template level is said to be "bound" by the parameter in whose type it appears.

- the template levels may also appear in the inductive's conclusion,
  and appear nowhere else (not in non-arity parameters, not in
  the domains of arity parameters, not in the indices, and not
  in the constructor arguments and return types).

- template levels which appear in the inductive's conclusion do
  not appear with an increment (i.e. if `u` is a template level it
  does not appear as `u+1`).

  This restriction prevents generating increments higher than 1 by
  applying template inductives to themselves, i.e. if `I : Type@{u} ->
  Type@{u + 1}` was template polymorphic and `X:Type@{i}` then `I
  (I X) : Type@{i + 2}`. It is necessary as the current universe
  checking cannot handle such increments properly, but this
  restriction may be removed in the future.

- the template sorts appear in the conclusions of parameters (not
  necessarily linearly), may appear in the inductive's conclusion, and
  appear nowhere else.

- for each template universe `u`, there are no constraints of the form
  `v <= u` ("no constraints from below").

These requirements are more than sufficient to ensure that if the
inductive was declared universe polymorphic and cumulative then all
template levels would be irrelevant. The "no constraints from below"
requirement is needed for subject reduction (preservation of typing by
reduction) in terms involving partially applied template polymorphic
inductives. Linearity of template universes and not supporting mutual
inductives make implementation of template polymorphism easier.

.. warning::

   The restriction that universes are introduced by the inductive
   declaration prevents inductive types declared in sections from being
   template-polymorphic on universes introduced previously in the
   section: they cannot parameterize over the universes introduced with
   section variables that become parameters at section closing time, as
   these may be shared with other definitions from the same section
   which can impose constraints on them.

.. note::

   Currently user syntax does not support explicit sort polymorphism
   annotations (`@{s;...}`) in template polymorphic declarations. The
   sorts must be left implicit and will be automatically inferred.

.. example::

   .. rocqtop:: in reset

      Inductive option (A:Type) : Type :=
      | None : option A
      | Some : A -> option A.

      Inductive prod A B := pair : A -> B -> prod A B.

   .. rocqtop:: all

      Set Printing Universes.
      About option.
      About prod.

   Since the sort polymorphism of template inductives cannot be
   specified in the user syntax, it is instead described by the
   "can/cannot be instantiated to `Prop`" mention in :cmd:`About`'s
   output. Since `option` has 2 constructors, it cannot be
   instantiated to `Prop` i.e. it is not sort polymorphic.

Using template polymorphic inductives
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For each template universe `u` bound by parameter `A` of an inductive
`I`, when `I` is applied such that `A` is instantiated with a term of
type `forall ..., Type@{q;i}` (where `i` may be an algebraic
universe), `u` is instantiated by `i` in the inductive's conclusion
and in the constraints (which must be of the form `u <= x` where `x`
is a global universe due to the "no constraints from below"
requirement).

Each template sort `s` is instantiated by the supremum of the `q`
appearing in the conclusions of the types of arguments provided for
parameters binding `s`. This is well-defined because template sorts
may only be instantiated by `Prop` and `Type` and variable sorts
restricted to these 2 ground sorts.

If the inductive is partially applied, leftover parameters act as
though they were given an argument at a default global universe and at
sort `Type`.

.. warning::

   Partially applied template polymorphic inductives lead to
   constraints between global universes, which can cause complex universe inconsistencies.

.. example::

   As mentioned previously, `option` is not sort polymorphic:

   .. rocqtop:: all

      Check fun A:Prop => option A.

   but it is universe polymorphic:

   .. rocqtop:: all

      Check fun A:Set => option A.
      Check option Set.

.. example::

   `prod` is sort polymorphic, but restricted to `Prop` and `Type`:

   .. rocqtop:: all

      Check fun A:Prop => prod A A.
      Fail Check fun A:SProp =>  prod A A.

   When only one of the arguments is `Prop`, the supremum of the sorts is `Type`:

   .. rocqtop:: all

      Check prod True nat.

   This is also the case when partially applied to a `Prop`, and we
   can see the use of the default universe `prod.u1` for the second
   parameter:

   .. rocqtop:: all

      Check prod True.

Controlling template polymorphism
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Auto Template Polymorphism

   This :term:`flag`, enabled by default, makes every inductive type declared
   at level `Type` (without an explicit universe instance or hiding it behind a
   definition) template polymorphic if possible.

   This can be prevented using the :attr:`universes(template=no) <universes(template)>`
   attribute.

   Template polymorphism and full universe polymorphism (see Chapter
   :ref:`polymorphicuniverses`) are incompatible, so if the latter is
   enabled (through the :flag:`Universe Polymorphism` flag or the
   :attr:`universes(polymorphic)` attribute) it will prevail over
   automatic template polymorphism.

.. warn:: Automatically declaring @ident as template polymorphic.

   Warning ``auto-template`` can be used (it is off by default) to
   find which types are implicitly declared template polymorphic by
   :flag:`Auto Template Polymorphism`.

   An inductive type can be forced to be template polymorphic using
   the :attr:`universes(template)` attribute: in this case, the
   warning is not emitted.

.. attr:: universes(template{? = {| yes | no } })
   :name: universes(template)

   This :term:`boolean attribute` can be used to explicitly declare an
   inductive type as template polymorphic, whether the :flag:`Auto
   Template Polymorphism` flag is on or off.

   .. exn:: Template-polymorphism and universe polymorphism are not compatible

      This attribute cannot be used in a full universe polymorphic
      context, i.e. if the :flag:`Universe Polymorphism` flag is on or
      if the :attr:`universes(polymorphic)` attribute is used.

   .. warn:: This inductive type has no template universes
      :name: no-template-universe

      The attribute was used but the inductive definition does not
      satisfy the criterion to be template polymorphic.

   When ``universes(template=no)`` is used, it will prevent an
   inductive type from being template polymorphic, even if the :flag:`Auto
   Template Polymorphism` flag is on.

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
