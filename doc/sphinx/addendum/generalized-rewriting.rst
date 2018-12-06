.. _generalizedrewriting:

Generalized rewriting
=====================

:Author: Matthieu Sozeau

This chapter presents the extension of several equality related
tactics to work over user-defined structures (called setoids) that are
equipped with ad-hoc equivalence relations meant to behave as
equalities. Actually, the tactics have also been generalized to
relations weaker then equivalences (e.g. rewriting systems). The
toolbox also extends the automatic rewriting capabilities of the
system, allowing the specification of custom strategies for rewriting.

This documentation is adapted from the previous setoid documentation
by Claudio Sacerdoti Coen (based on previous work by Clément Renard).
The new implementation is a drop-in replacement for the old one
[#tabareau]_, hence most of the documentation still applies.

The work is a complete rewrite of the previous implementation, based
on the typeclass infrastructure. It also improves on and generalizes
the previous implementation in several ways:

+ User-extensible algorithm. The algorithm is separated into two parts:
  generation of the rewriting constraints (written in ML) and solving
  these constraints using typeclass resolution. As typeclass
  resolution is extensible using tactics, this allows users to define
  general ways to solve morphism constraints.
+ Subrelations. An example extension to the base algorithm is the
  ability to define one relation as a subrelation of another so that
  morphism declarations on one relation can be used automatically for
  the other. This is done purely using tactics and typeclass search.
+ Rewriting under binders. It is possible to rewrite under binders in
  the new implementation, if one provides the proper morphisms. Again,
  most of the work is handled in the tactics.
+ First-class morphisms and signatures. Signatures and morphisms are
  ordinary Coq terms, hence they can be manipulated inside Coq, put
  inside structures and lemmas about them can be proved inside the
  system. Higher-order morphisms are also allowed.
+ Performance. The implementation is based on a depth-first search for
  the first solution to a set of constraints which can be as fast as
  linear in the size of the term, and the size of the proof term is
  linear in the size of the original term. Besides, the extensibility
  allows the user to customize the proof search if necessary.

.. [#tabareau] Nicolas Tabareau helped with the gluing.

Introduction to generalized rewriting
-------------------------------------


Relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~

A parametric *relation* ``R`` is any term of type
``forall (x1 : T1) ... (xn : Tn), relation A``.
The expression ``A``, which depends on ``x1 ... xn`` , is called the *carrier*
of the relation and ``R`` is said to be a relation over ``A``; the list
``x1,...,xn`` is the (possibly empty) list of parameters of the relation.

.. example:: Parametric relation

   It is possible to implement finite sets of elements of type ``A`` as
   unordered lists of elements of type ``A``.
   The function ``set_eq: forall (A : Type), relation (list A)``
   satisfied by two lists with the same elements is a parametric relation
   over ``(list A)`` with one parameter ``A``. The type of ``set_eq``
   is convertible with ``forall (A : Type), list A -> list A -> Prop.``

An *instance* of a parametric relation ``R`` with n parameters is any term
``(R t1 ... tn)``.

Let ``R`` be a relation over ``A`` with ``n`` parameters. A term is a parametric
proof of reflexivity for ``R`` if it has type
``forall (x1 : T1) ... (xn : Tn), reflexive (R x1 ... xn)``.
Similar definitions are given for parametric proofs of symmetry and transitivity.

.. example:: Parametric relation (continued)

   The ``set_eq`` relation of the previous example can be proved to be
   reflexive, symmetric and transitive. A parametric unary function ``f`` of type
   ``forall (x1 : T1) ... (xn : Tn), A1 -> A2`` covariantly respects two parametric relation instances
   ``R1`` and ``R2`` if, whenever ``x``, ``y`` satisfy ``R1 x y``, their images (``f x``) and (``f y``)
   satisfy ``R2 (f x) (f y)``. An ``f`` that respects its input and output
   relations will be called a unary covariant *morphism*. We can also say
   that ``f`` is a monotone function with respect to ``R1`` and ``R2`` . The
   sequence ``x1 ... xn`` represents the parameters of the morphism.

Let ``R1`` and ``R2`` be two parametric relations. The *signature* of a
parametric morphism of type ``forall (x1 : T1) ... (xn : Tn), A1 -> A2``
that covariantly respects two instances :math:`I_{R_1}` and :math:`I_{R_2}` of ``R1`` and ``R2``
is written :math:`I_{R_1} ++> I_{R_2}`. Notice that the special arrow ++>, which
reminds the reader of covariance, is placed between the two relation
instances, not between the two carriers. The signature relation
instances and morphism will be typed in a context introducing
variables for the parameters.

The previous definitions are extended straightforwardly to n-ary
morphisms, that are required to be simultaneously monotone on every
argument.

Morphisms can also be contravariant in one or more of their arguments.
A morphism is contravariant on an argument associated to the relation
instance :math:`R` if it is covariant on the same argument when the inverse
relation :math:`R^{−1}` (``inverse R`` in Coq) is considered. The special arrow ``-->``
is used in signatures for contravariant morphisms.

Functions having arguments related by symmetric relations instances
are both covariant and contravariant in those arguments. The special
arrow ``==>`` is used in signatures for morphisms that are both
covariant and contravariant.

An instance of a parametric morphism :math:`f` with :math:`n`
parameters is any term :math:`f \, t_1 \ldots t_n`.

.. example:: Morphisms

   Continuing the previous example, let ``union: forall (A : Type), list A -> list A -> list A``
   perform the union of two sets by appending one list to the other. ``union` is a binary
   morphism parametric over ``A`` that respects the relation instance
   ``(set_eq A)``. The latter condition is proved by showing:

   .. coqtop:: in

     forall (A: Type) (S1 S1' S2 S2': list A),
       set_eq A S1 S1' ->
       set_eq A S2 S2' ->
       set_eq A (union A S1 S2) (union A S1' S2').

   The signature of the function ``union A`` is ``set_eq A ==> set_eq A ==> set_eq A``
   for all ``A``.

.. example:: Contravariant morphisms

   The division function ``Rdiv : R -> R -> R`` is a morphism of signature
   ``le ++> le --> le`` where ``le`` is the usual order relation over
   real numbers. Notice that division is covariant in its first argument
   and contravariant in its second argument.

Leibniz equality is a relation and every function is a morphism that
respects Leibniz equality. Unfortunately, Leibniz equality is not
always the intended equality for a given structure.

In the next section we will describe the commands to register terms as
parametric relations and morphisms. Several tactics that deal with
equality in Coq can also work with the registered relations. The exact
list of tactics will be given :ref:`in this section <tactics-enabled-on-user-provided-relations>`.
For instance, the tactic reflexivity can be used to solve a goal ``R n n`` whenever ``R``
is an instance of a registered reflexive relation. However, the
tactics that replace in a context ``C[]`` one term with another one
related by ``R`` must verify that ``C[]`` is a morphism that respects the
intended relation. Currently the verification consists of checking
whether ``C[]`` is a syntactic composition of morphism instances that respects some obvious
compatibility constraints.

.. example:: Rewriting

   Continuing the previous examples, suppose that the user must prove
   ``set_eq int (union int (union int S1 S2) S2) (f S1 S2)`` under the
   hypothesis ``H : set_eq int S2 (@nil int)``. It
   is possible to use the ``rewrite`` tactic to replace the first two
   occurrences of ``S2`` with ``@nil int`` in the goal since the
   context ``set_eq int (union int (union int S1 nil) nil) (f S1 S2)``,
   being a composition of morphisms instances, is a morphism. However the
   tactic will fail replacing the third occurrence of ``S2``  unless ``f``
   has also been declared as a morphism.


Adding new relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd::  Add Parametric Relation (x1 : T1) ... (xn : Tk) : (A t1 ... tn) (Aeq t′1 ... t′m) {? reflexivity proved by refl} {? symmetry proved by sym} {? transitivity proved by trans} as @ident

   This command declares a parametric relation :g:`Aeq: forall (y1 : β1 ... ym : βm)`,
   :g:`relation (A t1 ... tn)` over :g:`(A : αi -> ... αn -> Type)`.

   The :token:`ident` gives a unique name to the morphism and it is used
   by the command to generate fresh names for automatically provided
   lemmas used internally.

   Notice that the carrier and relation parameters may refer to the
   context of variables introduced at the beginning of the declaration,
   but the instances need not be made only of variables. Also notice that
   ``A`` is *not* required to be a term having the same parameters as ``Aeq``,
   although that is often the case in practice (this departs from the
   previous implementation).

   To use this command, you need to first import the module ``Setoid`` using
   the command ``Require Import Setoid``.

.. cmd:: Add Relation

   In case the carrier and relations are not parametric, one can use this command
   instead, whose syntax is the same except there is no local context.

   The proofs of reflexivity, symmetry and transitivity can be omitted if
   the relation is not an equivalence relation. The proofs must be
   instances of the corresponding relation definitions: e.g. the proof of
   reflexivity must have a type convertible to
   :g:`reflexive (A t1 ... tn) (Aeq t′ 1 …t′ n)`.
   Each proof may refer to the introduced variables as well.

.. example:: Parametric relation

   For Leibniz equality, we may declare:

   .. coqtop:: in

     Add Parametric Relation (A : Type) : A (@eq A)
       [reflexivity proved by @refl_equal A]
     ...

Some tactics (:tacn:`reflexivity`, :tacn:`symmetry`, :tacn:`transitivity`) work only on
relations that respect the expected properties. The remaining tactics
(:tacn:`replace`, :tacn:`rewrite` and derived tactics such as :tacn:`autorewrite`) do not
require any properties over the relation. However, they are able to
replace terms with related ones only in contexts that are syntactic
compositions of parametric morphism instances declared with the
following command.

.. cmd:: Add Parametric Morphism (x1 : T1) ... (xk : Tk) : (f t1 ... tn) with signature sig as @ident

   This command declares ``f`` as a parametric morphism of signature ``sig``. The
   identifier :token:`ident` gives a unique name to the morphism and it is used as
   the base name of the typeclass instance definition and as the name of
   the lemma that proves the well-definedness of the morphism. The
   parameters of the morphism as well as the signature may refer to the
   context of variables. The command asks the user to prove interactively
   that ``f`` respects the relations identified from the signature.

.. example::

   We start the example by assuming a small theory over
   homogeneous sets and we declare set equality as a parametric
   equivalence relation and union of two sets as a parametric morphism.

   .. coqtop:: in

      Require Export Setoid.
      Require Export Relation_Definitions.

      Set Implicit Arguments.

      Parameter set : Type -> Type.
      Parameter empty : forall A, set A.
      Parameter eq_set : forall A, set A -> set A -> Prop.
      Parameter union : forall A, set A -> set A -> set A.

      Axiom eq_set_refl : forall A, reflexive _ (eq_set (A:=A)).
      Axiom eq_set_sym : forall A, symmetric _ (eq_set (A:=A)).
      Axiom eq_set_trans : forall A, transitive _ (eq_set (A:=A)).
      Axiom empty_neutral : forall A (S : set A), eq_set (union S (empty A)) S.

      Axiom union_compat :
        forall (A : Type),
          forall x x' : set A, eq_set x x' ->
          forall y y' : set A, eq_set y y' ->
            eq_set (union x y) (union x' y').

      Add Parametric Relation A : (set A) (@eq_set A)
        reflexivity proved by (eq_set_refl (A:=A))
        symmetry proved by (eq_set_sym (A:=A))
        transitivity proved by (eq_set_trans (A:=A))
        as eq_set_rel.

      Add Parametric Morphism A : (@union A)
        with signature (@eq_set A) ==> (@eq_set A) ==> (@eq_set A) as union_mor.
      Proof.
        exact (@union_compat A).
      Qed.

   It is possible to reduce the burden of specifying parameters using
   (maximally inserted) implicit arguments. If ``A`` is always set as
   maximally implicit in the previous example, one can write:

   .. coqtop:: in

      Add Parametric Relation A : (set A) eq_set
        reflexivity proved by eq_set_refl
        symmetry proved by eq_set_sym
        transitivity proved by eq_set_trans
        as eq_set_rel.

   .. coqtop:: in

      Add Parametric Morphism A : (@union A) with
        signature eq_set ==> eq_set ==> eq_set as union_mor.

   .. coqtop:: in

      Proof. exact (@union_compat A). Qed.

   We proceed now by proving a simple lemma performing a rewrite step and
   then applying reflexivity, as we would do working with Leibniz
   equality. Both tactic applications are accepted since the required
   properties over ``eq_set`` and ``union`` can be established from the two
   declarations above.

   .. coqtop:: in

      Goal forall (S : set nat),
        eq_set (union (union S empty) S) (union S S).

   .. coqtop:: in

      Proof. intros. rewrite empty_neutral. reflexivity. Qed.

   The tables of relations and morphisms are managed by the typeclass
   instance mechanism. The behavior on section close is to generalize the
   instances by the variables of the section (and possibly hypotheses
   used in the proofs of instance declarations) but not to export them in
   the rest of the development for proof search. One can use the
   cmd:`Existing Instance` command to do so outside the section, using the name of the
   declared morphism suffixed by ``_Morphism``, or use the ``Global`` modifier
   for the corresponding class instance declaration
   (see :ref:`First Class Setoids and Morphisms <first-class-setoids-and-morphisms>`) at
   definition time. When loading a compiled file or importing a module,
   all the declarations of this module will be loaded.


Rewriting and non reflexive relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To replace only one argument of an n-ary morphism it is necessary to
prove that all the other arguments are related to themselves by the
respective relation instances.

.. example::

   To replace ``(union S empty)`` with ``S`` in ``(union (union S empty) S) (union S S)``
   the rewrite tactic must exploit the monotony of ``union`` (axiom ``union_compat``
   in the previous example). Applying ``union_compat`` by hand we are left with the
   goal ``eq_set (union S S) (union S S)``.

When the relations associated to some arguments are not reflexive, the
tactic cannot automatically prove the reflexivity goals, that are left
to the user.

Setoids whose relations are partial equivalence relations (PER) are
useful for dealing with partial functions. Let ``R`` be a PER. We say that an
element ``x`` is defined if ``R x x``. A partial function whose domain
comprises all the defined elements is declared as a morphism that
respects ``R``. Every time a rewriting step is performed the user must
prove that the argument of the morphism is defined.

.. example::

   Let ``eqO`` be ``fun x y => x = y /\ x <> 0`` (the
   smallest PER over nonzero elements). Division can be declared as a
   morphism of signature ``eq ==> eq0 ==> eq``. Replacing ``x`` with
   ``y`` in ``div x n = div y n`` opens an additional goal ``eq0 n n``
   which is equivalent to ``n = n /\ n <> 0``.


Rewriting and non symmetric relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When the user works up to relations that are not symmetric, it is no
longer the case that any covariant morphism argument is also
contravariant. As a result it is no longer possible to replace a term
with a related one in every context, since the obtained goal implies
the previous one if and only if the replacement has been performed in
a contravariant position. In a similar way, replacement in an
hypothesis can be performed only if the replaced term occurs in a
covariant position.

.. example:: Covariance and contravariance

   Suppose that division over real numbers has been defined as a morphism of signature
   ``Z.div : Z.lt ++> Z.lt --> Z.lt`` (i.e. ``Z.div`` is increasing in
   its first argument, but decreasing on the second one). Let ``<``
   denote ``Z.lt``. Under the hypothesis ``H : x < y`` we have
   ``k < x / y -> k < x / x``, but not ``k < y / x -> k < x / x``. Dually,
   under the same hypothesis ``k < x / y -> k < y / y`` holds, but
   ``k < y / x -> k < y / y`` does not. Thus, if the current goal is
   ``k < x / x``, it is possible to replace only the second occurrence of
   ``x`` (in contravariant position) with ``y`` since the obtained goal
   must imply the current one. On the contrary, if ``k < x / x`` is an
   hypothesis, it is possible to replace only the first occurrence of
   ``x`` (in covariant position) with ``y`` since the current
   hypothesis must imply the obtained one.

   Contrary to the previous implementation, no specific error message
   will be raised when trying to replace a term that occurs in the wrong
   position. It will only fail because the rewriting constraints are not
   satisfiable. However it is possible to use the at modifier to specify
   which occurrences should be rewritten.

   As expected, composing morphisms together propagates the variance
   annotations by switching the variance every time a contravariant
   position is traversed.

.. example::

   Let us continue the previous example and let us consider
   the goal ``x / (x / x) < k``. The first and third occurrences of
   ``x`` are in a contravariant position, while the second one is in
   covariant position. More in detail, the second occurrence of ``x``
   occurs covariantly in ``(x / x)`` (since division is covariant in
   its first argument), and thus contravariantly in ``x / (x / x)``
   (since division is contravariant in its second argument), and finally
   covariantly in ``x / (x / x) < k`` (since ``<``, as every
   transitive relation, is contravariant in its first argument with
   respect to the relation itself).


Rewriting in ambiguous setoid contexts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One function can respect several different relations and thus it can
be declared as a morphism having multiple signatures.

.. example::

   Union over homogeneous lists can be given all the
   following signatures: ``eq ==> eq ==> eq`` (``eq`` being the
   equality over ordered lists) ``set_eq ==> set_eq ==> set_eq``
   (``set_eq`` being the equality over unordered lists up to duplicates),
   ``multiset_eq ==> multiset_eq ==> multiset_eq`` (``multiset_eq``
   being the equality over unordered lists).

To declare multiple signatures for a morphism, repeat the :cmd:`Add Morphism`
command.

When morphisms have multiple signatures it can be the case that a
rewrite request is ambiguous, since it is unclear what relations
should be used to perform the rewriting. Contrary to the previous
implementation, the tactic will always choose the first possible
solution to the set of constraints generated by a rewrite and will not
try to find *all* the possible solutions to warn the user about them.


Commands and tactics
--------------------


.. _first-class-setoids-and-morphisms:

First class setoids and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



The implementation is based on a first-class representation of
properties of relations and morphisms as typeclasses. That is, the
various combinations of properties on relations and morphisms are
represented as records and instances of theses classes are put in a
hint database. For example, the declaration:

.. coqdoc::

   Add Parametric Relation (x1 : T1) ... (xn : Tn) : (A t1 ... tn) (Aeq t′1 ... t′m)
     [reflexivity proved by refl]
     [symmetry proved by sym]
     [transitivity proved by trans]
     as id.


is equivalent to an instance declaration:

.. coqdoc::

   Instance (x1 : T1) ... (xn : Tn) => id : @Equivalence (A t1 ... tn) (Aeq t′1 ... t′m) :=
     [Equivalence_Reflexive := refl]
     [Equivalence_Symmetric := sym]
     [Equivalence_Transitive := trans].

The declaration itself amounts to the definition of an object of the
record type ``Coq.Classes.RelationClasses.Equivalence`` and a hint added
to the ``typeclass_instances`` hint database. Morphism declarations are
also instances of a typeclass defined in ``Classes.Morphisms``. See the
documentation on :ref:`typeclasses` and the theories files in Classes
for further explanations.

One can inform the rewrite tactic about morphisms and relations just
by using the typeclass mechanism to declare them using Instance and
Context vernacular commands. Any object of type Proper (the type of
morphism declarations) in the local context will also be automatically
used by the rewriting tactic to solve constraints.

Other representations of first class setoids and morphisms can also be
handled by encoding them as records. In the following example, the
projections of the setoid relation and of the morphism function can be
registered as parametric relations and morphisms.

.. example:: First class setoids

   .. coqtop:: in

      Require Import Relation_Definitions Setoid.

      Record Setoid : Type :=
      { car: Type;
        eq: car -> car -> Prop;
        refl: reflexive _ eq;
        sym: symmetric _ eq;
        trans: transitive _ eq
      }.

      Add Parametric Relation (s : Setoid) : (@car s) (@eq s)
        reflexivity proved by (refl s)
        symmetry proved by (sym s)
        transitivity proved by (trans s) as eq_rel.

      Record Morphism (S1 S2 : Setoid) : Type :=
      { f: car S1 -> car S2;
        compat: forall (x1 x2 : car S1), eq S1 x1 x2 -> eq S2 (f x1) (f x2)
      }.

      Add Parametric Morphism (S1 S2 : Setoid) (M : Morphism S1 S2) :
        (@f S1 S2 M) with signature (@eq S1 ==> @eq S2) as apply_mor.
      Proof. apply (compat S1 S2 M). Qed.

      Lemma test : forall (S1 S2 : Setoid) (m : Morphism S1 S2)
        (x y : car S1), eq S1 x y -> eq S2 (f _ _ m x) (f _ _ m y).
      Proof. intros. rewrite H. reflexivity. Qed.

.. _tactics-enabled-on-user-provided-relations:

Tactics enabled on user provided relations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following tactics, all prefixed by ``setoid_``, deal with arbitrary
registered relations and morphisms. Moreover, all the corresponding
unprefixed tactics (i.e. :tacn:`reflexivity`, :tacn:`symmetry`, :tacn:`transitivity`,
:tacn:`replace`, :tacn:`rewrite`) have been extended to fall back to their prefixed
counterparts when the relation involved is not Leibniz equality.
Notice, however, that using the prefixed tactics it is possible to
pass additional arguments such as ``using relation``.

.. tacv:: setoid_reflexivity
          setoid_symmetry {? in @ident}
          setoid_transitivity
          setoid_rewrite {? @orientation} @term {? at @occs} {? in @ident}
          setoid_replace @term with @term {? using relation @term} {? in @ident} {? by @tactic}
   :name: setoid_reflexivity; setoid_symmetry; setoid_transitivity; setoid_rewrite; setoid_replace

   The ``using relation`` arguments cannot be passed to the unprefixed form.
   The latter argument tells the tactic what parametric relation should
   be used to replace the first tactic argument with the second one. If
   omitted, it defaults to the ``DefaultRelation`` instance on the type of
   the objects. By default, it means the most recent ``Equivalence`` instance
   in the environment, but it can be customized by declaring
   new ``DefaultRelation`` instances. As Leibniz equality is a declared
   equivalence, it will fall back to it if no other relation is declared
   on a given type.

Every derived tactic that is based on the unprefixed forms of the
tactics considered above will also work up to user defined relations.
For instance, it is possible to register hints for :tacn:`autorewrite` that
are not proofs of Leibniz equalities. In particular it is possible to
exploit :tacn:`autorewrite` to simulate normalization in a term rewriting
system up to user defined equalities.


Printing relations and morphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Instances

   This command can be used to show the list of currently
   registered ``Reflexive`` (using ``Print Instances Reflexive``), ``Symmetric``
   or ``Transitive`` relations, Equivalences, PreOrders, PERs, and Morphisms
   (implemented as ``Proper`` instances). When the rewriting tactics refuse
   to replace a term in a context because the latter is not a composition
   of morphisms, the :cmd:`Print Instances` command can be useful to understand
   what additional morphisms should be registered.


Deprecated syntax and backward incompatibilities
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Add Setoid @A @Aeq @ST as @ident

   This command for declaring setoids and morphisms is also accepted due
   to backward compatibility reasons.

   Here ``Aeq`` is a congruence relation without parameters, ``A`` is its carrier
   and ``ST`` is an object of type (``Setoid_Theory A Aeq``) (i.e. a record
   packing together the reflexivity, symmetry and transitivity lemmas).
   Notice that the syntax is not completely backward compatible since the
   identifier was not required.

.. cmd:: Add Morphism f : @ident
   :name: Add Morphism

   This command is restricted to the declaration of morphisms
   without parameters. It is not fully backward compatible since the
   property the user is asked to prove is slightly different: for n-ary
   morphisms the hypotheses of the property are permuted; moreover, when
   the morphism returns a proposition, the property is now stated using a
   bi-implication in place of a simple implication. In practice, porting
   an old development to the new semantics is usually quite simple.

Notice that several limitations of the old implementation have been
lifted. In particular, it is now possible to declare several relations
with the same carrier and several signatures for the same morphism.
Moreover, it is now also possible to declare several morphisms having
the same signature. Finally, the :tacn:`replace` and :tacn:`rewrite` tactics can be
used to replace terms in contexts that were refused by the old
implementation. As discussed in the next section, the semantics of the
new :tacn:`setoid_rewrite` tactic differs slightly from the old one and
:tacn:`rewrite`.


Extensions
----------


Rewriting under binders
~~~~~~~~~~~~~~~~~~~~~~~

.. warning::
   Due to compatibility issues, this feature is enabled only
   when calling the :tacn:`setoid_rewrite` tactic directly and not :tacn:`rewrite`.

To be able to rewrite under binding constructs, one must declare
morphisms with respect to pointwise (setoid) equivalence of functions.
Example of such morphisms are the standard ``all`` and ``ex`` combinators for
universal and existential quantification respectively. They are
declared as morphisms in the ``Classes.Morphisms_Prop`` module. For
example, to declare that universal quantification is a morphism for
logical equivalence:

.. coqtop:: in

   Instance all_iff_morphism (A : Type) :
            Proper (pointwise_relation A iff ==> iff) (@all A).

.. coqtop:: all

   Proof. simpl_relation.

One then has to show that if two predicates are equivalent at every
point, their universal quantifications are equivalent. Once we have
declared such a morphism, it will be used by the setoid rewriting
tactic each time we try to rewrite under an ``all`` application (products
in ``Prop`` are implicitly translated to such applications).

Indeed, when rewriting under a lambda, binding variable ``x``, say from ``P x``
to ``Q x`` using the relation iff, the tactic will generate a proof of
``pointwise_relation A iff (fun x => P x) (fun x => Q x)`` from the proof
of ``iff (P x) (Q x)`` and a constraint of the form ``Proper (pointwise_relation A iff ==> ?) m``
will be generated for the surrounding morphism ``m``.

Hence, one can add higher-order combinators as morphisms by providing
signatures using pointwise extension for the relations on the
functional arguments (or whatever subrelation of the pointwise
extension). For example, one could declare the ``map`` combinator on lists
as a morphism:

.. coqtop:: in

   Instance map_morphism `{Equivalence A eqA, Equivalence B eqB} :
            Proper ((eqA ==> eqB) ==> list_equiv eqA ==> list_equiv eqB) (@map A B).

where ``list_equiv`` implements an equivalence on lists parameterized by
an equivalence on the elements.

Note that when one does rewriting with a lemma under a binder using
:tacn:`setoid_rewrite`, the application of the lemma may capture the bound
variable, as the semantics are different from rewrite where the lemma
is first matched on the whole term. With the new :tacn:`setoid_rewrite`,
matching is done on each subterm separately and in its local
environment, and all matches are rewritten *simultaneously* by
default. The semantics of the previous :tacn:`setoid_rewrite` implementation
can almost be recovered using the ``at 1`` modifier.


Subrelations
~~~~~~~~~~~~~

Subrelations can be used to specify that one relation is included in
another, so that morphism signatures for one can be used for the
other. If a signature mentions a relation ``R`` on the left of an
arrow ``==>``, then the signature also applies for any relation ``S`` that is
smaller than ``R``, and the inverse applies on the right of an arrow. One
can then declare only a few morphisms instances that generate the
complete set of signatures for a particular constant. By default, the
only declared subrelation is ``iff``, which is a subrelation of ``impl`` and
``inverse impl`` (the dual of implication). That’s why we can declare only
two morphisms for conjunction: ``Proper (impl ==> impl ==> impl) and`` and
``Proper (iff ==> iff ==> iff) and``. This is sufficient to satisfy any
rewriting constraints arising from a rewrite using ``iff``, ``impl`` or
``inverse impl`` through ``and``.

Subrelations are implemented in ``Classes.Morphisms`` and are a prime
example of a mostly user-space extension of the algorithm.


Constant unfolding
~~~~~~~~~~~~~~~~~~

The resolution tactic is based on typeclasses and hence regards user-
defined constants as transparent by default. This may slow down the
resolution due to a lot of unifications (all the declared ``Proper``
instances are tried at each node of the search tree). To speed it up,
declare your constant as rigid for proof search using the command
:cmd:`Typeclasses Opaque`.

Strategies for rewriting
------------------------

Definitions
~~~~~~~~~~~

The generalized rewriting tactic is based on a set of strategies that can be
combined to obtain custom rewriting procedures. Its set of strategies is based
on Elan’s rewriting strategies :cite:`Luttik97specificationof`. Rewriting
strategies are applied using the tactic ``rewrite_strat s`` where ``s`` is a
strategy expression. Strategies are defined inductively as described by the
following grammar:

.. productionlist:: rewriting
   s, t, u : `strategy`
           : | `lemma`
           : | `lemma_right_to_left`
           : | `failure`
           : | `identity`
           : | `reflexivity`
           : | `progress`
           : | `failure_catch`
           : | `composition`
           : | `left_biased_choice`
           : | `iteration_one_or_more`
           : | `iteration_zero_or_more`
           : | `one_subterm`
           : | `all_subterms`
           : | `innermost_first`
           : | `outermost_first`
           : | `bottom_up`
           : | `top_down`
           : | `apply_hint`
           : | `any_of_the_terms`
           : | `apply_reduction`
           : | `fold_expression`

.. productionlist:: rewriting
   strategy : "(" `s` ")"
   lemma : `c`
   lemma_right_to_left : "<-" `c`
   failure : `fail`
   identity : `id`
   reflexivity : `refl`
   progress : `progress` `s`
   failure_catch : `try` `s`
   composition : `s` ";" `u`
   left_biased_choice : choice `s` `t`
   iteration_one_or_more : `repeat` `s`
   iteration_zero_or_more : `any` `s`
   one_subterm : subterm `s`
   all_subterms : subterms `s`
   innermost_first : `innermost` `s`
   outermost_first : `outermost` `s`
   bottom_up : `bottomup` `s`
   top_down : `topdown` `s`
   apply_hint : hints `hintdb`
   any_of_the_terms : terms (`c`)+
   apply_reduction : eval `redexpr`
   fold_expression : fold `c`


Actually a few of these are defined in term of the others using a
primitive fixpoint operator:

.. productionlist:: rewriting
   try `s` : choice `s` `id`
   any `s` : fix `u`. try (`s` ; `u`)
   repeat `s` : `s` ; `any` `s`
   bottomup s : fix `bu`. (choice (progress (subterms bu)) s) ; try bu
   topdown s : fix `td`. (choice s (progress (subterms td))) ; try td
   innermost s : fix `i`. (choice (subterm i) s)
   outermost s : fix `o`. (choice s (subterm o))

The basic control strategy semantics are straightforward: strategies
are applied to subterms of the term to rewrite, starting from the root
of the term. The lemma strategies unify the left-hand-side of the
lemma with the current subterm and on success rewrite it to the right-
hand-side. Composition can be used to continue rewriting on the
current subterm. The fail strategy always fails while the identity
strategy succeeds without making progress. The reflexivity strategy
succeeds, making progress using a reflexivity proof of rewriting.
Progress tests progress of the argument strategy and fails if no
progress was made, while ``try`` always succeeds, catching failures.
Choice is left-biased: it will launch the first strategy and fall back
on the second one in case of failure. One can iterate a strategy at
least 1 time using ``repeat`` and at least 0 times using ``any``.

The ``subterm`` and ``subterms`` strategies apply their argument strategy ``s`` to
respectively one or all subterms of the current term under
consideration, left-to-right. ``subterm`` stops at the first subterm for
which ``s`` made progress. The composite strategies ``innermost`` and ``outermost``
perform a single innermost or outermost rewrite using their argument
strategy. Their counterparts ``bottomup`` and ``topdown`` perform as many
rewritings as possible, starting from the bottom or the top of the
term.

Hint databases created for :tacn:`autorewrite` can also be used
by :tacn:`rewrite_strat` using the ``hints`` strategy that applies any of the
lemmas at the current subterm. The ``terms`` strategy takes the lemma
names directly as arguments. The ``eval`` strategy expects a reduction
expression (see :ref:`performingcomputations`) and succeeds
if it reduces the subterm under consideration. The ``fold`` strategy takes
a term ``c`` and tries to *unify* it to the current subterm, converting it to ``c``
on success, it is stronger than the tactic ``fold``.


Usage
~~~~~


.. tacn:: rewrite_strat @s [in @ident]
   :name: rewrite_strat

   Rewrite using the strategy s in hypothesis ident or the conclusion.

   .. exn:: Nothing to rewrite.

      If the strategy failed.

   .. exn:: No progress made.

      If the strategy succeeded but made no progress.

   .. exn:: Unable to satisfy the rewriting constraints.

      If the strategy succeeded and made progress but the
      corresponding rewriting constraints are not satisfied.


   The ``setoid_rewrite c`` tactic is basically equivalent to
   ``rewrite_strat (outermost c)``.

