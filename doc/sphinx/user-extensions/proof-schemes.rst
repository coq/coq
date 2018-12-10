.. _proofschemes:

Proof schemes
===============

.. _proofschemes-induction-principles:

Generation of induction principles with ``Scheme``
--------------------------------------------------------

The ``Scheme`` command is a high-level tool for generating automatically
(possibly mutual) induction principles for given types and sorts. Its
syntax follows the schema:

.. cmd:: Scheme @ident__1 := Induction for @ident__2 Sort @sort {* with @ident__i := Induction for @ident__j Sort @sort}

  This command is a high-level tool for generating automatically
  (possibly mutual) induction principles for given types and sorts.
  Each :n:`@ident__j` is a different inductive type identifier belonging to
  the same package of mutual inductive definitions.
  The command generates the :n:`@ident__i`\s to be mutually recursive
  definitions. Each term :n:`@ident__i` proves a general principle of mutual
  induction for objects in type :n:`@ident__j`.

.. cmdv:: Scheme @ident := Minimality for @ident Sort @sort {* with @ident := Minimality for @ident' Sort @sort}

   Same as before but defines a non-dependent elimination principle more
   natural in case of inductively defined relations.

.. cmdv:: Scheme Equality for @ident
   :name: Scheme Equality

   Tries to generate a Boolean equality and a proof of the decidability of the usual equality. If `ident`
   involves some other inductive types, their equality has to be defined first.

.. cmdv:: Scheme Induction for @ident Sort @sort {* with Induction for @ident Sort @sort}

   If you do not provide the name of the schemes, they will be automatically computed from the
   sorts involved (works also with Minimality).

.. example::

   Induction scheme for tree and forest.

   A mutual induction principle for tree and forest in sort ``Set`` can be defined using the command

    .. coqtop:: none

       Axiom A : Set.
       Axiom B : Set.

    .. coqtop:: all

     Inductive tree : Set := node : A -> forest -> tree
     with forest : Set :=
         leaf : B -> forest
       | cons : tree -> forest -> forest.

     Scheme tree_forest_rec := Induction for tree Sort Set
       with forest_tree_rec := Induction for forest Sort Set.

  You may now look at the type of tree_forest_rec:

  .. coqtop:: all

    Check tree_forest_rec.

  This principle involves two different predicates for trees andforests;
  it also has three premises each one corresponding to a constructor of
  one of the inductive definitions.

  The principle `forest_tree_rec` shares exactly the same premises, only
  the conclusion now refers to the property of forests.

.. example::

  Predicates odd and even on naturals.

  Let odd and even be inductively defined as:

   .. coqtop:: all

      Inductive odd : nat -> Prop := oddS : forall n:nat, even n -> odd (S n)
      with even : nat -> Prop :=
        | evenO : even 0
        | evenS : forall n:nat, odd n -> even (S n).

  The following command generates a powerful elimination principle:

   .. coqtop:: all

    Scheme odd_even := Minimality for odd Sort Prop
    with even_odd := Minimality for even Sort Prop.

  The type of odd_even for instance will be:

  .. coqtop:: all

    Check odd_even.

  The type of `even_odd` shares the same premises but the conclusion is
  `(n:nat)(even n)->(P0 n)`.


Automatic declaration of schemes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Elimination Schemes

   Enables automatic declaration of induction principles when defining a new
   inductive type.  Defaults to on.

.. flag:: Nonrecursive Elimination Schemes

   Enables automatic declaration of induction principles for types declared with the :cmd:`Variant` and
   :cmd:`Record` commands.  Defaults to off.

.. flag:: Case Analysis Schemes

   This flag governs the generation of case analysis lemmas for inductive types,
   i.e. corresponding to the pattern matching term alone and without fixpoint.

.. flag:: Boolean Equality Schemes
          Decidable Equality Schemes

   These flags control the automatic declaration of those Boolean equalities (see
   the second variant of ``Scheme``).

.. warning::

   You have to be careful with this option since Coq may now reject well-defined
   inductive types because it cannot compute a Boolean equality for them.

.. flag:: Rewriting Schemes

   This flag governs generation of equality-related schemes such as congruence.

Combined Scheme
~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Combined Scheme @ident from {+, @ident__i}

   This command is a tool for combining induction principles generated
   by the :cmd:`Scheme` command.
   Each :n:`@ident__i` is a different inductive principle that must  belong
   to the same package of mutual inductive principle definitions.
   This command generates :n:`@ident` to be the conjunction of the
   principles: it is built from the common premises of the principles
   and concluded by the conjunction of their conclusions.
   In the case where all the inductive principles used are in sort
   ``Prop``, the propositional conjunction ``and`` is used, otherwise
   the simple product ``prod`` is used instead.

.. example::

  We can define the induction principles for trees and forests using:

  .. coqtop:: all

    Scheme tree_forest_ind := Induction for tree Sort Prop
    with forest_tree_ind := Induction for forest Sort Prop.

  Then we can build the combined induction principle which gives the
  conjunction of the conclusions of each individual principle:

  .. coqtop:: all

    Combined Scheme tree_forest_mutind from tree_forest_ind,forest_tree_ind.

  The type of tree_forest_mutind will be:

  .. coqtop:: all

    Check tree_forest_mutind.

.. example::

   We can also combine schemes at sort ``Type``:

  .. coqtop:: all

     Scheme tree_forest_rect := Induction for tree Sort Type
     with forest_tree_rect := Induction for forest Sort Type.

  .. coqtop:: all

     Combined Scheme tree_forest_mutrect from tree_forest_rect, forest_tree_rect.

  .. coqtop:: all

     Check tree_forest_mutrect.

.. _functional-scheme:

Generation of induction principles with ``Functional`` ``Scheme``
-----------------------------------------------------------------


.. cmd:: Functional Scheme @ident__0 := Induction for @ident' Sort @sort {* with @ident__i := Induction for @ident__i' Sort @sort}

   This command is a high-level experimental tool for
   generating automatically induction principles corresponding to
   (possibly mutually recursive) functions. First, it must be made
   available via ``Require Import FunInd``.
   Each :n:`@ident__i` is a different mutually defined function
   name (the names must be in the same order as when they were defined). This
   command generates the induction principle for each :n:`@ident__i`, following
   the recursive structure and case analyses of the corresponding function
   :n:`@ident__i'`.

.. warning::

   There is a difference between induction schemes generated by the command
   :cmd:`Functional Scheme` and these generated by the :cmd:`Function`. Indeed,
   :cmd:`Function` generally produces smaller principles that are closer to how
   a user would implement them. See :ref:`advanced-recursive-functions` for details.

.. example::

  Induction scheme for div2.

  We define the function div2 as follows:

  .. coqtop:: all

   Require Import FunInd.
   Require Import Arith.

   Fixpoint div2 (n:nat) : nat :=
   match n with
   | O => 0
   | S O => 0
   | S (S n') => S (div2 n')
   end.

  The definition of a principle of induction corresponding to the
  recursive structure of `div2` is defined by the command:

  .. coqtop:: all

    Functional Scheme div2_ind := Induction for div2 Sort Prop.

  You may now look at the type of div2_ind:

  .. coqtop:: all

    Check div2_ind.

  We can now prove the following lemma using this principle:

  .. coqtop:: all

    Lemma div2_le' : forall n:nat, div2 n <= n.
    intro n.
    pattern n, (div2 n).
    apply div2_ind; intros.
    auto with arith.
    auto with arith.
    simpl; auto with arith.
    Qed.

  We can use directly the functional induction (:tacn:`functional induction`) tactic instead
  of the pattern/apply trick:

  .. coqtop:: all

    Reset div2_le'.

    Lemma div2_le : forall n:nat, div2 n <= n.
    intro n.
    functional induction (div2 n).
    auto with arith.
    auto with arith.
    auto with arith.
    Qed.

.. example::

  Induction scheme for tree_size.

  We define trees by the following mutual inductive type:

  .. original LaTeX had "Variable" instead of "Axiom", which generates an ugly warning

  .. coqtop:: reset all

     Axiom A : Set.

     Inductive tree : Set :=
     node : A -> forest -> tree
     with forest : Set :=
     | empty : forest
     | cons : tree -> forest -> forest.

  We define the function tree_size that computes the size of a tree or a
  forest. Note that we use ``Function`` which generally produces better
  principles.

  .. coqtop:: all

    Require Import FunInd.

    Function tree_size (t:tree) : nat :=
    match t with
    | node A f => S (forest_size f)
    end
    with forest_size (f:forest) : nat :=
    match f with
    | empty => 0
    | cons t f' => (tree_size t + forest_size f')
    end.

  Notice that the induction principles ``tree_size_ind`` and ``forest_size_ind``
  generated by ``Function`` are not mutual.

  .. coqtop:: all

    Check tree_size_ind.

  Mutual induction principles following the recursive structure of ``tree_size``
  and ``forest_size`` can be generated by the following command:

  .. coqtop:: all

    Functional Scheme tree_size_ind2 := Induction for tree_size Sort Prop
    with forest_size_ind2 := Induction for forest_size Sort Prop.

  You may now look at the type of `tree_size_ind2`:

  .. coqtop:: all

    Check tree_size_ind2.

.. _derive-inversion:

Generation of inversion principles with ``Derive`` ``Inversion``
-----------------------------------------------------------------

.. cmd:: Derive Inversion @ident with forall (x : T), I t Sort sort

   This command generates an inversion principle for the
   :tacn:`inversion ... using ...`  tactic. Let :g:`I` be an inductive
   predicate and :g:`x` the variables occurring in t. This command
   generates and stocks the inversion lemma for the sort :g:`sort`
   corresponding to the instance :g:`∀ (x:T), I t` with the name
   :n:`@ident` in the global environment. When applied, it is
   equivalent to having inverted the instance with the tactic
   :g:`inversion`.


.. cmdv:: Derive Inversion_clear @ident with forall (x:T), I t Sort @sort

   When applied, it is equivalent to having inverted the instance with the
   tactic inversion replaced by the tactic `inversion_clear`.

.. cmdv:: Derive Dependent Inversion @ident with forall (x:T), I t Sort @sort

   When applied, it is equivalent to having inverted the instance with
   the tactic `dependent inversion`.

.. cmdv:: Derive Dependent Inversion_clear @ident with forall(x:T), I t Sort @sort

   When applied, it is equivalent to having inverted the instance
   with the tactic `dependent inversion_clear`.

.. example::

  Consider the relation `Le` over natural numbers and the following
  parameter ``P``:

  .. coqtop:: all

    Inductive Le : nat -> nat -> Set :=
    | LeO : forall n:nat, Le 0 n
    | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

    Parameter P : nat -> nat -> Prop.

  To generate the inversion lemma for the instance :g:`(Le (S n) m)` and the
  sort :g:`Prop`, we do:

  .. coqtop:: all

    Derive Inversion_clear leminv with (forall n m:nat, Le (S n) m) Sort Prop.
    Check leminv.

  Then we can use the proven inversion lemma:

  .. the original LaTeX did not have any Coq code to setup the goal

  .. coqtop:: none

    Goal forall (n m : nat) (H : Le (S n) m), P n m.
    intros.

  .. coqtop:: all

    Show.

    inversion H using leminv.
