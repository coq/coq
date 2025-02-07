Functional induction
====================

.. note::

   The functional induction (FunInd) plugin is legacy functionality. For
   new code and new projects, we recommend `Equations <http://mattam82.github.io/Coq-Equations/>`_,
   a more powerful plugin that provides most of FunInd's features. It can
   be installed through the `Coq Platform <https://github.com/coq/platform/releases>`_.
   Refer to the `Equations documentation <https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations.pdf>`_
   to learn more. FunInd is not deprecated and not planned for removal
   yet because porting code from FunInd to Equations can be difficult
   (due to differences in the generated induction principles).

.. note::
   The tactics described in this chapter require the Stdlib library.

.. _advanced-recursive-functions:

Advanced recursive functions
----------------------------

The following command is available when the ``FunInd`` library has been loaded via ``From Stdlib Require Import FunInd``:

.. cmd:: Function @fix_definition {* with @fix_definition }

   This command is a generalization of :cmd:`Fixpoint`. It is a wrapper
   for several ways of defining a function *and* other useful related
   objects, namely: an induction principle that reflects the recursive
   structure of the function (see :tacn:`functional induction`) and its fixpoint equality.
   This defines a function similar to those defined by :cmd:`Fixpoint`.
   As in :cmd:`Fixpoint`, the decreasing argument must
   be given (unless the function is not recursive), but it might not
   necessarily be *structurally* decreasing. Use the :n:`@fixannot` clause
   to name the decreasing argument *and* to describe which kind of
   decreasing criteria to use to ensure termination of recursive
   calls.

   :cmd:`Function` also supports the :n:`with` clause to create
   mutually recursive definitions, however this feature is limited
   to structurally recursive functions (i.e. when :n:`@fixannot` is a :n:`struct`
   clause).

   See :tacn:`functional induction` and :cmd:`Functional Scheme` for how to use
   the induction principle to reason easily about the function.

   The form of the :n:`@fixannot` clause determines which definition mechanism :cmd:`Function` uses.
   (Note that references to :n:`ident` below refer to the name of the function being defined.):

   *  If :n:`@fixannot` is not specified, :cmd:`Function`
      defines the nonrecursive function :token:`ident` as if it was declared with
      :cmd:`Definition`. In addition, the following are defined:

       + :token:`ident`\ ``_rect``, :token:`ident`\ ``_rec`` and :token:`ident`\ ``_ind``,
         which reflect the pattern matching structure of :token:`term` (see :cmd:`Inductive`);
       + The inductive :n:`R_@ident` corresponding to the graph of :token:`ident` (silently);
       + :token:`ident`\ ``_complete`` and :token:`ident`\ ``_correct`` which
         are inversion information linking the function and its graph.

   *  If :n:`{ struct ... }` is specified, :cmd:`Function`
      defines the structural recursive function :token:`ident` as if it was declared
      with :cmd:`Fixpoint`. In addition, the following are defined:

       + The same objects as above;
       + The fixpoint equation of :token:`ident`: :n:`@ident`\ ``_equation``.

   *  If :n:`{ measure ... }` or :n:`{ wf ... }` are specified, :cmd:`Function`
      defines a recursive function by well-founded recursion. The module ``Recdef``
      of the standard library must be loaded for this feature.

       + :n:`{measure @one_term__1 {? @ident } {? @one_term__2 } }`\: where :n:`@ident` is the decreasing argument
         and :n:`@one_term__1` is a function from the type of :n:`@ident` to :g:`nat` for which
         the decreasing argument decreases (for the :g:`lt` order on :g:`nat`)
         for each recursive call of the function. The parameters of the function are
         bound in :n:`@one_term__1`.
       + :n:`{wf @one_term @ident }`\: where :n:`@ident` is the decreasing argument and
         :n:`@one_term` is an ordering relation on the type of :n:`@ident` (i.e. of type
         `T`\ :math:`_{\sf ident}` → `T`\ :math:`_{\sf ident}` → ``Prop``) for which the decreasing argument
         decreases for each recursive call of the function. The order must be well-founded.
         The parameters of the function are bound in :n:`@one_term`.

      If the clause is ``measure`` or ``wf``, the user is left with some proof
      obligations that will be used to define the function. These proofs
      are: proofs that each recursive call is actually decreasing with
      respect to the given criteria, and (if the criteria is `wf`) a proof
      that the ordering relation is well-founded. Once proof obligations are
      discharged, the following objects are defined:

        + The same objects as with the ``struct`` clause;
        + The lemma :n:`@ident`\ ``_tcc`` which collects all proof obligations in one
          property;
        + The lemmas :n:`@ident`\ ``_terminate`` and :n:`@ident`\ ``_F`` which will be inlined
          during extraction of :n:`@ident`.

      The way this recursive function is defined is the subject of several
      papers by Yves Bertot and Antonia Balaa on the one hand, and Gilles
      Barthe, Julien Forest, David Pichardie, and Vlad Rusu on the other
      hand.

.. note::

   To obtain the right principle, it is better to put rigid
   parameters of the function as first arguments. For example it is
   better to define plus like this:

   .. rocqtop:: reset none extra-stdlib

      From Stdlib Require Import FunInd.

   .. rocqtop:: all extra-stdlib

      Function plus (m n : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (plus m p)
      end.

   than like this:

   .. rocqtop:: reset none extra-stdlib

      From Stdlib Require Import FunInd.

   .. rocqtop:: all extra-stdlib

      Function plus (n m : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (plus p m)
      end.


*Limitations*

:token:`term` must be built as a *pure pattern matching tree* (:g:`match … with`)
with applications only *at the end* of each branch.

:cmd:`Function` does not support partial application of the function being
defined. Thus, the following example cannot be accepted due to the
presence of partial application of :g:`wrong` in the body of :g:`wrong`:

.. rocqtop:: none extra-stdlib

   From Stdlib Require List.
   Import List.ListNotations.

.. rocqtop:: all fail extra-stdlib

   Function wrong (C:nat) : nat :=
     List.hd 0 (List.map wrong (C::nil)).

For now, dependent cases are not treated for non-structurally
terminating functions.

.. exn:: The recursive argument must be specified.
   :undocumented:

.. exn:: No argument name @ident.
   :undocumented:

.. exn:: Cannot use mutual definition with well-founded recursion or measure.
   :undocumented:

.. warn:: Cannot define graph for @ident.

   The generation of the graph relation (:n:`R_@ident`) used to compute the induction scheme of ident
   raised a typing error. Only :token:`ident` is defined; the induction scheme
   will not be generated. This error happens generally when:

   - the definition uses pattern matching on dependent types,
     which :cmd:`Function` cannot deal with yet.
   - the definition is not a *pattern matching tree* as explained above.

.. warn:: Cannot define principle(s) for @ident.

   The generation of the graph relation (:n:`R_@ident`) succeeded but the induction principle
   could not be built. Only :token:`ident` is defined. Please report.

.. warn:: Cannot build functional inversion principle.

   :tacn:`functional inversion` will not be available for the function.

Tactics
-------

.. tacn:: functional induction @term {? using @one_term_with_bindings } {? as @simple_intropattern }

   Performs case analysis and induction following the definition of a function
   :token:`qualid`, which must be fully applied to its arguments as part of
   :token:`term`. It uses a principle
   generated by :cmd:`Function` or :cmd:`Functional Scheme`.
   Note that this tactic is only available after a ``From Stdlib Require Import FunInd``.
   See the :cmd:`Function` command.

   :n:`using @one_term`
     Specifies the induction principle (aka elimination scheme).

   :n:`with @bindings`
     Specifies the arguments of the induction principle.

   :n:`as @simple_intropattern`
     Provides names for the introduced variables.

   .. example::

      .. rocqtop:: reset all extra-stdlib

         From Stdlib Require Import FunInd.
         Functional Scheme minus_ind := Induction for minus Sort Prop.
         Check minus_ind.
         Lemma le_minus (n m:nat) : n - m <= n.
         functional induction (minus n m) using minus_ind; simpl; auto.
         Qed.

   .. note::
      :n:`functional induction (f x1 x2 x3)` is actually a wrapper for
      :n:`induction x1, x2, x3, (f x1 x2 x3) using @qualid` followed by a cleaning
      phase, where :n:`@qualid` is the induction principle registered for :g:`f`
      (by the :cmd:`Function` or :cmd:`Functional Scheme` command)
      corresponding to the sort of the goal. Therefore
      :tacn:`functional induction` may fail if the induction scheme :n:`@qualid` is not
      defined.

   .. note::
      There is a difference between obtaining an induction scheme
      for a function by using :cmd:`Function`
      and by using :cmd:`Functional Scheme` after a normal definition using
      :cmd:`Fixpoint` or :cmd:`Definition`.

   .. exn:: Cannot find induction information on @qualid.
      :undocumented:

   .. exn:: Not the right number of induction arguments.
      :undocumented:

.. tacn:: soft functional induction {+ @one_term } {? using @one_term_with_bindings } {? as @simple_intropattern }
   :undocumented:

.. tacn:: functional inversion {| @ident | @natural } {? @qualid }

   Performs inversion on hypothesis
   :n:`@ident` of the form :n:`@qualid {+ @term} = @term` or
   :n:`@term = @qualid {+ @term}` when :n:`@qualid` is defined using :cmd:`Function`.
   Note that this tactic is only available after a ``From Stdlib Require Import FunInd``.

   :n:`@natural`
     Does the same thing as :n:`intros until @natural` followed by
     :n:`functional inversion @ident` where :token:`ident` is the
     identifier for the last introduced hypothesis.

   :n:`@qualid`
     If the hypothesis :token:`ident` (or :token:`natural`) has a type of the form
     :n:`@qualid__1 {+ @term__i } = @qualid__2 {+ @term__j }` where
     :n:`@qualid__1` and :n:`@qualid__2` are valid candidates to
     functional inversion, this variant allows choosing which :token:`qualid`
     is inverted.


   .. exn:: Hypothesis @ident must contain at least one Function.
      :undocumented:

   .. exn:: Cannot find inversion information for hypothesis @ident.

      This error may be raised when some inversion lemma failed to be generated by
      Function.

.. _functional-scheme:

Generation of induction principles with ``Functional`` ``Scheme``
-----------------------------------------------------------------


.. cmd:: Functional Scheme @func_scheme_def {* with @func_scheme_def }

   .. insertprodn func_scheme_def func_scheme_def

   .. prodn::
      func_scheme_def ::= @ident := Induction for @qualid Sort @sort_family

   An experimental high-level tool that
   automatically generates induction principles corresponding to functions that
   may be mutually recursive.  The command generates an
   induction principle named :n:`@ident` for each given function named :n:`@qualid`.
   The :n:`@qualid`\s must be given in the same order as when they were defined.

   Note the command must be made available via ``From Stdlib`` :cmd:`Require Import` ``FunInd``.

.. warning::

   There is a difference between induction schemes generated by the command
   :cmd:`Functional Scheme` and these generated by the :cmd:`Function`. Indeed,
   :cmd:`Function` generally produces smaller principles that are closer to how
   a user would implement them. See :ref:`advanced-recursive-functions` for details.

.. example::

  Induction scheme for div2.

  We define the function div2 as follows:

  .. rocqtop:: all extra-stdlib

   From Stdlib Require Import FunInd.
   From Stdlib Require Import Arith.

   Fixpoint div2 (n:nat) : nat :=
   match n with
   | O => 0
   | S O => 0
   | S (S n') => S (div2 n')
   end.

  The definition of a principle of induction corresponding to the
  recursive structure of `div2` is defined by the command:

  .. rocqtop:: all extra-stdlib

    Functional Scheme div2_ind := Induction for div2 Sort Prop.

  You may now look at the type of div2_ind:

  .. rocqtop:: all extra-stdlib

    Check div2_ind.

  We can now prove the following lemma using this principle:

  .. rocqtop:: all extra-stdlib

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

  .. rocqtop:: all extra-stdlib

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

  .. rocqtop:: reset all extra-stdlib

     Axiom A : Set.

     Inductive tree : Set :=
     node : A -> forest -> tree
     with forest : Set :=
     | empty : forest
     | cons : tree -> forest -> forest.

  We define the function tree_size that computes the size of a tree or a
  forest. Note that we use ``Function`` which generally produces better
  principles.

  .. rocqtop:: all extra-stdlib

    From Stdlib Require Import FunInd.

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

  .. rocqtop:: all extra-stdlib

    Check tree_size_ind.

  Mutual induction principles following the recursive structure of ``tree_size``
  and ``forest_size`` can be generated by the following command:

  .. rocqtop:: all extra-stdlib

    Functional Scheme tree_size_ind2 := Induction for tree_size Sort Prop
    with forest_size_ind2 := Induction for forest_size Sort Prop.

  You may now look at the type of `tree_size_ind2`:

  .. rocqtop:: all extra-stdlib

    Check tree_size_ind2.

.. cmd:: Functional Case @func_scheme_def
         Generate graph for @qualid

   Internal debugging commands.
