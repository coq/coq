Functional induction
====================

.. _advanced-recursive-functions:

Advanced recursive functions
----------------------------

The following command is available when the ``FunInd`` library has been loaded via ``Require Import FunInd``:

.. cmd:: Function @fix_definition {* with @fix_definition }

   This command is a generalization of :cmd:`Fixpoint`. It is a wrapper
   for several ways of defining a function *and* other useful related
   objects, namely: an induction principle that reflects the recursive
   structure of the function (see :tacn:`function induction`) and its fixpoint equality.
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

   See :tacn:`function induction` and :cmd:`Functional Scheme` for how to use
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

   .. coqtop:: reset none

      Require Import FunInd.

   .. coqtop:: all

      Function plus (m n : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (plus m p)
      end.

   than like this:

   .. coqtop:: reset none

      Require Import FunInd.

   .. coqtop:: all

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

.. coqtop:: none

   Require List.
   Import List.ListNotations.

.. coqtop:: all fail

   Function wrong (C:nat) : nat :=
     List.hd 0 (List.map wrong (C::nil)).

For now, dependent cases are not treated for non structurally
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

.. seealso:: :ref:`functional-scheme` and :tacn:`function induction`
