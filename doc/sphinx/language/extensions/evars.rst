.. extracted from Gallina extensions chapter

.. _existential-variables:

Existential variables
---------------------

:gdef:`Existential variables <existential variable>` represent as yet unknown
values.

.. insertprodn term_evar term_evar

.. prodn::
   term_evar ::= _
   | ?[ @ident ]
   | ?[ ?@ident ]
   | ?@ident {? @%{ {+; @ident := @term } %} }

Rocq terms can include existential variables that represent unknown
subterms that are eventually replaced with actual subterms.

Existential variables are generated in place of unsolved implicit
arguments or “_” placeholders when using commands such as ``Check`` (see
Section :ref:`requests-to-the-environment`) or when using tactics such as
:tacn:`refine`, as well as in place of unsolved instances when using
tactics such that :tacn:`eapply`. An existential
variable is defined in a context, which is the context of variables of
the placeholder which generated the existential variable, and a type,
which is the expected type of the placeholder.

As a consequence of typing constraints, existential variables can be
duplicated in such a way that they possibly appear in different
contexts than their defining context. Thus, any occurrence of a given
existential variable comes with an instance of its original context.
In the simple case, when an existential variable denotes the
placeholder which generated it, or is used in the same context as the
one in which it was generated, the context is not displayed and the
existential variable is represented by “?” followed by an identifier.

.. rocqtop:: all

   Parameter identity : forall (X:Set), X -> X.

   Check identity _ _.

   Check identity _ (fun x => _).

In the general case, when an existential variable :n:`?@ident` appears
outside its context of definition, its instance, written in the
form :n:`{ {*; @ident := @term} }`, is appended to its name, indicating
how the variables of its defining context are instantiated.
Only the variables that are defined in another context are displayed:
this is why an existential variable used in the same context as its
context of definition is written with no instance.
This behavior may be changed: see :ref:`explicit-display-existentials`.

.. rocqtop:: all

   Check (fun x y => _) 0 1.

Existential variables can be named by the user upon creation using
the syntax :n:`?[@ident]`. This is useful when the existential
variable needs to be explicitly handled later in the script (e.g.
with a named-goal selector, see :ref:`goal-selectors`).

.. extracted from Gallina chapter

.. index:: _

Inferable subterms
~~~~~~~~~~~~~~~~~~

.. todo: This topic deserves considerably more explanation, but this will have
   to do for now
   @name allows `_` (used in 43 places in the grammar), but IIUC is semantically restricted.
   Some of the cases:
   * match expressions in terms (see :n:`@term_match`)
   * binders (see :n:`@name`) in let, functions
   * function parameters
   * universe levels
   relation to implicit arguments?
   also intropatterns and hints paths, which are not terms

   :n:`@term`\s may use :gdef:`holes <hole>`, denoted by :n:`_`, for purposes such as:

   * Omitting redundant subterms.  Redundant subterms that Rocq is able to infer can
     be replaced with :n:`_`.  For example HELP ME HERE.
   * Indicating where existential variables should be created in e* tactics such as
     :tacn:`assert`.

   is it possible to see holes in the context for any of these?

Expressions often contain redundant pieces of information. Subterms that can be
automatically inferred by Rocq can be replaced by the symbol ``_`` and Rocq will
guess the missing piece of information.

e* tactics that can create existential variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A number of tactics have companion tactics that create existential variables
when the base tactic would fail because of uninstantiated variables.
The companion tactic names begin with an :n:`e` followed by the name of the
base tactic.
For example, :tacn:`eapply` works the same way as :tacn:`apply`, except that
it will create new existential variable(s) when :tacn:`apply` would fail.

   .. example:: apply vs eapply

      Both tactics unify the goal with :n:`x = z` in the theorem.  :n:`y` is
      unspecified.  This makes :tacn:`apply` fail, while :tacn:`eapply`
      creates a new existential variable :n:`?y`.

      .. rocqtop:: none reset

         Goal forall i j : nat, i = j.
         intros.

      .. rocqtop:: all

         (* Theorem eq_trans : forall (A : Type) (x y z : A), x = y -> y = z -> x = z. *)

         Fail apply eq_trans.
         eapply eq_trans.

The :n:`e*` tactics include:

   .. list-table::

      * - :tacn:`eapply`
        - :tacn:`eassert`
        - :tacn:`eassumption`
        - :tacn:`eauto`

      * - :tacn:`ecase`
        - :tacn:`econstructor`
        - :tacn:`edestruct`
        - :tacn:`ediscriminate`

      * - :tacn:`eelim`
        - :tacn:`eenough`
        - :tacn:`eexact`
        - :tacn:`eexists`

      * - :tacn:`einduction`
        - :tacn:`einjection`
        - :tacn:`eintros`
        - :tacn:`eleft`

      * - :tacn:`epose`
        - :tacn:`eremember`
        - :tacn:`erewrite`
        - :tacn:`eright`

      * - :tacn:`eset`
        - :tacn:`esimplify_eq`
        - :tacn:`esplit`
        - :tacn:`etransitivity`

Note that :tacn:`eassumption` and :tacn:`eauto` behave differently from the
others.

Automatic resolution of existential variables
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Existential variables that are used in other goals are generally resolved
automatically as a side effect of other tactics.

.. _automatic-evar-resolution:

.. example:: Automatic resolution of existential variables

   :n:`?y` is used in other goals.  The :tacn:`exact`
   shown below determines the value of this variable by unification,
   which resolves it.

   .. rocqtop:: reset in

      Set Printing Goal Names.

      Goal forall p n m : nat, n = p -> p = m -> n = m.

   .. rocqtop:: all

      intros x y z H1 H2.
      eapply eq_trans. (* creates ?y : nat as a shelved goal *)
      Unshelve. (* moves the shelved goals into focus--not needed and usually not done *)
      exact H1. (* resolves the first goal and by side effect ?y *)

   The :n:`?y` goal asks for proof that :n:`nat` has an
   :term:`inhabitant`, i.e. it is not an empty type.  This can be proved directly
   by applying a constructor of :n:`nat`, which assigns values for :n:`?y`.
   However if you choose poorly, you can end up with unprovable goals
   (in this case :n:`x = 0`).  Like this:

   .. rocqtop:: reset none

      Set Printing Goal Names.

      Goal forall p n m : nat, n = p -> p = m -> n = m.
      intros x y z H1 H2.
      eapply eq_trans. (* creates ?y : nat as a shelved goal *)

   .. rocqtop:: out

      Unshelve. (* moves the shelved goals into focus--not needed and usually not done *)

   .. rocqtop:: all

      3: apply 0.  (* assigns value to ?y *)

.. extracted from Gallina extensions chapter

.. _explicit-display-existentials:

Explicit display of existential instances for pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Existential Instances

   Activates the full display of how the
   context of an existential variable is instantiated at each of the
   occurrences of the existential variable.  Off by default.

.. rocqtop:: all

   Check (fun x y => _) 0 1.

   Set Printing Existential Instances.

   Check (fun x y => _) 0 1.

.. _tactics-in-terms:

Solving existential variables using tactics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Instead of letting the unification engine try to solve an existential
variable by itself, one can also provide an explicit hole together
with a tactic to solve it. Using the syntax ``ltac:(``\ `tacexpr`\ ``)``, the user
can put a tactic anywhere a term is expected. The order of resolution
is not specified and is implementation-dependent. The inner tactic may
use any variable defined in its scope, including repeated alternations
between variables introduced by term binding as well as those
introduced by tactic binding. The expression `tacexpr` can be any tactic
expression as described in :ref:`ltac`.

.. rocqtop:: all

   Definition foo (x : nat) : nat := ltac:(exact x).

This construction is useful when one wants to define complicated terms
using highly automated tactics without resorting to writing the proof-term
by means of the interactive proof engine.
