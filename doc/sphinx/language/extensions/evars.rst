.. extracted from Gallina extensions chapter

.. _existential-variables:

Existential variables
---------------------

.. insertprodn term_evar term_evar

.. prodn::
   term_evar ::= _
   | ?[ @ident ]
   | ?[ ?@ident ]
   | ?@ident {? @%{ {+; @ident := @term } %} }

|Coq| terms can include existential variables which represents unknown
subterms to eventually be replaced by actual subterms.

Existential variables are generated in place of unsolvable implicit
arguments or “_” placeholders when using commands such as ``Check`` (see
Section :ref:`requests-to-the-environment`) or when using tactics such as
:tacn:`refine`, as well as in place of unsolvable instances when using
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

.. coqtop:: all

   Parameter identity : forall (X:Set), X -> X.

   Check identity _ _.

   Check identity _ (fun x => _).

In the general case, when an existential variable :n:`?@ident` appears
outside of its context of definition, its instance, written under the
form :n:`{ {*; @ident := @term} }` is appending to its name, indicating
how the variables of its defining context are instantiated.
The variables of the context of the existential variables which are
instantiated by themselves are not written, unless the :flag:`Printing Existential Instances` flag
is on (see Section :ref:`explicit-display-existentials`), and this is why an
existential variable used in the same context as its context of definition is written with no instance.

.. coqtop:: all

   Check (fun x y => _) 0 1.

   Set Printing Existential Instances.

   Check (fun x y => _) 0 1.

Existential variables can be named by the user upon creation using
the syntax :n:`?[@ident]`. This is useful when the existential
variable needs to be explicitly handled later in the script (e.g.
with a named-goal selector, see :ref:`goal-selectors`).

.. extracted from Gallina chapter

.. index:: _

Inferable subterms
~~~~~~~~~~~~~~~~~~

Expressions often contain redundant pieces of information. Subterms that can be
automatically inferred by Coq can be replaced by the symbol ``_`` and Coq will
guess the missing piece of information.

.. extracted from Gallina extensions chapter

.. _explicit-display-existentials:

Explicit displaying of existential instances for pretty-printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Existential Instances

   This flag (off by default) activates the full display of how the
   context of an existential variable is instantiated at each of the
   occurrences of the existential variable.

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

.. coqtop:: all

   Definition foo (x : nat) : nat := ltac:(exact x).

This construction is useful when one wants to define complicated terms
using highly automated tactics without resorting to writing the proof-term
by means of the interactive proof engine.
