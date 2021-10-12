.. _section-mechanism:

Section mechanism
-----------------

Sections are naming scopes that permit creating section-local declarations that can
be used by other declarations in the section.  Declarations made
with :cmd:`Variable`, :cmd:`Hypothesis`, :cmd:`Context`,
:cmd:`Let`, :cmd:`Let Fixpoint` and
:cmd:`Let CoFixpoint` (or the plural variants of the first two) within sections
are local to the section.

In proofs done within the section, section-local declarations
are included in the :term:`local context` of the initial goal of the proof.
They are also accessible in definitions made with the :cmd:`Definition` command.

Sections are opened by the :cmd:`Section` command, and closed by :cmd:`End`.
Sections can be nested.
When a section is closed, its local declarations are no longer available.
Global declarations that refer to them will be adjusted so they're still
usable outside the section as shown in this :ref:`example <section_local_declarations>`.

.. cmd:: Section @ident

   Opens the section named :token:`ident`.
   Section names do not need to be unique.


.. cmd:: End @ident

   Closes the section or module named :token:`ident`.
   See :ref:`Terminating an interactive module or module type definition <terminating_module>`
   for a description of its use with modules.

   After closing the section, the section-local declarations (variables and
   :gdef:`section-local definitions <section-local definition>`, see :cmd:`Variable`) are
   *discharged*, meaning that they stop being visible and that all global
   objects defined in the section are generalized with respect to the
   variables and local definitions they each depended on in the section.

   .. exn:: There is nothing to end.
      :undocumented:

   .. exn:: Last block to end has name @ident.
       :undocumented:

.. note::
   Most commands, such as the :ref:`Hint <creating_hints>` commands,
   :cmd:`Notation` and option management commands that
   appear inside a section are canceled when the section is closed.

.. cmd:: Let @ident_decl @def_body
         Let Fixpoint @fix_definition {* with @fix_definition }
         Let CoFixpoint @cofix_definition {* with @cofix_definition }
   :name: Let; Let Fixpoint; Let CoFixpoint

   These are similar to :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`, except that
   the declared :term:`constant` is local to the current section.
   When the section is closed, all persistent
   definitions and theorems within it that depend on the constant
   will be wrapped with a :n:`@term_let` with the same declaration.

   As for :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`,
   if :n:`@term` is omitted, :n:`@type` is required and Coq enters proof mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

.. cmd:: Context {+ @binder }

   Declare variables in the context of the current section, like :cmd:`Variable`,
   but also allowing implicit variables, :ref:`implicit-generalization`, and
   let-binders.

   .. coqdoc::

     Context {A : Type} (a b : A).
     Context `{EqDec A}.
     Context (b' := b).

.. seealso:: Section :ref:`binders`. Section :ref:`contexts` in chapter :ref:`typeclasses`.

.. _section_local_declarations:

.. example:: Section-local declarations

   .. coqtop:: all

      Section s1.

   .. coqtop:: all

      Variables x y : nat.

   The command :cmd:`Let` introduces section-wide :ref:`let-in`. These definitions
   won't persist when the section is closed, and all persistent definitions which
   depend on `y'` will be prefixed with `let y' := y in`.

   .. coqtop:: in

      Let y' := y.
      Definition x' := S x.
      Definition x'' := x' + y'.

   .. coqtop:: all

      Print x'.
      Print x''.

      End s1.

      Print x'.
      Print x''.

   Notice the difference between the value of :g:`x'` and :g:`x''` inside section
   :g:`s1` and outside.
