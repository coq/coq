.. _section-mechanism:

Section mechanism
-----------------

Sections create local contexts which can be shared across multiple definitions.

.. example::

   Sections are opened by the :cmd:`Section` command, and closed by :cmd:`End`.

   .. coqtop:: all

      Section s1.

   Inside a section, local parameters can be introduced using :cmd:`Variable`,
   :cmd:`Hypothesis`, or :cmd:`Context` (there are also plural variants for
   the first two).

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

.. cmd:: Section @ident

   This command is used to open a section named :token:`ident`.
   Section names do not need to be unique.


.. cmd:: End @ident

   This command closes the section or module named :token:`ident`.
   See :ref:`Terminating an interactive module or module type definition<terminating_module>`
   for a description of its use with modules.

   After closing the
   section, the local declarations (variables and local definitions, see :cmd:`Variable`) are
   *discharged*, meaning that they stop being visible and that all global
   objects defined in the section are generalized with respect to the
   variables and local definitions they each depended on in the section.

   .. exn:: There is nothing to end.
      :undocumented:

   .. exn:: Last block to end has name @ident.
       :undocumented:

.. note::
   Most commands, like :cmd:`Hint`, :cmd:`Notation`, option management, … which
   appear inside a section are canceled when the section is closed.

.. cmd:: Let @ident_decl @def_body
         Let Fixpoint @fix_definition {* with @fix_definition }
         Let CoFixpoint @cofix_definition {* with @cofix_definition }
   :name: Let; Let Fixpoint; Let CoFixpoint

   These commands behave like :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`, except that
   the declared constant is local to the current section.
   When the section is closed, all persistent
   definitions and theorems within it that depend on the constant
   will be wrapped with a :n:`@term_let` with the same declaration.

   As for :cmd:`Definition`, :cmd:`Fixpoint` and :cmd:`CoFixpoint`,
   if :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
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
