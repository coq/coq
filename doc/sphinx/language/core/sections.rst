.. _section-mechanism:

Sections
====================================

Sections are naming scopes that permit creating section-local declarations that can
be used by other declarations in the section. Declarations made with
:cmd:`Variable`, :cmd:`Hypothesis`, :cmd:`Context`
(or the plural variants of the first two)
and definitions made with
:cmd:`Let`, :cmd:`Let Fixpoint` and :cmd:`Let CoFixpoint`
within sections are local to the section.

In proofs done within the section, section-local declarations
are included in the :term:`local context` of the initial goal of the proof.
They are also accessible in definitions made with the :cmd:`Definition` command.

Using sections
--------------

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
   In some cases, this behaviour can be tuned with locality attributes.
   See :ref:`this table<visibility-attributes-sections>`.

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
   if :n:`@term` is omitted, :n:`@type` is required and Rocq enters proof mode.
   This can be used to define a term incrementally,
   in particular by relying on the :tacn:`refine` tactic.
   See :ref:`proof-editing-mode`.

.. attr:: clearbody

   When used with :cmd:`Let` in a section,
   clears the body of the definition in the proof context of following proofs.
   The kernel will still use the body when checking.

.. note::

   Terminating the proof for a :cmd:`Let` with :cmd:`Qed` produces an opaque side definition.
   `Let foo : T. Proof. tactics. Qed.` is equivalent to

   .. rocqdoc::

      Lemma foo_subproof : T. Proof. tactics. Qed.
      #[clearbody] Let foo := foo_subproof.

.. cmd:: Context {+ @binder }

   Declare variables in the context of the current section, like :cmd:`Variable`,
   but also allowing implicit variables, :ref:`implicit-generalization`, and
   let-binders.

   .. rocqdoc::

     Context {A : Type} (a b : A).
     Context `{EqDec A}.
     Context (b' := b).

.. seealso:: Section :ref:`binders`. Section :ref:`contexts` in chapter :ref:`typeclasses`.

.. _section_local_declarations:

.. example:: Section-local declarations

   .. rocqtop:: all

      Section s1.

   .. rocqtop:: all

      Variables x y : nat.

   The command :cmd:`Let` introduces section-wide :ref:`let-in`. These definitions
   won't persist when the section is closed, and all persistent definitions which
   depend on `y'` will be prefixed with `let y' := y in`.

   .. rocqtop:: in

      Let y' := y.
      Definition x' := S x.
      Definition x'' := x' + y'.

   .. rocqtop:: all

      Print x'.
      Print x''.

      End s1.

      Print x'.
      Print x''.

   Notice the difference between the value of :g:`x'` and :g:`x''` inside section
   :g:`s1` and outside.

.. _visibility-attributes-sections:

Summary of locality attributes in a section
-------------------------------------------

This table sums up the effect of locality attributes on the scope of vernacular
commands in a :cmd:`Section`, when outside the :cmd:`Section` where they were entered. In the
following table:

* a cross (❌) marks an unsupported attribute (compilation error);
* “not available” means that the command has no effect outside the :cmd:`Section` it
  was entered;
* “available” means that the effects of the command persists outside the :cmd:`Section`.
* For :cmd:`Definition` (and :cmd:`Lemma`, ...), :cmd:`Canonical Structure`,
  :cmd:`Coercion` and :cmd:`Set` (and :cmd:`Unset`), some locality attributes
  will be passed on to the :cmd:`Module` containing the current :cmd:`Section`,
  see the associated footnotes.


A similar table for :cmd:`Module` can be found
:ref:`here <visibility-attributes-modules>`.

.. list-table::
  :header-rows: 1

  * - ``Command``
    - no attribute
    - :attr:`local`
    - :attr:`export`
    - :attr:`global`

  * - :cmd:`Definition`, :cmd:`Lemma`, :cmd:`Axiom`, ...
    - available [#note1]_
    - :attr:`local` in

      module [#note1]_
    - ❌
    - ❌

  * - :cmd:`Ltac`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Ltac2`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Notation (abbreviation)`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Notation`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Tactic Notation`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Ltac2 Notation`
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Coercion`
    - :attr:`global`
    - not available
    - ❌
    - :attr:`global` in

      module [#note2]_

  * - :cmd:`Canonical Structure`
    - :attr:`global`
    - not available
    - ❌
    - :attr:`global` in

      module [#note2]_

  * - ``Hints`` (and :cmd:`Instance`)
    - :attr:`local`
    - not available
    - ❌
    - ❌

  * - :cmd:`Set` or :cmd:`Unset` a flag
    - available [#note3]_
    - not available
    - :attr:`export` in

      module [#note3]_
    - :attr:`global` in

      module [#note3]_

.. [#note1] For :cmd:`Definition`, :cmd:`Lemma`, ... the default visibility is
   to be available outside the section and available with a short name when the
   current :cmd:`Module` is imported (with :cmd:`Import` or cmd:`Export`)
   outside the current :cmd:`Module`.
   The :attr:`local` attribute make the corresponding identifiers available in
   the current :cmd:`Module` but only with a fully qualified name outside the
   current :cmd:`Module`.

.. [#note2] For :cmd:`Coercion` and :cmd:`Canonical Structure`, the
   :attr:`global` visibility, which is the default, makes them available outside
   the section, in the current :cmd:`Module`, and outside the current
   :cmd:`Module` when it is imported (with :cmd:`Import` or cmd:`Export`).

.. [#note3] For :cmd:`Set` and :cmd:`Unset`, the :attr:`export` and
   :attr:`global` attributes both make the command's effects persist outside the
   current section, in the current :cmd:`Module`.
   It will also persist outside the current :cmd:`Module` with the
   :attr:`global` attribute, or with the :attr:`export` attribute, when the
   :cmd:`Module` is imported (with :cmd:`Import` or cmd:`Export`).
   The default behaviour (no attribute) is to make the setting persist outside
   the section in the current :cmd:`Module`, but not outside the current
   :cmd:`Module`.

.. _Admissible-rules-for-global-environments:

Typing rules used at the end of a section
--------------------------------------------

From the original rules of the type system, one can show the
admissibility of rules which change the local context of definition of
objects in the global environment. We show here the admissible rules
that are used in the discharge mechanism at the end of a section.


.. _Abstraction:

**Abstraction.**
One can modify a global declaration by generalizing it over a
previously assumed constant :math:`c`. For doing that, we need to modify the
reference to the global declaration in the subsequent global
environment and local context by explicitly applying this constant to
the constant :math:`c`.

Below, if :math:`Γ` is a context of the form :math:`[y_1 :A_1 ;~…;~y_n :A_n]`, we write
:math:`∀x:U,~\subst{Γ}{c}{x}` to mean
:math:`[y_1 :∀ x:U,~\subst{A_1}{c}{x};~…;~y_n :∀ x:U,~\subst{A_n}{c}{x}]`
and :math:`\subst{E}{|Γ|}{|Γ|c}` to mean the parallel substitution
:math:`E\{y_1 /(y_1~c)\}…\{y_n/(y_n~c)\}`.


.. _First-abstracting-property:

**First abstracting property:**

.. math::
   \frac{\WF{E;~c:U;~E′;~c′:=t:T;~E″}{Γ}}
        {\WF{E;~c:U;~E′;~c′:=λ x:U.~\subst{t}{c}{x}:∀x:U,~\subst{T}{c}{x};~\subst{E″}{c′}{(c′~c)}}
        {\subst{Γ}{c′}{(c′~c)}}}


.. math::
   \frac{\WF{E;~c:U;~E′;~c′:T;~E″}{Γ}}
        {\WF{E;~c:U;~E′;~c′:∀ x:U,~\subst{T}{c}{x};~\subst{E″}{c′}{(c′~c)}}{\subst{Γ}{c′}{(c′~c)}}}

.. math::
   \frac{\WF{E;~c:U;~E′;~\ind{p}{Γ_I}{Γ_C};~E″}{Γ}}
        {\WFTWOLINES{E;~c:U;~E′;~\ind{p+1}{∀ x:U,~\subst{Γ_I}{c}{x}}{∀ x:U,~\subst{Γ_C}{c}{x}};~
          \subst{E″}{|Γ_I ;Γ_C |}{|Γ_I ;Γ_C | c}}
         {\subst{Γ}{|Γ_I ;Γ_C|}{|Γ_I ;Γ_C | c}}}

One can similarly modify a global declaration by generalizing it over
a previously defined constant :math:`c`. Below, if :math:`Γ` is a context of the form
:math:`[y_1 :A_1 ;~…;~y_n :A_n]`, we write :math:`\subst{Γ}{c}{u}` to mean
:math:`[y_1 :\subst{A_1} {c}{u};~…;~y_n:\subst{A_n} {c}{u}]`.


.. _Second-abstracting-property:

**Second abstracting property:**

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~c′:=t:T;~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~c′:=(\letin{x}{u:U}{\subst{t}{c}{x}}):\subst{T}{c}{u};~E″}{Γ}}

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~c′:T;~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~c′:\subst{T}{c}{u};~E″}{Γ}}

.. math::
   \frac{\WF{E;~c:=u:U;~E′;~\ind{p}{Γ_I}{Γ_C};~E″}{Γ}}
        {\WF{E;~c:=u:U;~E′;~\ind{p}{\subst{Γ_I}{c}{u}}{\subst{Γ_C}{c}{u}};~E″}{Γ}}

.. _Pruning-the-local-context:

**Pruning the local context.**
If one abstracts or substitutes constants with the above rules then it
may happen that some declared or defined constant does not occur any
more in the subsequent global environment and in the local context.
One can consequently derive the following property.


.. _First-pruning-property:

.. inference:: First pruning property:

   \WF{E;~c:U;~E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}


.. _Second-pruning-property:

.. inference:: Second pruning property:

   \WF{E;~c:=u:U;~E′}{Γ}
   c~\kw{does not occur in}~E′~\kw{and}~Γ
   --------------------------------------
   \WF{E;E′}{Γ}
