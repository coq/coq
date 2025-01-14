.. _themodulesystem:

The Module System
=================

The module system extends the Calculus of Inductive Constructions
providing a convenient way to structure large developments as well as
a means of massive abstraction.


Modules and module types
----------------------------

**Access path.** An access path is denoted by :math:`p` and can be
either a module variable :math:`X` or, if :math:`p′` is an access path
and :math:`id` an identifier, then :math:`p′.id` is an access path.


**Structure element.** A structure element is denoted by :math:`e` and
is either a definition of a :term:`constant`, an assumption, a definition of
an inductive, a definition of a module, an alias of a module or a module
type abbreviation.


**Structure expression.** A structure expression is denoted by :math:`S` and can be:

+ an access path :math:`p`
+ a plain structure :math:`\Struct~e ; … ; e~\End`
+ a functor :math:`\Functor(X:S)~S′`, where :math:`X` is a module variable, :math:`S` and :math:`S′` are
  structure expressions
+ an application :math:`S~p`, where :math:`S` is a structure expression and :math:`p` an
  access path
+ a refined structure :math:`S~\with~p := p′` or :math:`S~\with~p := t:T` where :math:`S` is a
  structure expression, :math:`p` and :math:`p′` are access paths, :math:`t` is a term and :math:`T` is
  the type of :math:`t`.

**Module definition.** A module definition is written :math:`\Mod{X}{S}{S'}`
and consists of a module variable :math:`X`, a module type
:math:`S` which can be any structure expression and optionally a
module implementation :math:`S′` which can be any structure expression
except a refined structure.


**Module alias.** A module alias is written :math:`\ModA{X}{p}`
and consists of a module variable :math:`X` and a module path
:math:`p`.

**Module type abbreviation.**
A module type abbreviation is written :math:`\ModType{Y}{S}`,
where :math:`Y` is an identifier and :math:`S` is any structure
expression .

.. extracted from Gallina extensions chapter

Using modules
-------------

The module system provides a way of packaging related elements
together, as well as a means of massive abstraction.


.. cmd:: Module {? {| Import | Export } {? @import_categories } } @ident {* @module_binder } {? @of_module_type } {? := {+<+ @module_expr_inl } }

   .. insertprodn module_binder module_expr_inl

   .. prodn::
      module_binder ::= ( {? {| Import | Export } {? @import_categories } } {+ @ident } : @module_type_inl )
      module_type_inl ::= ! @module_type
      | @module_type {? @functor_app_annot }
      functor_app_annot ::= [ inline at level @natural ]
      | [ no inline ]
      module_type ::= @qualid
      | ( @module_type )
      | @module_type @module_expr_atom
      | @module_type with @with_declaration
      with_declaration ::= Definition @qualid {? @univ_decl } := @term
      | Module @qualid := @qualid
      module_expr_atom ::= @qualid
      | ( @module_expr_atom )
      of_module_type ::= : @module_type_inl
      | {* <: @module_type_inl }
      module_expr_inl ::= ! {+ @module_expr_atom }
      | {+ @module_expr_atom } {? @functor_app_annot }

   Defines a module named :token:`ident`.  See the examples :ref:`here<module_examples>`.

   The :n:`Import` and :n:`Export` flags specify whether the module should be automatically
   imported or exported.

   Specifying :n:`{* @module_binder }` starts a functor with
   parameters given by the :n:`@module_binder`\s.  (A *functor* is a function
   from modules to modules.)

   :n:`@of_module_type` specifies the module type.  :n:`{+ <: @module_type_inl }`
   starts a module that satisfies each :n:`@module_type_inl`.

   .. todo: would like to find a better term than "interactive", not very descriptive

   :n:`:= {+<+ @module_expr_inl }` specifies the body of a module or functor
   definition.  If it's not specified, then the module is defined *interactively*,
   meaning that the module is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module` command.
   Interactively defining the :n:`@module_expr_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module` command.

   The ! prefix indicates that any assumption command (such as :cmd:`Axiom`) with an :n:`Inline` clause
   in the type of the functor arguments will be ignored.

   .. todo: What is an Inline directive?  sb command but still unclear.  Maybe referring to the
      "inline" in functor_app_annot?  or assumption_token Inline assum_list?

.. cmd:: Module Type @ident {* @module_binder } {* <: @module_type_inl } {? := {+<+ @module_type_inl } }

   Defines a module type named :n:`@ident`.  See the example :ref:`here<example_def_simple_module_type>`.

   Specifying :n:`{* @module_binder }` starts a functor type with
   parameters given by the :n:`@module_binder`\s.

   :n:`:= {+<+ @module_type_inl }` specifies the body of a module or functor type
   definition.  If it's not specified, then the module type is defined *interactively*,
   meaning that the module type is defined as a series of commands terminated with :cmd:`End`
   instead of in a single :cmd:`Module Type` command.
   Interactively defining the :n:`@module_type_inl`\s in a series of
   :cmd:`Include` commands is equivalent to giving them all in a single
   non-interactive :cmd:`Module Type` command.

.. _terminating_module:

**Terminating an interactive module or module type definition**

Interactive modules are terminated with the :cmd:`End` command, which
is also used to terminate :ref:`Sections<section-mechanism>`.
:n:`End @ident` closes the interactive module or module type :token:`ident`.
If the module type was given, the command verifies that the content of the module
matches the module type.  If the module is not a
functor, its components (:term:`constants <constant>`, inductive types, submodules etc.)
are now available through the dot notation.

.. exn:: Signature components for field @ident do not match.
    :undocumented:

.. exn:: The field @ident is missing in @qualid.
   :undocumented:

.. |br| raw:: html

    <br>

.. note::

  #. Interactive modules and module types can be nested.
  #. Interactive modules and module types can't be defined inside of :ref:`sections<section-mechanism>`.
     Sections can be defined inside of interactive modules and module types.
  #. Hints and notations (the :ref:`Hint <creating_hints>` and :cmd:`Notation`
     commands) can also appear inside interactive
     modules and module types. Note that with module definitions like:

     :n:`Module @ident__1 : @module_type := @ident__2.`

     or

     :n:`Module @ident__1 : @module_type.` |br|
     :n:`Include @ident__2.` |br|
     :n:`End @ident__1.`

     hints and the like valid for :n:`@ident__1` are the ones defined in :n:`@module_type`
     rather then those defined in :n:`@ident__2` (or the module body).
  #. Within an interactive module type definition, the :cmd:`Parameter` command declares a
     :term:`constant` instead of definining a new axiom (which it does when not in a module type definition).
  #. Assumptions such as :cmd:`Axiom` that include the :n:`Inline` clause will be automatically
     expanded when the functor is applied, except when the function application is prefixed by ``!``.

.. cmd:: Include @module_type_inl {* <+ @module_type_inl }

   Includes the content of module(s) in the current
   interactive module. Here :n:`@module_type_inl` can be a module expression or a module
   type expression. If it is a high-order module or module type
   expression then the system tries to instantiate :n:`@module_type_inl` with the current
   interactive module.

   Including multiple modules in a single :cmd:`Include` is equivalent to including each module
   in a separate :cmd:`Include` command.

.. cmd:: Include Type {+<+ @module_type_inl }

   .. deprecated:: 8.3

      Use :cmd:`Include` instead.

.. cmd:: Declare Module {? {| Import | Export } {? @import_categories } } @ident {* @module_binder } : @module_type_inl

   Declares a module :token:`ident` of type :token:`module_type_inl`.

   If :n:`@module_binder`\s are specified, declares a functor with parameters given by the list of
   :token:`module_binder`\s.

.. cmd:: Import {? @import_categories } {+ @filtered_import }

   For each module name :n:`@qualid` in :n:`@filtered_import`,
   if :n:`@qualid` denotes a valid basic module (i.e. its module type is a
   signature), makes its components available by their short names.

   When used inside a section, the effect is local to the section.

   .. example::

      .. rocqtop:: reset in

         Module Mod.
         Definition T:=nat.
         Check T.
         End Mod.
         Check Mod.T.

      .. rocqtop:: all

         Fail Check T.
         Import Mod.
         Check T.

   Some features defined in modules are activated only when a module is
   imported. This is for instance the case of notations (see :ref:`Notations`).

   Declarations made with the :attr:`local` attribute are never imported by the :cmd:`Import`
   command. Such declarations are only accessible through their fully
   qualified name.

   .. example::

      .. rocqtop:: in

         Module A.
         Module B.
         Local Definition T := nat.
         End B.
         End A.
         Import A.

      .. rocqtop:: all fail

         Check B.T.

   .. insertprodn filtered_import filtered_import

   .. prodn::
      filtered_import ::= @qualid {? ( {+, @qualid {? ( .. ) } } ) }

   Appending a module name with a parenthesized list of names will
   make only those names available with short names, not other names
   defined in the module nor will it activate other features.

   The names to import may be :term:`constants <constant>`, inductive types and
   constructors, and notation aliases (for instance, Ltac definitions
   cannot be selectively imported). If they are from an inner module
   to the one being imported, they must be prefixed by the inner path.

   The name of an inductive type may also be followed by ``(..)`` to
   import it, its constructors and its eliminators if they exist. For
   this purpose "eliminator" means a :term:`constant` in the same module whose
   name is the inductive type's name suffixed by one of ``_sind``,
   ``_ind``, ``_rec`` or ``_rect``.

   .. example::

      .. rocqtop:: reset in

         Module A.
         Module B.
         Inductive T := C.
         Definition U := nat.
         End B.
         Definition Z := Prop.
         End A.
         Import A(B.T(..), Z).

      .. rocqtop:: all

         Check B.T.
         Check B.C.
         Check Z.
         Fail Check B.U.
         Check A.B.U.

   .. warn:: Cannot import local constant, it will be ignored.

      This warning is printed when a name in the list of names to
      import was declared as a local constant, and the name is not imported.

   .. insertprodn import_categories import_categories

   .. prodn::
      import_categories ::= {? - } ( {+, @qualid } )


   Putting a list of :n:`@import_categories` after ``Import`` will
   restrict activation of features according to those categories.
   Currently supported categories are:

   - ``coercions`` corresponding to :cmd:`Coercion`.

   - ``hints`` corresponding to the `Hint` commands (e.g. :cmd:`Hint
     Resolve` or :cmd:`Hint Rewrite`) and :ref:`typeclass
     <typeclasses>` instances.

   - ``canonicals`` corresponding to :cmd:`Canonical Structure`.

   - ``notations`` corresponding to :cmd:`Notation` (including
     :cmd:`Reserved Notation`), scope controls (:cmd:`Delimit Scope`,
     :cmd:`Bind Scope`, :cmd:`Open Scope`) but not :ref:`Abbreviations`.

   - ``options`` for :ref:`flags-options-tables`

   - ``ltac.notations`` corresponding to :cmd:`Tactic Notation`.

   - ``ltac2.notations`` corresponding to :cmd:`Ltac2 Notation`
     (including Ltac2 abbreviations).

   Plugins may define their own categories.

.. cmd:: Export {? @import_categories } {+ @filtered_import }

   Similar to :cmd:`Import`, except that when the module containing this command
   is imported, the :n:`{+ @qualid }` are imported as well.

   When used in a section, the effect is not local to the section.

   The selective import syntax also works with Export.

   .. exn:: @qualid is not a module.
      :undocumented:

   .. warn:: Trying to mask the absolute name @qualid!
      :undocumented:

.. cmd:: Print Module @qualid

   Prints the module type and (optionally) the body of the module :n:`@qualid`.

.. cmd:: Print Module Type @qualid

   Prints the module type corresponding to :n:`@qualid`.

.. flag:: Short Module Printing

   This :term:`flag` (off by default) disables the printing of the types of fields,
   leaving only their names, for the commands :cmd:`Print Module` and
   :cmd:`Print Module Type`.

.. cmd:: Print Namespace @dirpath

   Prints the names and types of all loaded constants whose fully qualified
   names start with :n:`@dirpath`. For example, the command ``Print Namespace Stdlib.``
   displays the names and types of all loaded constants in the standard library.
   The command ``Print Namespace Stdlib.Init`` only shows constants defined in one
   of the files in the ``Init`` directory. The command ``Print Namespace
   Stdlib.Init.Nat`` shows what is in the ``Nat`` library file inside the ``Init``
   directory. Module names may appear in :n:`@dirpath`.

   .. example::

      .. rocqtop:: reset in

         Module A.
         Definition foo := 0.
         Module B.
         Definition bar := 1.
         End B.
         End A.

      .. rocqtop:: all

         Print Namespace Top.
         Print Namespace Top.A.
         Print Namespace Top.A.B.

.. _module_examples:

Examples
~~~~~~~~

.. example:: Defining a simple module interactively

    .. rocqtop:: in

       Module M.
       Definition T := nat.
       Definition x := 0.

    .. rocqtop:: all

       Definition y : bool.
       exact true.

    .. rocqtop:: in

       Defined.
       End M.

Inside a module one can define :term:`constants <constant>`, prove theorems and do anything
else that can be done in the toplevel. Components of a closed
module can be accessed using the dot notation:

.. rocqtop:: all

   Print M.x.

.. _example_def_simple_module_type:

.. example:: Defining a simple module type interactively

   .. rocqtop:: in

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

.. _example_filter_module:

.. example:: Creating a new module that omits some items from an existing module

   Since :n:`SIG`, the type of the new module :n:`N`, doesn't define :n:`y` or
   give the body of :n:`x`, which are not included in :n:`N`.

   .. rocqtop:: all

      Module N : SIG with Definition T := nat := M.
      Print N.T.
      Print N.x.
      Fail Print N.y.

   .. reset to remove N (undo in last coqtop block doesn't seem to do that), invisibly redefine M, SIG
   .. rocqtop:: none reset

      Module M.
      Definition T := nat.
      Definition x := 0.
      Definition y : bool.
      exact true.
      Defined.
      End M.

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

The definition of :g:`N` using the module type expression :g:`SIG` with
:g:`Definition T := nat` is equivalent to the following one:

.. rocqtop:: in

   Module Type SIG'.
   Definition T : Set := nat.
   Parameter x : T.
   End SIG'.

   Module N : SIG' := M.

.. exn:: No field named @ident in @qualid.

   Raised when the final :n:`@ident` in the left-hand side :n:`@qualid` of
   a :n:`@with_declaration` is applied to a module type :n:`@qualid` that
   has no field named this :n:`@ident`.

If we just want to be sure that our implementation satisfies a
given module type without restricting the interface, we can use a
transparent constraint

.. rocqtop:: in

   Module P <: SIG := M.

.. rocqtop:: all

   Print P.y.

.. example:: Creating a functor (a module with parameters)

   .. rocqtop:: in

      Module Two (X Y: SIG).
      Definition T := (X.T * Y.T)%type.
      Definition x := (X.x, Y.x).
      End Two.

   and apply it to our modules and do some computations:

   .. rocqtop:: in


      Module Q := Two M N.

   .. rocqtop:: all

      Eval compute in (fst Q.x + snd Q.x).

.. example:: A module type with two sub-modules, sharing some fields

   .. rocqtop:: in

      Module Type SIG2.
        Declare Module M1 : SIG.
        Module M2 <: SIG.
          Definition T := M1.T.
          Parameter x : T.
        End M2.
      End SIG2.

   .. rocqtop:: in

      Module Mod <: SIG2.
        Module M1.
          Definition T := nat.
          Definition x := 1.
        End M1.
      Module M2 := M.
      End Mod.

Notice that ``M`` is a correct body for the component ``M2`` since its ``T``
component is ``nat`` as specified for ``M1.T``.

.. extracted from Gallina extensions chapter

.. _qualified-names:

Qualified names
---------------

Qualified names (:token:`qualid`\s) are hierarchical names that are used to
identify items such as definitions, theorems and parameters that may be defined
inside modules (see :cmd:`Module`).  In addition, they are used to identify
compiled files.  Syntactically, they have this form:

.. insertprodn qualid qualid

.. prodn::
   qualid ::= @ident {* .@ident }

*Fully qualified* or *absolute* qualified names uniquely identify files
(as in the `Require` command) and items within files, such as a single
:cmd:`Variable` definition.  It's usually possible to use a suffix of the fully
qualified name (a *short name*) that uniquely identifies an item.

The first part of a fully qualified name identifies a file, which may be followed
by a second part that identifies a specific item within that file.  Qualified names
that identify files don't have a second part.

While qualified names always consist of a series of dot-separated :n:`@ident`\s,
*the following few paragraphs omit the dots for the sake of simplicity.*

**File part.** Files are identified by :gdef:`logical paths <logical path>`,
which are prefixes in the form :n:`{* @ident__logical } {+ @ident__file }`, such
as :n:`Stdlib.Init.Logic`, in which:

- :n:`{* @ident__logical }`, the :gdef:`logical name`, maps to one or more
  directories (or :gdef:`physical paths <physical path>`) in the user's file system.
  The logical name
  is used so that Rocq scripts don't depend on where files are installed.
  For example, the directory associated with :n:`Stdlib` contains Rocq's standard library.
  The logical name is generally a single :n:`@ident`.

- :n:`{+ @ident__file }` corresponds to the file system path of the file relative
  to the directory that contains it.  For example, :n:`Init.Logic`
  corresponds to the file system path :n:`Init/Logic.v` on Linux)

When Rocq is processing a script that hasn't been saved in a file, such as a new
buffer in RocqIDE or anything in `rocq repl`, definitions in the script are associated
with the logical name :n:`Top` and there is no associated file system path.

**Item part.** Items are further qualified by a suffix in the form
:n:`{* @ident__module } @ident__base` in which:

- :n:`{* @ident__module }` gives the names of the nested modules, if any,
  that syntactically contain the definition of the item.  (See :cmd:`Module`.)

- :n:`@ident__base` is the base name used in the command defining
  the item.  For example, :n:`eq` in the :cmd:`Inductive` command defining it
  in `Stdlib.Init.Logic` is the base name for `Stdlib.Init.Logic.eq`, the standard library
  definition of :term:`Leibniz equality`.

If :n:`@qualid` is the fully qualified name of an item, Rocq
always interprets :n:`@qualid` as a reference to that item.  If :n:`@qualid` is also a
partially qualified name for another item, then you must provide a more-qualified
name to uniquely identify that other item.  For example, if there are two
fully qualified items named `Foo.Bar` and `Stdlib.X.Foo.Bar`, then `Foo.Bar` refers
to the first item and `X.Foo.Bar` is the shortest name for referring to the second item.

Definitions with the :attr:`local` attribute are only accessible with
their fully qualified name (see :ref:`gallina-definitions`).

.. example::

    .. rocqtop:: all

       Check 0.

       Definition nat := bool.

       Check 0.

       Check Datatypes.nat.

       Locate nat.

.. seealso:: Commands :cmd:`Locate`.

:ref:`logical-paths-load-path` describes how :term:`logical paths <logical path>`
become associated with specific files.

.. _controlling-locality-of-commands:

Controlling the scope of commands with locality attributes
----------------------------------------------------------

Many commands have effects that apply only within a specific scope,
typically the section or the module in which the command was
called. Locality :term:`attributes <attribute>` can alter the scope of
the effect. Below, we give the semantics of each locality attribute
while noting a few exceptional commands for which :attr:`local` and
:attr:`global` attributes are interpreted differently.

.. attr:: local

   This :term:`attribute` limits the effect of the command to the
   current scope (section or module).

   The ``Local`` prefix is an alternative syntax for the :attr:`local`
   attribute (see :n:`@legacy_attr`).

   .. note::

      - For some commands, this is the only locality supported within
        sections (e.g., for :cmd:`Notation`, :cmd:`Ltac` and
        :ref:`Hint <creating_hints>` commands).

      - For some commands, this is the default locality within
        sections even though other locality attributes are supported
        as well (e.g., for the :cmd:`Arguments` command).

   .. warning::

      **Exception:** when :attr:`local` is applied to
      :cmd:`Definition`, :cmd:`Theorem` or their variants, its
      semantics are different: it makes the defined objects available
      only through their fully qualified names rather than their
      unqualified names after an :cmd:`Import`.

.. attr:: export

   This :term:`attribute` makes the effect of the command
   persist when the section is closed and applies the effect when the
   module containing the command is imported.

   Commands supporting this attribute include :cmd:`Set`, :cmd:`Unset`
   and the :ref:`Hint <creating_hints>` commands, although the latter
   don't support it within sections.

.. attr:: global

   This :term:`attribute` makes the effect of the command
   persist even when the current section or module is closed.  Loading
   the file containing the command (possibly transitively) applies the
   effect of the command.

   The ``Global`` prefix is an alternative syntax for the
   :attr:`global` attribute (see :n:`@legacy_attr`).

   .. warning::

      **Exception:** for a few commands (like :cmd:`Notation` and
      :cmd:`Ltac`), this attribute behaves like :attr:`export`.

   .. warning::

      We strongly discourage using the :attr:`global` locality
      attribute because the transitive nature of file loading gives
      the user little control. We recommend using the :attr:`export`
      locality attribute where it is supported.

.. _visibility-attributes-modules:

Summary of locality attributes in a module
------------------------------------------

This table sums up the effect of locality attributes on the scope of vernacular
commands in a module, when outside the module where they were entered. In the
following table:

* a cross (❌) marks an unsupported attribute (compilation error);
* “not available” means that the command has no effect outside the :cmd:`Module` it
  was entered;
* “when imported” means that the command has effect outside the :cmd:`Module` if, and
  only if, the :cmd:`Module` (or the command, via :n:`@filtered_import`) is imported
  (with :cmd:`Import` or :cmd:`Export`).
* “short name when imported” means that the command has effects outside the
  :cmd:`Module`; if the :cmd:`Module` (or command, via :n:`@filtered_import`) is not
  imported, the associated identifiers must be qualified;
* “qualified name” means that the command has effects outside the :cmd:`Module`, but
  the corresponding identifier may only be referred to with a qualified name;
* “always” means that the command always has effects outside the :cmd:`Module` (even
  if it is not imported).

A similar table for :cmd:`Section` can be found
:ref:`here<visibility-attributes-sections>`.

.. list-table::
  :header-rows: 1

  * - ``Command``
    - no attribute
    - :attr:`local`
    - :attr:`export`
    - :attr:`global`

  * - :cmd:`Definition`, :cmd:`Lemma`,

      :cmd:`Axiom`, ...
    - :attr:`global`
    - qualified name
    - ❌
    - short name

      when imported

  * - :cmd:`Ltac`
    - :attr:`global`
    - not available
    - ❌
    - short name

      when imported

  * - :cmd:`Ltac2`
    - :attr:`global`
    - not available
    - ❌
    - short name

      when imported

  * - :cmd:`Notation (abbreviation)`
    - :attr:`global`
    - not available
    - ❌
    - short name

      when imported

  * - :cmd:`Notation`
    - :attr:`global`
    - not available
    - ❌
    - when imported

  * - :cmd:`Tactic Notation`
    - :attr:`global`
    - not available
    - ❌
    - when imported

  * - :cmd:`Ltac2 Notation`
    - :attr:`global`
    - not available
    - ❌
    - when imported

  * - :cmd:`Coercion`
    - :attr:`global`
    - not available
    - ❌
    - when imported

  * - :cmd:`Canonical Structure`
    - :attr:`global`

    - when imported
    - ❌
    - when imported

  * - ``Hints`` (and :cmd:`Instance`)
    - :attr:`export`
    - not available
    - when imported
    - always

  * - :cmd:`Set` or :cmd:`Unset` a flag
    - :attr:`local`
    - not available
    - when imported
    - always

Typing Modules
------------------

In order to introduce the typing system we first slightly extend the syntactic
class of terms and environments given in section :ref:`The-terms`. The
environments, apart from definitions of :term:`constants <constant>` and inductive types now also
hold any other structure elements. Terms, apart from variables, :term:`constants <constant>` and
complex terms, also include access paths.

We also need additional typing judgments:


+ :math:`\WFT{E}{S}`, denoting that a structure :math:`S` is well-formed,
+ :math:`\WTM{E}{p}{S}`, denoting that the module pointed by :math:`p` has type :math:`S` in
  the global environment :math:`E`.
+ :math:`\WEV{E}{S}{\ovl{S}}`, denoting that a structure :math:`S` is evaluated to a
  structure :math:`\ovl{S}` in weak head normal form.
+ :math:`\WS{E}{S_1}{S_2}` , denoting that a structure :math:`S_1` is a subtype of a
  structure :math:`S_2`.
+ :math:`\WS{E}{e_1}{e_2}` , denoting that a structure element :math:`e_1` is more
  precise than a structure element :math:`e_2`.

The rules for forming structures are the following:

.. inference:: WF-STR

   \WF{E;E′}{}
   ------------------------
   \WFT{E}{ \Struct~E′ ~\End}

.. inference:: WF-FUN

   \WFT{E; \ModS{X}{S}}{ \ovl{S′} }
   --------------------------
   \WFT{E}{ \Functor(X:S)~S′}


Evaluation of structures to weak head normal form:

.. inference:: WEVAL-APP

   \begin{array}{c}
   \WEV{E}{S}{\Functor(X:S_1 )~S_2}~~~~~\WEV{E}{S_1}{\ovl{S_1}} \\
   \WTM{E}{p}{S_3}~~~~~ \WS{E}{S_3}{\ovl{S_1}}
   \end{array}
   --------------------------
   \WEV{E}{S~p}{\subst{S_2}{X}{p}}


.. inference:: WEVAL-WITH-MOD

   \begin{array}{c}
   E[] ⊢ S \lra \Struct~e_1 ;…;e_i ; \ModS{X}{S_1 };e_{i+2} ;… ;e_n ~\End \\
   E;e_1 ;…;e_i [] ⊢ S_1 \lra \ovl{S_1} ~~~~~~
   E[] ⊢ p : S_2 \\
   E;e_1 ;…;e_i [] ⊢ S_2 <: \ovl{S_1}
   \end{array}
   ----------------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~X := p}{}\\
   \Struct~e_1 ;…;e_i ; \ModA{X}{p};\subst{e_{i+2}}{X}{p} ;…;\subst{e_n}{X}{p} ~\End
   \end{array}

.. inference:: WEVAL-WITH-MOD-REC

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ; \ModS{X_1}{S_1 };e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S_1~\with~p := p_1}{\ovl{S_2}}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~X_1.p := p_1}{} \\
   \Struct~e_1 ;…;e_i ; \ModS{X}{\ovl{S_2}};\subst{e_{i+2}}{X_1.p}{p_1} ;…;\subst{e_n}{X_1.p}{p_1} ~\End
   \end{array}

.. inference:: WEVAL-WITH-DEF

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ;(c:T_1);e_{i+2} ;… ;e_n ~\End} \\
   \WS{E;e_1 ;…;e_i }{(c:=t:T)}{(c:T_1)}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~c := t:T}{} \\
   \Struct~e_1 ;…;e_i ;(c:=t:T);e_{i+2} ;… ;e_n ~\End
   \end{array}

.. inference:: WEVAL-WITH-DEF-REC

   \begin{array}{c}
   \WEV{E}{S}{\Struct~e_1 ;…;e_i ; \ModS{X_1 }{S_1 };e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S_1~\with~p := p_1}{\ovl{S_2}}
   \end{array}
   --------------------------
   \begin{array}{c}
   \WEV{E}{S~\with~X_1.p := t:T}{} \\
   \Struct~e_1 ;…;e_i ; \ModS{X}{\ovl{S_2} };e_{i+2} ;… ;e_n ~\End
   \end{array}

.. inference:: WEVAL-PATH-MOD1

   \begin{array}{c}
   \WEV{E}{p}{\Struct~e_1 ;…;e_i ; \Mod{X}{S}{S_1};e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S}{\ovl{S}}
   \end{array}
   --------------------------
   E[] ⊢ p.X \lra \ovl{S}

.. inference:: WEVAL-PATH-MOD2

   \WF{E}{}
   \Mod{X}{S}{S_1}∈ E
   \WEV{E}{S}{\ovl{S}}
   --------------------------
   \WEV{E}{X}{\ovl{S}}

.. inference:: WEVAL-PATH-ALIAS1

   \begin{array}{c}
   \WEV{E}{p}{~\Struct~e_1 ;…;e_i ; \ModA{X}{p_1};e_{i+2}  ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{p_1}{\ovl{S}}
   \end{array}
   --------------------------
   \WEV{E}{p.X}{\ovl{S}}

.. inference:: WEVAL-PATH-ALIAS2

   \WF{E}{}
   \ModA{X}{p_1 }∈ E
   \WEV{E}{p_1}{\ovl{S}}
   --------------------------
   \WEV{E}{X}{\ovl{S}}

.. inference:: WEVAL-PATH-TYPE1

   \begin{array}{c}
   \WEV{E}{p}{~\Struct~e_1 ;…;e_i ; \ModType{Y}{S};e_{i+2} ;… ;e_n ~\End} \\
   \WEV{E;e_1 ;…;e_i }{S}{\ovl{S}}
   \end{array}
   --------------------------
   \WEV{E}{p.Y}{\ovl{S}}

.. inference:: WEVAL-PATH-TYPE2

   \WF{E}{}
   \ModType{Y}{S}∈ E
   \WEV{E}{S}{\ovl{S}}
   --------------------------
   \WEV{E}{Y}{\ovl{S}}


Rules for typing module:

.. inference:: MT-EVAL

   \WEV{E}{p}{\ovl{S}}
   --------------------------
   E[] ⊢ p : \ovl{S}

.. inference:: MT-STR

   E[] ⊢ p : S
   --------------------------
   E[] ⊢ p : S/p


The last rule, called strengthening is used to make all module fields
manifestly equal to themselves. The notation :math:`S/p` has the following
meaning:


+ if :math:`S\lra~\Struct~e_1 ;…;e_n ~\End` then :math:`S/p=~\Struct~e_1 /p;…;e_n /p ~\End`
  where :math:`e/p` is defined as follows (note that opaque definitions are processed
  as assumptions):

    + :math:`(c:=t:T)/p = (c:=t:T)`
    + :math:`(c:U)/p = (c:=p.c:U)`
    + :math:`\ModS{X}{S}/p = \ModA{X}{p.X}`
    + :math:`\ModA{X}{p′}/p = \ModA{X}{p′}`
    + :math:`\ind{r}{Γ_I}{Γ_C}/p = \Indp{r}{Γ_I}{Γ_C}{p}`
    + :math:`\Indpstr{r}{Γ_I}{Γ_C}{p'}{p} = \Indp{r}{Γ_I}{Γ_C}{p'}`

+ if :math:`S \lra \Functor(X:S′)~S″` then :math:`S/p=S`


The notation :math:`\Indp{r}{Γ_I}{Γ_C}{p}`
denotes an inductive definition that is definitionally equal to the
inductive definition in the module denoted by the path :math:`p`. All rules
which have :math:`\ind{r}{Γ_I}{Γ_C}` as premises are also valid for
:math:`\Indp{r}{Γ_I}{Γ_C}{p}`. We give the formation rule for
:math:`\Indp{r}{Γ_I}{Γ_C}{p}`
below as well as the equality rules on inductive types and
constructors.

The module subtyping rules:

.. inference:: MSUB-STR

   \begin{array}{c}
   \WS{E;e_1 ;…;e_n }{e_{σ(i)}}{e'_i ~\for~ i=1..m} \\
   σ : \{1… m\} → \{1… n\} ~\injective
   \end{array}
   --------------------------
   \WS{E}{\Struct~e_1 ;…;e_n ~\End}{~\Struct~e'_1 ;…;e'_m ~\End}

.. inference:: MSUB-FUN

   \WS{E}{\ovl{S_1'}}{\ovl{S_1}}
   \WS{E; \ModS{X}{S_1'}}{\ovl{S_2}}{\ovl{S_2'}}
   --------------------------
   E[] ⊢ \Functor(X:S_1 ) S_2 <: \Functor(X:S_1') S_2'


Structure element subtyping rules:

.. inference:: ASSUM-ASSUM

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   --------------------------
   \WS{E}{(c:T_1)}{(c:T_2)}

.. inference:: DEF-ASSUM

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   --------------------------
   \WS{E}{(c:=t:T_1)}{(c:T_2)}

.. inference:: ASSUM-DEF

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   E[] ⊢ c =_{βδιζη} t_2
   --------------------------
   \WS{E}{(c:T_1)}{(c:=t_2:T_2)}

.. inference:: DEF-DEF

   E[] ⊢ T_1 ≤_{βδιζη} T_2
   E[] ⊢ t_1 =_{βδιζη} t_2
   --------------------------
   \WS{E}{(c:=t_1:T_1)}{(c:=t_2:T_2)}

.. inference:: IND-IND

   E[] ⊢ Γ_I =_{βδιζη} Γ_I'
   E[Γ_I] ⊢ Γ_C =_{βδιζη} Γ_C'
   --------------------------
   \WS{E}{\ind{r}{Γ_I}{Γ_C}}{\ind{r}{Γ_I'}{Γ_C'}}

.. inference:: INDP-IND

   E[] ⊢ Γ_I =_{βδιζη} Γ_I'
   E[Γ_I] ⊢ Γ_C =_{βδιζη} Γ_C'
   --------------------------
   \WS{E}{\Indp{r}{Γ_I}{Γ_C}{p}}{\ind{r}{Γ_I'}{Γ_C'}}

.. inference:: INDP-INDP

   E[] ⊢ Γ_I =_{βδιζη} Γ_I'
   E[Γ_I] ⊢ Γ_C =_{βδιζη} Γ_C'
   E[] ⊢ p =_{βδιζη} p'
   --------------------------
   \WS{E}{\Indp{r}{Γ_I}{Γ_C}{p}}{\Indp{r}{Γ_I'}{Γ_C'}{p'}}

.. inference:: MOD-MOD

   \WS{E}{S_1}{S_2}
   --------------------------
   \WS{E}{\ModS{X}{S_1 }}{\ModS{X}{S_2 }}

.. inference:: ALIAS-MOD

   E[] ⊢ p : S_1
   \WS{E}{S_1}{S_2}
   --------------------------
   \WS{E}{\ModA{X}{p}}{\ModS{X}{S_2 }}

.. inference:: MOD-ALIAS

   E[] ⊢ p : S_2
   \WS{E}{S_1}{S_2}
   E[] ⊢ X =_{βδιζη} p
   --------------------------
   \WS{E}{\ModS{X}{S_1 }}{\ModA{X}{p}}

.. inference:: ALIAS-ALIAS

   E[] ⊢ p_1 =_{βδιζη} p_2
   --------------------------
   \WS{E}{\ModA{X}{p_1 }}{\ModA{X}{p_2 }}

.. inference:: MODTYPE-MODTYPE

   \WS{E}{S_1}{S_2}
   \WS{E}{S_2}{S_1}
   --------------------------
   \WS{E}{\ModType{Y}{S_1 }}{\ModType{Y}{S_2 }}


New environment formation rules


.. inference:: WF-MOD1

   \WF{E}{}
   \WFT{E}{S}
   --------------------------
   \WF{E; \ModS{X}{S}}{}

.. inference:: WF-MOD2

   \WS{E}{S_2}{S_1}
   \WF{E}{}
   \WFT{E}{S_1}
   \WFT{E}{S_2}
   --------------------------
   \WF{E; \ModImp{X}{S_1}{S_2}}{}

.. inference:: WF-ALIAS

   \WF{E}{}
   E[] ⊢ p : S
   --------------------------
   \WF{E; \ModA{X}{p}}{}

.. inference:: WF-MODTYPE

   \WF{E}{}
   \WFT{E}{S}
   --------------------------
   \WF{E; \ModType{Y}{S}}{}

.. inference:: WF-IND

   \begin{array}{c}
   \WF{E;\ind{r}{Γ_I}{Γ_C}}{} \\
   E[] ⊢ p:~\Struct~e_1 ;…;e_n ;\ind{r}{Γ_I'}{Γ_C'};… ~\End \\
   E[] ⊢ \ind{r}{Γ_I'}{Γ_C'} <: \ind{r}{Γ_I}{Γ_C}
   \end{array}
   --------------------------
   \WF{E; \Indp{r}{Γ_I}{Γ_C}{p} }{}


Component access rules


.. inference:: ACC-TYPE1

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;(c:T);… ~\End
   --------------------------
   E[Γ] ⊢ p.c : T

.. inference:: ACC-TYPE2

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;(c:=t:T);… ~\End
   --------------------------
   E[Γ] ⊢ p.c : T

Notice that the following rule extends the delta rule defined in section :ref:`Conversion-rules`

.. inference:: ACC-DELTA

    E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;(c:=t:U);… ~\End
    --------------------------
    E[Γ] ⊢ p.c \triangleright_δ t

In the rules below we assume
:math:`Γ_P` is :math:`[p_1{:}P_1 ; …; p_r {:}P_r ]`,
:math:`Γ_I` is :math:`[I_1{:}∀ Γ_P, A_1 ; …; I_k{:}∀ Γ_P, A_k ]`,
and :math:`Γ_C` is :math:`[c_1{:}∀ Γ_P, C_1 ; …; c_n{:}∀ Γ_P, C_n ]`.


.. inference:: ACC-IND1

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\ind{r}{Γ_I}{Γ_C};… ~\End
   --------------------------
   E[Γ] ⊢ p.I_j : ∀ Γ_P, A_j

.. inference:: ACC-IND2

   E[Γ] ⊢ p :~\Struct~e_1 ;…;e_i ;\ind{r}{Γ_I}{Γ_C};… ~\End
   --------------------------
   E[Γ] ⊢ p.c_m : ∀ Γ_P, C_m

.. inference:: ACC-INDP1

   E[] ⊢ p :~\Struct~e_1 ;…;e_i ; \Indp{r}{Γ_I}{Γ_C}{p'} ;… ~\End
   --------------------------
   E[] ⊢ p.I_i \triangleright_δ p'.I_i

.. inference:: ACC-INDP2

   E[] ⊢ p :~\Struct~e_1 ;…;e_i ; \Indp{r}{Γ_I}{Γ_C}{p'} ;… ~\End
   --------------------------
   E[] ⊢ p.c_i \triangleright_δ p'.c_i
