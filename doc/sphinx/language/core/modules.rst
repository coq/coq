Using modules
-------------

The module system provides a way of packaging related elements
together, as well as a means of massive abstraction.


.. cmd:: Module {? {| Import | Export } } @ident {* @module_binder } {? @of_module_type } {? := {+<+ @module_expr_inl } }

   .. insertprodn module_binder module_expr_inl

   .. prodn::
      module_binder ::= ( {? {| Import | Export } } {+ @ident } : @module_type_inl )
      module_type_inl ::= ! @module_type
      | @module_type {? @functor_app_annot }
      functor_app_annot ::= [ inline at level @num ]
      | [ no inline ]
      module_type ::= @qualid
      | ( @module_type )
      | @module_type @module_expr_atom
      | @module_type with @with_declaration
      with_declaration ::= Definition @qualid {? @univ_decl } := @term
      | Module @qualid := @qualid
      module_expr_atom ::= @qualid
      | ( {+ @module_expr_atom } )
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
functor, its components (constants, inductive types, submodules etc.)
are now available through the dot notation.

.. exn:: No such label @ident.
    :undocumented:

.. exn:: Signature components for label @ident do not match.
    :undocumented:

.. exn:: The field @ident is missing in @qualid.
   :undocumented:

.. |br| raw:: html

    <br>

.. note::

  #. Interactive modules and module types can be nested.
  #. Interactive modules and module types can't be defined inside of :ref:`sections<section-mechanism>`.
     Sections can be defined inside of interactive modules and module types.
  #. Hints and notations (:cmd:`Hint` and :cmd:`Notation` commands) can also appear inside interactive
     modules and module types. Note that with module definitions like:

     :n:`Module @ident__1 : @module_type := @ident__2.`

     or

     :n:`Module @ident__1 : @module_type.` |br|
     :n:`Include @ident__2.` |br|
     :n:`End @ident__1.`

     hints and the like valid for :n:`@ident__1` are the ones defined in :n:`@module_type`
     rather then those defined in :n:`@ident__2` (or the module body).
  #. Within an interactive module type definition, the :cmd:`Parameter` command declares a
     constant instead of definining a new axiom (which it does when not in a module type definition).
  #. Assumptions such as :cmd:`Axiom` that include the :n:`Inline` clause will be automatically
     expanded when the functor is applied, except when the function application is prefixed by ``!``.

.. cmd:: Include @module_type_inl {* <+ @module_expr_inl }

   Includes the content of module(s) in the current
   interactive module. Here :n:`@module_type_inl` can be a module expression or a module
   type expression. If it is a high-order module or module type
   expression then the system tries to instantiate :n:`@module_type_inl` with the current
   interactive module.

   Including multiple modules is a single :cmd:`Include` is equivalent to including each module
   in a separate :cmd:`Include` command.

.. cmd:: Include Type {+<+ @module_type_inl }

   .. deprecated:: 8.3

      Use :cmd:`Include` instead.

.. cmd:: Declare Module {? {| Import | Export } } @ident {* @module_binder } : @module_type_inl

   Declares a module :token:`ident` of type :token:`module_type_inl`.

   If :n:`@module_binder`\s are specified, declares a functor with parameters given by the list of
   :token:`module_binder`\s.

.. cmd:: Import {+ @filtered_import }

   .. insertprodn filtered_import filtered_import

   .. prodn::
      filtered_import ::= @qualid {? ( {+, @qualid {? ( .. ) } } ) }

   If :token:`qualid` denotes a valid basic module (i.e. its module type is a
   signature), makes its components available by their short names.

   .. example::

      .. coqtop:: reset in

         Module Mod.
         Definition T:=nat.
         Check T.
         End Mod.
         Check Mod.T.

      .. coqtop:: all

         Fail Check T.
         Import Mod.
         Check T.

   Some features defined in modules are activated only when a module is
   imported. This is for instance the case of notations (see :ref:`Notations`).

   Declarations made with the :attr:`local` attribute are never imported by the :cmd:`Import`
   command. Such declarations are only accessible through their fully
   qualified name.

   .. example::

      .. coqtop:: in

         Module A.
         Module B.
         Local Definition T := nat.
         End B.
         End A.
         Import A.

      .. coqtop:: all fail

         Check B.T.

   Appending a module name with a parenthesized list of names will
   make only those names available with short names, not other names
   defined in the module nor will it activate other features.

   The names to import may be constants, inductive types and
   constructors, and notation aliases (for instance, Ltac definitions
   cannot be selectively imported). If they are from an inner module
   to the one being imported, they must be prefixed by the inner path.

   The name of an inductive type may also be followed by ``(..)`` to
   import it, its constructors and its eliminators if they exist. For
   this purpose "eliminator" means a constant in the same module whose
   name is the inductive type's name suffixed by one of ``_sind``,
   ``_ind``, ``_rec`` or ``_rect``.

   .. example::

      .. coqtop:: reset in

         Module A.
         Module B.
         Inductive T := C.
         Definition U := nat.
         End B.
         Definition Z := Prop.
         End A.
         Import A(B.T(..), Z).

      .. coqtop:: all

         Check B.T.
         Check B.C.
         Check Z.
         Fail Check B.U.
         Check A.B.U.

.. cmd:: Export {+ @filtered_import }
   :name: Export

   Similar to :cmd:`Import`, except that when the module containing this command
   is imported, the :n:`{+ @qualid }` are imported as well.

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

   This flag (off by default) disables the printing of the types of fields,
   leaving only their names, for the commands :cmd:`Print Module` and
   :cmd:`Print Module Type`.

.. _module_examples:

Examples
~~~~~~~~

.. example:: Defining a simple module interactively

    .. coqtop:: in

       Module M.
       Definition T := nat.
       Definition x := 0.

    .. coqtop:: all

       Definition y : bool.
       exact true.

    .. coqtop:: in

       Defined.
       End M.

Inside a module one can define constants, prove theorems and do anything
else that can be done in the toplevel. Components of a closed
module can be accessed using the dot notation:

.. coqtop:: all

   Print M.x.

.. _example_def_simple_module_type:

.. example:: Defining a simple module type interactively

   .. coqtop:: in

      Module Type SIG.
      Parameter T : Set.
      Parameter x : T.
      End SIG.

.. _example_filter_module:

.. example:: Creating a new module that omits some items from an existing module

   Since :n:`SIG`, the type of the new module :n:`N`, doesn't define :n:`y` or
   give the body of :n:`x`, which are not included in :n:`N`.

   .. coqtop:: all

      Module N : SIG with Definition T := nat := M.
      Print N.T.
      Print N.x.
      Fail Print N.y.

   .. reset to remove N (undo in last coqtop block doesn't seem to do that), invisibly redefine M, SIG
   .. coqtop:: none reset

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

.. coqtop:: in

   Module Type SIG'.
   Definition T : Set := nat.
   Parameter x : T.
   End SIG'.

   Module N : SIG' := M.

If we just want to be sure that our implementation satisfies a
given module type without restricting the interface, we can use a
transparent constraint

.. coqtop:: in

   Module P <: SIG := M.

.. coqtop:: all

   Print P.y.

.. example:: Creating a functor (a module with parameters)

   .. coqtop:: in

      Module Two (X Y: SIG).
      Definition T := (X.T * Y.T)%type.
      Definition x := (X.x, Y.x).
      End Two.

   and apply it to our modules and do some computations:

   .. coqtop:: in


      Module Q := Two M N.

   .. coqtop:: all

      Eval compute in (fst Q.x + snd Q.x).

.. example:: A module type with two sub-modules, sharing some fields

   .. coqtop:: in

      Module Type SIG2.
        Declare Module M1 : SIG.
        Module M2 <: SIG.
          Definition T := M1.T.
          Parameter x : T.
        End M2.
      End SIG2.

   .. coqtop:: in

      Module Mod <: SIG2.
        Module M1.
          Definition T := nat.
          Definition x := 1.
        End M1.
      Module M2 := M.
      End Mod.

Notice that ``M`` is a correct body for the component ``M2`` since its ``T``
component is ``nat`` as specified for ``M1.T``.

Libraries and qualified names
---------------------------------

.. _names-of-libraries:

Names of libraries
~~~~~~~~~~~~~~~~~~

The theories developed in |Coq| are stored in *library files* which are
hierarchically classified into *libraries* and *sublibraries*. To
express this hierarchy, library names are represented by qualified
identifiers qualid, i.e. as list of identifiers separated by dots (see
:ref:`gallina-identifiers`). For instance, the library file ``Mult`` of the standard
|Coq| library ``Arith`` is named ``Coq.Arith.Mult``. The identifier that starts
the name of a library is called a *library root*. All library files of
the standard library of |Coq| have the reserved root |Coq| but library
filenames based on other roots can be obtained by using |Coq| commands
(coqc, coqtop, coqdep, …) options ``-Q`` or ``-R`` (see :ref:`command-line-options`).
Also, when an interactive |Coq| session starts, a library of root ``Top`` is
started, unless option ``-top`` or ``-notop`` is set (see :ref:`command-line-options`).

.. _qualified-names:

Qualified names
~~~~~~~~~~~~~~~

Library files are modules which possibly contain submodules which
eventually contain constructions (axioms, parameters, definitions,
lemmas, theorems, remarks or facts). The *absolute name*, or *full
name*, of a construction in some library file is a qualified
identifier starting with the logical name of the library file,
followed by the sequence of submodules names encapsulating the
construction and ended by the proper name of the construction.
Typically, the absolute name ``Coq.Init.Logic.eq`` denotes Leibniz’
equality defined in the module Logic in the sublibrary ``Init`` of the
standard library of |Coq|.

The proper name that ends the name of a construction is the short name
(or sometimes base name) of the construction (for instance, the short
name of ``Coq.Init.Logic.eq`` is ``eq``). Any partial suffix of the absolute
name is a *partially qualified name* (e.g. ``Logic.eq`` is a partially
qualified name for ``Coq.Init.Logic.eq``). Especially, the short name of a
construction is its shortest partially qualified name.

|Coq| does not accept two constructions (definition, theorem, …) with
the same absolute name but different constructions can have the same
short name (or even same partially qualified names as soon as the full
names are different).

Notice that the notion of absolute, partially qualified and short
names also applies to library filenames.

**Visibility**

|Coq| maintains a table called the name table which maps partially qualified
names of constructions to absolute names. This table is updated by the
commands :cmd:`Require`, :cmd:`Import` and :cmd:`Export` and
also each time a new declaration is added to the context. An absolute
name is called visible from a given short or partially qualified name
when this latter name is enough to denote it. This means that the
short or partially qualified name is mapped to the absolute name in
|Coq| name table. Definitions with the :attr:`local` attribute are only accessible with
their fully qualified name (see :ref:`gallina-definitions`).

It may happen that a visible name is hidden by the short name or a
qualified name of another construction. In this case, the name that
has been hidden must be referred to using one more level of
qualification. To ensure that a construction always remains
accessible, absolute names can never be hidden.

.. example::

    .. coqtop:: all

       Check 0.

       Definition nat := bool.

       Check 0.

       Check Datatypes.nat.

       Locate nat.

.. seealso:: Commands :cmd:`Locate`.

.. _libraries-and-filesystem:

Libraries and filesystem
~~~~~~~~~~~~~~~~~~~~~~~~

.. note:: The questions described here have been subject to redesign in |Coq| 8.5.
   Former versions of |Coq| use the same terminology to describe slightly different things.

Compiled files (``.vo`` and ``.vio``) store sub-libraries. In order to refer
to them inside |Coq|, a translation from file-system names to |Coq| names
is needed. In this translation, names in the file system are called
*physical* paths while |Coq| names are contrastingly called *logical*
names.

A logical prefix Lib can be associated with a physical path using
the command line option ``-Q`` `path` ``Lib``. All subfolders of path are
recursively associated to the logical path ``Lib`` extended with the
corresponding suffix coming from the physical path. For instance, the
folder ``path/fOO/Bar`` maps to ``Lib.fOO.Bar``. Subdirectories corresponding
to invalid |Coq| identifiers are skipped, and, by convention,
subdirectories named ``CVS`` or ``_darcs`` are skipped too.

Thanks to this mechanism, ``.vo`` files are made available through the
logical name of the folder they are in, extended with their own
basename. For example, the name associated to the file
``path/fOO/Bar/File.vo`` is ``Lib.fOO.Bar.File``. The same caveat applies for
invalid identifiers. When compiling a source file, the ``.vo`` file stores
its logical name, so that an error is issued if it is loaded with the
wrong loadpath afterwards.

Some folders have a special status and are automatically put in the
path. |Coq| commands associate automatically a logical path to files in
the repository trees rooted at the directory from where the command is
launched, ``coqlib/user-contrib/``, the directories listed in the
``$COQPATH``, ``${XDG_DATA_HOME}/coq/`` and ``${XDG_DATA_DIRS}/coq/``
environment variables (see `XDG base directory specification
<http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html>`_)
with the same physical-to-logical translation and with an empty logical prefix.

The command line option ``-R`` is a variant of ``-Q`` which has the strictly
same behavior regarding loadpaths, but which also makes the
corresponding ``.vo`` files available through their short names in a way
similar to the :cmd:`Import` command. For instance, ``-R path Lib``
associates to the file ``/path/fOO/Bar/File.vo`` the logical name
``Lib.fOO.Bar.File``, but allows this file to be accessed through the
short names ``fOO.Bar.File,Bar.File`` and ``File``. If several files with
identical base name are present in different subdirectories of a
recursive loadpath, which of these files is found first may be system-
dependent and explicit qualification is recommended. The ``From`` argument
of the ``Require`` command can be used to bypass the implicit shortening
by providing an absolute root to the required file (see :ref:`compiled-files`).

There also exists another independent loadpath mechanism attached to
OCaml object files (``.cmo`` or ``.cmxs``) rather than |Coq| object
files as described above. The OCaml loadpath is managed using
the option ``-I`` `path` (in the OCaml world, there is neither a
notion of logical name prefix nor a way to access files in
subdirectories of path). See the command :cmd:`Declare ML Module` in
:ref:`compiled-files` to understand the need of the OCaml loadpath.

See :ref:`command-line-options` for a more general view over the |Coq| command
line options.
