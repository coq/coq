.. _extensionsofgallina:

Extensions of |Gallina|
=======================

|Gallina| is the kernel language of |Coq|. We describe here extensions of
|Gallina|’s syntax.

Variants and extensions of :g:`match`
-------------------------------------

.. _mult-match:

Multiple and nested pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The basic version of :g:`match` allows pattern matching on simple
patterns. As an extension, multiple nested patterns or disjunction of
patterns are allowed, as in ML-like languages.

The extension just acts as a macro that is expanded during parsing
into a sequence of match on simple patterns. Especially, a
construction defined using the extended match is generally printed
under its expanded form (see :flag:`Printing Matching`).

.. seealso:: :ref:`extendedpatternmatching`.

.. _if-then-else:

Pattern-matching on boolean values: the if expression
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For inductive types with exactly two constructors and for pattern matching
expressions that do not depend on the arguments of the constructors, it is possible
to use a ``if … then … else`` notation. For instance, the definition

.. coqtop:: all

   Definition not (b:bool) :=
   match b with
   | true => false
   | false => true
   end.

can be alternatively written

.. coqtop:: reset all

   Definition not (b:bool) := if b then false else true.

More generally, for an inductive type with constructors :n:`@ident__1`
and :n:`@ident__2`, the following terms are equal:

:n:`if @term__0 {? {? as @name } return @term } then @term__1 else @term__2`

:n:`match @term__0 {? {? as @name } return @term } with | @ident__1 {* _ } => @term__1 | @ident__2 {* _ } => @term__2 end`

.. example::

  .. coqtop:: all

     Check (fun x (H:{x=0}+{x<>0}) =>
     match H with
     | left _ => true
     | right _ => false
     end).

Notice that the printing uses the :g:`if` syntax because :g:`sumbool` is
declared as such (see :ref:`controlling-match-pp`).

.. _irrefutable-patterns:

Irrefutable patterns: the destructuring let variants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern-matching on terms inhabiting inductive type having only one
constructor can be alternatively written using :g:`let … in …`
constructions. There are two variants of them.


First destructuring let syntax
++++++++++++++++++++++++++++++

The expression :n:`let ( {*, @ident__i } ) := @term__0 in @term__1`
performs case analysis on :n:`@term__0` whose type must be an
inductive type with exactly one constructor.  The number of variables
:n:`@ident__i` must correspond to the number of arguments of this
contrustor.  Then, in :n:`@term__1`, these variables are bound to the
arguments of the constructor in :n:`@term__0`.  For instance, the
definition

.. coqtop:: reset all

   Definition fst (A B:Set) (H:A * B) := match H with
   | pair x y => x
   end.

can be alternatively written

.. coqtop:: reset all

   Definition fst (A B:Set) (p:A * B) := let (x, _) := p in x.

Notice that reduction is different from regular :g:`let … in …`
construction since it happens only if :n:`@term__0` is in constructor form.
Otherwise, the reduction is blocked.

The pretty-printing of a definition by matching on a irrefutable
pattern can either be done using :g:`match` or the :g:`let` construction
(see Section :ref:`controlling-match-pp`).

If term inhabits an inductive type with one constructor `C`, we have an
equivalence between

::

   let (ident₁, …, identₙ) [dep_ret_type] := term in term'

and

::

   match term [dep_ret_type] with
   C ident₁ … identₙ => term'
   end


Second destructuring let syntax
+++++++++++++++++++++++++++++++

Another destructuring let syntax is available for inductive types with
one constructor by giving an arbitrary pattern instead of just a tuple
for all the arguments. For example, the preceding example can be
written:

.. coqtop:: reset all

   Definition fst (A B:Set) (p:A*B) := let 'pair x _ := p in x.

This is useful to match deeper inside tuples and also to use notations
for the pattern, as the syntax :g:`let ’p := t in b` allows arbitrary
patterns to do the deconstruction. For example:

.. coqtop:: all

   Definition deep_tuple (A:Set) (x:(A*A)*(A*A)) : A*A*A*A :=
   let '((a,b), (c, d)) := x in (a,b,c,d).

   Notation " x 'With' p " := (exist _ x p) (at level 20).

   Definition proj1_sig' (A:Set) (P:A->Prop) (t:{ x:A | P x }) : A :=
   let 'x With p := t in x.

When printing definitions which are written using this construct it
takes precedence over let printing directives for the datatype under
consideration (see Section :ref:`controlling-match-pp`).


.. _controlling-match-pp:

Controlling pretty-printing of match expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following commands give some control over the pretty-printing
of :g:`match` expressions.

Printing nested patterns
+++++++++++++++++++++++++

.. flag:: Printing Matching

   The Calculus of Inductive Constructions knows pattern matching only
   over simple patterns. It is however convenient to re-factorize nested
   pattern matching into a single pattern matching over a nested
   pattern.

   When this flag is on (default), |Coq|’s printer tries to do such
   limited re-factorization.
   Turning it off tells |Coq| to print only simple pattern matching problems
   in the same way as the |Coq| kernel handles them.


Factorization of clauses with same right-hand side
++++++++++++++++++++++++++++++++++++++++++++++++++

.. flag:: Printing Factorizable Match Patterns

   When several patterns share the same right-hand side, it is additionally
   possible to share the clauses using disjunctive patterns. Assuming that the
   printing matching mode is on, this flag (on by default) tells |Coq|'s
   printer to try to do this kind of factorization.

Use of a default clause
+++++++++++++++++++++++

.. flag:: Printing Allow Match Default Clause

   When several patterns share the same right-hand side which do not depend on the
   arguments of the patterns, yet an extra factorization is possible: the
   disjunction of patterns can be replaced with a `_` default clause. Assuming that
   the printing matching mode and the factorization mode are on, this flag (on by
   default) tells |Coq|'s printer to use a default clause when relevant.

Printing of wildcard patterns
++++++++++++++++++++++++++++++

.. flag:: Printing Wildcard

   Some variables in a pattern may not occur in the right-hand side of
   the pattern matching clause. When this flag is on (default), the
   variables having no occurrences in the right-hand side of the
   pattern matching clause are just printed using the wildcard symbol
   “_”.


Printing of the elimination predicate
+++++++++++++++++++++++++++++++++++++

.. flag:: Printing Synth

   In most of the cases, the type of the result of a matched term is
   mechanically synthesizable. Especially, if the result type does not
   depend of the matched term. When this flag is on (default),
   the result type is not printed when |Coq| knows that it can re-
   synthesize it.


Printing matching on irrefutable patterns
++++++++++++++++++++++++++++++++++++++++++

If an inductive type has just one constructor, pattern matching can be
written using the first destructuring let syntax.

.. table:: Printing Let @qualid
   :name: Printing Let

   Specifies a set of qualids for which pattern matching is displayed using a let expression.
   Note that this only applies to pattern matching instances entered with :g:`match`.
   It doesn't affect pattern matching explicitly entered with a destructuring
   :g:`let`.
   Use the :cmd:`Add` and :cmd:`Remove` commands to update this set.


Printing matching on booleans
+++++++++++++++++++++++++++++

If an inductive type is isomorphic to the boolean type, pattern matching
can be written using ``if`` … ``then`` … ``else`` ….  This table controls
which types are written this way:

.. table:: Printing If @qualid
   :name: Printing If

   Specifies a set of qualids for which pattern matching is displayed using
   ``if`` … ``then`` … ``else`` ….  Use the :cmd:`Add` and :cmd:`Remove`
   commands to update this set.

This example emphasizes what the printing settings offer.

.. example::

     .. coqtop:: all

       Definition snd (A B:Set) (H:A * B) := match H with
       | pair x y => y
       end.

       Test Printing Let for prod.

       Print snd.

       Remove Printing Let prod.

       Unset Printing Synth.

       Unset Printing Wildcard.

       Print snd.

Module system
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

   .. todo: would like to find a better term than "interactive", not very descriptive

   :n:`@of_module_type` specifies the module type.  :n:`{+ <: @module_type_inl }`
   starts a module that satisfies each :n:`@module_type_inl`.

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

The following definition of :g:`N` using the module type expression :g:`SIG` with
:g:`Definition T := nat` is equivalent to the following one:

.. todo: what is other definition referred to above?
   "Module N' : SIG with Definition T := nat. End N`." is not it.

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

.. _Coercions:

Coercions
---------

Coercions can be used to implicitly inject terms from one *class* in
which they reside into another one. A *class* is either a sort
(denoted by the keyword ``Sortclass``), a product type (denoted by the
keyword ``Funclass``), or a type constructor (denoted by its name), e.g.
an inductive type or any constant with a type of the form
:n:`forall {+ @binder }, @sort`.

Then the user is able to apply an object that is not a function, but
can be coerced to a function, and more generally to consider that a
term of type ``A`` is of type ``B`` provided that there is a declared coercion
between ``A`` and ``B``.

More details and examples, and a description of the commands related
to coercions are provided in :ref:`implicitcoercions`.

.. _printing_constructions_full:

Printing constructions in full
------------------------------

.. flag:: Printing All

   Coercions, implicit arguments, the type of pattern matching, but also
   notations (see :ref:`syntaxextensionsandinterpretationscopes`) can obfuscate the behavior of some
   tactics (typically the tactics applying to occurrences of subterms are
   sensitive to the implicit arguments). Turning this flag on
   deactivates all high-level printing features such as coercions,
   implicit arguments, returned type of pattern matching, notations and
   various syntactic sugar for pattern matching or record projections.
   Otherwise said, :flag:`Printing All` includes the effects of the flags
   :flag:`Printing Implicit`, :flag:`Printing Coercions`, :flag:`Printing Synth`,
   :flag:`Printing Projections`, and :flag:`Printing Notations`. To reactivate
   the high-level printing features, use the command ``Unset Printing All``.

.. _printing-universes:

Printing universes
------------------

.. flag:: Printing Universes

   Turn this flag on to activate the display of the actual level of each
   occurrence of :g:`Type`. See :ref:`Sorts` for details. This wizard flag, in
   combination with :flag:`Printing All` can help to diagnose failures to unify
   terms apparently identical but internally different in the Calculus of Inductive
   Constructions.

.. cmd:: Print {? Sorted } Universes {? Subgraph ( {* @qualid } ) } {? @string }
   :name: Print Universes

   This command can be used to print the constraints on the internal level
   of the occurrences of :math:`\Type` (see :ref:`Sorts`).

   The :n:`Subgraph` clause limits the printed graph to the requested names (adjusting
   constraints to preserve the implied transitive constraints between
   kept universes).

   The :n:`Sorted` clause makes each universe
   equivalent to a numbered label reflecting its level (with a linear
   ordering) in the universe hierarchy.

   :n:`@string` is an optional output filename.
   If :n:`@string` ends in ``.dot`` or ``.gv``, the constraints are printed in the DOT
   language, and can be processed by Graphviz tools. The format is
   unspecified if `string` doesn’t end in ``.dot`` or ``.gv``.

.. _existential-variables:

Existential variables
---------------------

.. insertprodn term_evar term_evar

.. prodn::
   term_evar ::= ?[ @ident ]
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

.. _primitive-integers:

Primitive Integers
------------------

The language of terms features 63-bit machine integers as values. The type of
such a value is *axiomatized*; it is declared through the following sentence
(excerpt from the :g:`Int63` module):

.. coqdoc::

   Primitive int := #int63_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, equality of two primitive integers can be decided using the :g:`Int63.eqb` function,
declared and specified as follows:

.. coqdoc::

   Primitive eqb := #int63_eq.
   Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

   Axiom eqb_correct : forall i j, (i == j)%int63 = true -> i = j.

The complete set of such operators can be obtained looking at the :g:`Int63` module.

These primitive declarations are regular axioms. As such, they must be trusted and are listed by the
:g:`Print Assumptions` command, as in the following example.

.. coqtop:: in reset

   From Coq Require Import Int63.
   Lemma one_minus_one_is_zero : (1 - 1 = 0)%int63.
   Proof. apply eqb_correct; vm_compute; reflexivity. Qed.

.. coqtop:: all

   Print Assumptions one_minus_one_is_zero.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient, rules to reduce the applications of these primitive
operations.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlInt63`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Uint63` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (at type :g:`Int63.int`) are extracted to literal OCaml values
wrapped into the :g:`Uint63.of_int` (resp. :g:`Uint63.of_int64`) constructor on
64-bit (resp. 32-bit) platforms. Currently, this cannot be customized (see the
function :g:`Uint63.compile` from the kernel).

.. _primitive-floats:

Primitive Floats
----------------

The language of terms features Binary64 floating-point numbers as values.
The type of such a value is *axiomatized*; it is declared through the
following sentence (excerpt from the :g:`PrimFloat` module):

.. coqdoc::

   Primitive float := #float64_type.

This type is equipped with a few operators, that must be similarly declared.
For instance, the product of two primitive floats can be computed using the
:g:`PrimFloat.mul` function, declared and specified as follows:

.. coqdoc::

   Primitive mul := #float64_mul.
   Notation "x * y" := (mul x y) : float_scope.

   Axiom mul_spec : forall x y, Prim2SF (x * y)%float = SF64mul (Prim2SF x) (Prim2SF y).

where :g:`Prim2SF` is defined in the :g:`FloatOps` module.

The set of such operators is described in section :ref:`floats_library`.

These primitive declarations are regular axioms. As such, they must be trusted, and are listed by the
:g:`Print Assumptions` command.

The reduction machines (:tacn:`vm_compute`, :tacn:`native_compute`) implement
dedicated, efficient rules to reduce the applications of these primitive
operations, using the floating-point processor operators that are assumed
to comply with the IEEE 754 standard for floating-point arithmetic.

The extraction of these primitives can be customized similarly to the extraction
of regular axioms (see :ref:`extraction`). Nonetheless, the :g:`ExtrOCamlFloats`
module can be used when extracting to OCaml: it maps the Coq primitives to types
and functions of a :g:`Float64` module. Said OCaml module is not produced by
extraction. Instead, it has to be provided by the user (if they want to compile
or execute the extracted code). For instance, an implementation of this module
can be taken from the kernel of Coq.

Literal values (of type :g:`Float64.t`) are extracted to literal OCaml
values (of type :g:`float`) written in hexadecimal notation and
wrapped into the :g:`Float64.of_float` constructor, e.g.:
:g:`Float64.of_float (0x1p+0)`.

.. _bidirectionality_hints:

Bidirectionality hints
----------------------

When type-checking an application, Coq normally does not use information from
the context to infer the types of the arguments. It only checks after the fact
that the type inferred for the application is coherent with the expected type.
Bidirectionality hints make it possible to specify that after type-checking the
first arguments of an application, typing information should be propagated from
the context to help inferring the types of the remaining arguments.

An :cmd:`Arguments` command containing :n:`@argument_spec_block__1 & @argument_spec_block__2`
provides :ref:`bidirectionality_hints`.
It tells the typechecking algorithm, when type-checking
applications of :n:`@qualid`, to first type-check the arguments in
:n:`@argument_spec_block__1` and then propagate information from the typing context to
type-check the remaining arguments (in :n:`@argument_spec_block__2`).

.. example:: Bidirectionality hints

   In a context where a coercion was declared from ``bool`` to ``nat``:

   .. coqtop:: in reset

      Definition b2n (b : bool) := if b then 1 else 0.
      Coercion b2n : bool >-> nat.

   Coq cannot automatically coerce existential statements over ``bool`` to
   statements over ``nat``, because the need for inserting a coercion is known
   only from the expected type of a subterm:

   .. coqtop:: all

      Fail Check (ex_intro _ true _ : exists n : nat, n > 0).

   However, a suitable bidirectionality hint makes the example work:

   .. coqtop:: all

      Arguments ex_intro _ _ & _ _.
      Check (ex_intro _ true _ : exists n : nat, n > 0).

Coq will attempt to produce a term which uses the arguments you
provided, but in some cases involving Program mode the arguments after
the bidirectionality starts may be replaced by convertible but
syntactically different terms.
