.. _vernacularcommands:

Commands
========

.. _displaying:

Displaying
----------


.. _Print:

.. cmd:: Print {? Term } @reference {? @univ_name_list }

   .. insertprodn univ_name_list univ_name_list

   .. prodn::
      univ_name_list ::= @%{ {* @name } %}

   Displays definitions of terms, including opaque terms, for the object :n:`@reference`.

   * :n:`Term` - a syntactic marker to allow printing a term
     that is the same as one of the various :n:`Print` commands.  For example,
     :cmd:`Print All` is a different command, while :n:`Print Term All` shows
     information on the object whose name is ":n:`All`".

   * :n:`@univ_name_list` - locally renames the
     polymorphic universes of :n:`@reference`.
     The name `_` means the usual name is printed.

   .. exn:: @qualid not a defined object.
      :undocumented:

   .. exn:: Universe instance length is @natural but should be @natural.
      :undocumented:

   .. exn:: This object does not support universe names.
      :undocumented:


.. cmd:: Print All

   This command displays information about the current state of the
   environment, including sections and modules.

.. cmd:: Inspect @natural

   This command displays the :n:`@natural` last objects of the
   current environment, including sections and modules.

.. cmd:: Print Section @qualid

   Displays the objects defined since the beginning of the section named :n:`@qualid`.

   .. todo: "A.B" is permitted but unnecessary for modules/sections.
      should the command just take an @ident?

Query commands
--------------

Unlike other commands, :production:`query_command`\s may be prefixed with
a goal selector (:n:`@natural:`) to specify which goals it applies to.
If no selector is provided,
the command applies to the current goal.  If no proof is open, then the command only applies
to accessible objects.  (see Section :ref:`invocation-of-tactics`).

:cmd:`Eval` and :cmd:`Compute` are also :token:`query_command`\s, which are
described elsewhere

.. cmd:: About @reference {? @univ_name_list }

   Displays information about the :n:`@reference` object, which may be the
   name of any accessible defined symbol, such as a theorem, constructor,
   fixpoint or module.  If a proof is open, :n:`@reference` may refer to a
   hypothesis of the selected goal.  The information includes:
   the kind of the object (module, constant, assumption, inductive,
   constructor, abbreviation, projection, coercion,  …), long name, type,
   opacity/transparency, implicit arguments, argument names and
   argument scopes (as set in the definition of :token:`reference` or
   subsequently with the :cmd:`Arguments` command). It does not print the
   body of definitions or proofs.

   See :cmd:`Strategy` for details on opacity.

.. cmd:: Check @term

   Displays the type of :n:`@term`. When called in proof mode, the term is
   checked in the local context of the selected goal (possibly by using
   :ref:`single numbered goal selectors<goal-selectors>`). This command tries to
   resolve existential variables as much as possible.

.. cmd:: Type @term

   Displays the type of :n:`@term`, same as :cmd:`Check`, but will fail if any
   existential variables are unable to be resolved.

.. cmd:: Search {+ @search_query } {? {| inside | in | outside } {+ @qualid } }

   This command can be used to filter the goal and the global context
   to retrieve objects whose name or type satisfies a number of
   conditions.  Library files that were not loaded with :cmd:`Require`
   are not considered.  The :table:`Search Blacklist` table can also
   be used to exclude some things from all calls to :cmd:`Search`.

   The output of the command is a list of qualified identifiers and
   their types.  If the :flag:`Search Output Name Only` flag is on,
   the types are omitted.

   .. insertprodn search_query search_query

   .. prodn::
      search_query ::= @search_item
      | - @search_query
      | [ {+| {+ @search_query } } ]

   Multiple :n:`@search_item`\s can be combined into a complex
   :n:`@search_query`:

   :n:`- @search_query`
      Excludes the objects that would be filtered by
      :n:`@search_query`.  See :ref:`this example
      <search-disambiguate-notation>`.

   :n:`[ {+ @search_query } | ... | {+ @search_query } ]`
      This is a disjunction of conjunctions of queries.  A simple
      conjunction can be expressed by having a single disjunctive
      branch.  For a conjunction at top-level, the surrounding
      brackets are not required.

   .. insertprodn search_item search_item

   .. prodn::
      search_item ::= {? {| head | hyp | concl | headhyp | headconcl } : } @string {? % @scope_key }
      | {? {| head | hyp | concl | headhyp | headconcl } : } @one_pattern
      | is : @logical_kind

   Searched objects can be filtered by patterns, by the constants they
   contain (identified by their name or a notation) and by their
   names.
   The location of the pattern or constant within a term

   :n:`@one_pattern`
      Search for objects whose type contains a subterm matching the
      pattern :n:`@one_pattern`.  Holes of the pattern are indicated by
      `_` or :n:`?@ident`.  If the same :n:`?@ident` occurs more than
      once in the pattern, all occurrences in the subterm must be
      identical.  See :ref:`this example <search-pattern>`.

   :n:`@string {? % @scope_key }`
      - If :n:`@string` is a substring of a valid identifier and no
        :n:`% @scope_key` is provided, search for objects whose name
        contains :n:`@string`.  See :ref:`this example
        <search-part-ident>`.

      - Otherwise, search for objects
        whose type contains the reference that this string,
        interpreted as a notation, is attached to (as described in
        :n:`@reference`).  See :ref:`this example <search-by-notation>`.

     .. note::

        To refer to a string used in a notation that is a substring of a valid identifier,
        put it between single quotes or explicitly provide a scope.
        See :ref:`this example <search-disambiguate-notation>`.

   :n:`hyp:`
      The provided pattern or reference is matched against any subterm
      of an hypothesis of the type of the objects.  See :ref:`this
      example <search-hyp>`.

   :n:`headhyp:`
      The provided pattern or reference is matched against the
      subterms in head position (any partial applicative subterm) of
      the hypotheses of the type of the objects.  See :ref:`the
      previous example <search-hyp>`.

   :n:`concl:`
      The provided pattern or reference is matched against any subterm
      of the conclusion of the type of the objects.  See :ref:`this
      example <search-concl>`.

   :n:`headconcl:`
      The provided pattern or reference is matched against the
      subterms in head position (any partial applicative subterm) of
      the conclusion of the type of the objects.  See :ref:`the
      previous example <search-concl>`.

   :n:`head:`
      This is simply the union between `headconcl:` and `headhyp:`.

   :n:`is: @logical_kind`
      .. insertprodn logical_kind logical_kind

      .. prodn::
         logical_kind ::= {| @thm_token | @assumption_token }
         | {| Definition | Example | Context | Primitive | Symbol }
         | {| Coercion | Instance | Scheme | Canonical | SubClass }
         | {| Fixpoint | CoFixpoint | Field | Method }

      Filters objects by the keyword that was used to define them
      (`Theorem`, `Lemma`, `Axiom`, `Variable`, `Context`,
      `Primitive`...) or its status (`Coercion`, `Instance`, `Scheme`,
      `Canonical`, `SubClass`, `Field` for record fields, `Method` for class
      fields).  Note that `Coercion`\s, `Canonical Structure`\s, `Instance`\s and `Scheme`\s can be
      defined without using those keywords.  See :ref:`this example <search-by-keyword>`.

   Additional clauses:

   * :n:`{| inside | in } {+ @qualid }` - limit the search to the specified modules
   * :n:`outside {+ @qualid }` - exclude the specified modules from the search

   .. exn:: Module/section @qualid not found.

      There is no constant in the environment named :n:`@qualid`, where :n:`@qualid`
      is in an `inside` or `outside` clause.

   .. _search-pattern:

   .. example:: Searching for a pattern

      .. rocqtop:: none reset extra-stdlib

         From Stdlib Require Import PeanoNat.

      We can repeat meta-variables to narrow down the search.  Here,
      we are looking for commutativity lemmas.
      The following example requires the Stdlib library.

      .. rocqtop:: all

         Search (_ ?n ?m = _ ?m ?n).

   .. _search-part-ident:

   .. example:: Searching for part of an identifier

      .. rocqtop:: all reset

         Search "_assoc".

   .. _search-by-notation:

   .. example:: Searching for a reference by notation

      .. rocqtop:: all reset

         Search "+".

   .. _search-disambiguate-notation:

   .. example:: Disambiguating between part of identifier and notation

      The following example requires the Stdlib library.

      .. rocqtop:: none reset extra-stdlib

         From Stdlib Require Import PeanoNat.

      In this example, we show two ways of searching for all the
      objects whose type contains `Nat.modulo` but which do not
      contain the substring "mod".

      .. rocqtop:: all extra-stdlib

         Search "'mod'" -"mod".
         Search "mod"%nat -"mod".

   .. _search-hyp:

   .. example:: Search in hypotheses

      The following search shows the objects whose type contains
      `bool` in an hypothesis as a strict subterm only:

      .. rocqtop:: none reset

         Add Search Blacklist "internal_".

      .. rocqtop:: all

         Search hyp:bool -headhyp:bool.

   .. _search-concl:

   .. example:: Search in conclusion

      The following search shows the objects whose type contains `bool`
      in the conclusion as a strict subterm only:

      .. rocqtop:: all

         Search concl:bool -headconcl:bool.

   .. _search-by-keyword:

   .. example:: Search by keyword or status

      The following search shows the definitions whose type is a `nat`
      or a function which returns a `nat` and the lemmas about `+`:

      .. rocqtop:: all reset

         Search [ is:Definition headconcl:nat | is:Lemma (_ + _) ].

      The following search shows the instances whose type includes the
      classes `Reflexive` or `Symmetric`:

      .. rocqtop:: none reset

         Require Import Morphisms.

      .. rocqtop:: all

         Search is:Instance [ Reflexive | Symmetric ].

      The following search outputs operations on `nat` defined in the
      prelude either with the `Definition` or `Fixpoint` keyword:

      .. rocqtop:: all reset

         Search (nat -> nat -> nat) -bool [ is:Definition | is:Fixpoint ].

.. cmd:: SearchPattern @one_pattern {? {| inside | in | outside } {+ @qualid } }

   Displays the name and type of all hypotheses of the
   selected goal (if any) and theorems of the current context
   ending with :n:`{? forall {* @binder }, } {* P__i -> } C` that match the pattern
   :n:`@one_pattern`.

   See :cmd:`Search` for an explanation of the `inside`/`in`/`outside` clauses.

   .. example:: :cmd:`SearchPattern` examples

      The following example requires the Stdlib library.

      .. rocqtop:: in reset extra-stdlib

         From Stdlib Require Import Arith.

      .. rocqtop:: all extra-stdlib

         SearchPattern (_ + _ = _ + _).
         SearchPattern (nat -> bool).
         SearchPattern (forall l : list _, _ l l).

      .. rocqtop:: all extra-stdlib

         SearchPattern (?X1 + _ = _ + ?X1).

.. cmd:: SearchRewrite @one_pattern {? {| inside | in | outside } {+ @qualid } }

   Displays the name and type of all hypotheses of the
   selected goal (if any) and theorems of the current context that have the form
   :n:`{? forall {* @binder }, } {* P__i -> } LHS = RHS` where :n:`@one_pattern`
   matches either `LHS` or `RHS`.

   See :cmd:`Search` for an explanation of the `inside`/`in`/`outside` clauses.

   .. example:: :cmd:`SearchRewrite` examples

      The following example requires the Stdlib library.

      .. rocqtop:: in reset extra-stdlib

         From Stdlib Require Import Arith.

      .. rocqtop:: all extra-stdlib

         SearchRewrite (_ + _ + _).

.. table:: Search Blacklist @string

   This :term:`table` specifies a set of strings used to exclude lemmas from the results of :cmd:`Search`,
   :cmd:`SearchPattern` and :cmd:`SearchRewrite` queries.  A lemma whose
   fully qualified name contains any of the strings will be excluded from the
   search results.  The default blacklisted substrings are ``_subterm``, ``_subproof`` and
   ``Private_``.

   Use the :cmd:`Add` and :cmd:`Remove` commands to update the set of
   blacklisted strings.

.. flag:: Search Output Name Only

   This :term:`flag` restricts the output of search commands to identifier names;
   turning it on causes invocations of :cmd:`Search`,
   :cmd:`SearchPattern`, :cmd:`SearchRewrite` etc. to omit types from their
   output, printing only identifiers.

.. _requests-to-the-environment:

Requests to the environment
-------------------------------

.. cmd:: Print Assumptions @reference

   Displays all the assumptions (axioms, parameters and
   variables) a theorem or definition depends on.

   The message "Closed under the global context" indicates that the theorem or
   definition has no dependencies.

.. cmd:: Print Opaque Dependencies @reference

   Displays the assumptions and opaque constants that :n:`@reference` depends on.

.. cmd:: Print Transparent Dependencies @reference

   Displays the assumptions and  transparent constants that :n:`@reference` depends on.

.. cmd:: Print All Dependencies @reference

   Displays all the assumptions and constants :n:`@reference` depends on.

.. cmd:: Locate @reference

   .. insertprodn reference reference

   .. prodn::
      reference ::= @qualid
      | @string {? % @scope_key }

   Displays the full name of objects from Rocq's various qualified namespaces
   such as terms, modules and Ltac, thereby showing the module they are defined
   in.  It also displays notation definitions.

   Note that objects are reported only when the module containing them has
   been loaded, such as through a :cmd:`Require` command.  Notation definitions
   are reported only when the containing module has been imported
   (e.g. with :cmd:`Require Import` or :cmd:`Import`).

   Objects defined with commands such as :cmd:`Definition`, :cmd:`Parameter`,
   :cmd:`Record`, :cmd:`Theorem` and their numerous variants are shown
   as `Constant` in the output.

   :n:`@qualid`
     refers to object names that end with :n:`@qualid`.

   :n:`@string {? % @scope_key }`
     refers to definitions of notations.  :n:`@string`
     can be a single token in the notation such as "`->`" or a pattern that matches the
     notation.  See :ref:`locating-notations`.

     :n:`% @scope_key`, if present, limits the reference to the scope bound to the delimiting
     key :n:`@scope_key`, such as, for example, :n:`%nat`.  (see Section
     :ref:`LocalInterpretationRulesForNotations`)

   .. todo somewhere we should list all the qualified namespaces

.. cmd:: Locate Term @reference

   Like :cmd:`Locate`, but limits the search to terms

.. cmd:: Locate Module @qualid

   Like :cmd:`Locate`, but limits the search to modules

.. cmd:: Locate Ltac @qualid

   Like :cmd:`Locate`, but limits the search to Ltac tactics

.. cmd:: Locate Ltac2 @qualid

   Like :cmd:`Locate`, but limits the search to Ltac2 tactics.

.. cmd:: Locate Library @qualid

   Displays the full name, status and file system path of the module :n:`@qualid`, whether loaded or not.

.. cmd:: Locate File @string

   Displays the file system path of the file ending with :n:`@string`.
   Typically, :n:`@string` has a suffix such as ``.cmo`` or ``.vo`` or ``.v`` file, such as :n:`Nat.v`.

      .. todo: also works for directory names such as "Data" (parent of Nat.v)
         also "Data/Nat.v" works, but not a substring match

.. example:: Locate examples

   .. rocqtop:: all

      Locate nat.
      Locate Datatypes.O.
      Locate Init.Datatypes.O.
      Locate Stdlib.Init.Datatypes.O.
      Locate I.Dont.Exist.

.. _printing-flags:

Printing flags
-------------------------------

.. flag:: Fast Name Printing

   When this :term:`flag` is turned on, Rocq uses an asymptotically faster algorithm for the
   generation of unambiguous names of bound variables while printing terms.
   While faster, it is also less clever and results in a typically less elegant
   display, e.g. it will generate more names rather than reusing certain names
   across subterms. This flag is not enabled by default, because as Ltac
   observes bound names, turning it on can break existing proof scripts.


.. _loading-files:

Loading files
-----------------

Rocq offers the possibility of loading different parts of a whole
development stored in separate files. Their contents will be loaded as
if they were entered from the keyboard. This means that the loaded
files are text files containing sequences of commands for Rocq's
toplevel. This kind of file is called a *script* for Rocq. The standard
(and default) extension of Rocq's script files is .v.


.. cmd:: Load {? Verbose } {| @string | @ident }

   Loads a file.  If :n:`@ident` is specified, the command loads a file
   named :n:`@ident.v`, searching successively in
   each of the directories specified in the :term:`load path`. (see Section
   :ref:`logical-paths-load-path`)

   If :n:`@string` is specified, it must specify a complete filename.
   `~` and .. abbreviations are
   allowed as well as shell variables. If no extension is specified, Rocq
   will use the default extension ``.v``.

   Files loaded this way can't leave proofs open, nor can :cmd:`Load`
   be used inside a proof.

   We discourage the use of :cmd:`Load`; use :cmd:`Require` instead.
   :cmd:`Require` loads `.vo` files that were previously
   compiled from `.v` files.

   :n:`Verbose` displays the Rocq output for each command and tactic
   in the loaded file, as if the commands and tactics were entered interactively.

   .. exn:: Can’t find file @ident on loadpath.
      :undocumented:

   .. exn:: Load is not supported inside proofs.
      :undocumented:

   .. exn:: Files processed by Load cannot leave open proofs.
      :undocumented:

.. _compiled-files:

Compiled files
------------------

This section describes the commands used to load compiled files (see
Chapter :ref:`therocqcommands` for documentation on how to compile a file). A compiled
file is a particular case of a module called a *library file*.

.. cmd:: {? From @dirpath } Require {? {| Import | Export } {? @import_categories } } {+ @filtered_import }
   :name: From … Require; Require; Require Import; Require Export

   .. insertprodn dirpath dirpath

   .. prodn::
      dirpath ::= {* @ident . } @ident

   Loads compiled files into the Rocq environment. For the first
   :n:`@qualid` in each :n:`@filtered_import`, the command looks in the
   :term:`load path` for a compiled file :n:`@ident.vo` whose
   :term:`logical name` has the form :n:`@dirpath.{* @ident__implicit. }@qualid`
   (if :n:`From @dirpath` is given) or :n:`{* @ident__implicit. }@qualid` (if
   the optional `From` clause is absent). :n:`{* @ident__implicit. }` represents
   the parts of the fully qualified name that are implicit.  For example,
   `From Stdlib Require Nat` loads `Stdlib.Init.Nat` and `Init` is implicit.
   :n:`@ident` is the final component of the :n:`@qualid`.

   If a file is found, its logical name must be the same as the one
   used to compile the file. Then the file is loaded as well as all
   the files it depends on (recursively). All the files must have
   been compiled with the same version of Rocq.

   * :n:`Import` - additionally does an :cmd:`Import` on the loaded module,
     making components defined in the module available by their short names
   * :n:`Export` - additionally does an :cmd:`Export` on the loaded module,
     making components defined in the module available by their short names
     *and* marking them to be exported by the current module

   If the required file has already been loaded, it is not
   reloaded. If :n:`Import` or :n:`Export` are present, the command also does
   the equivalent of the :cmd:`Import` or :cmd:`Export` commands.

   A single file can be loaded with several variations of the `Require` command.
   For example, the ``-Q path Lib`` command line parameter associates the file
   ``path/Foo/File.vo`` with the logical name ``Lib.Foo.File``.  It allows this
   file to be loaded through :n:`Require Lib.Foo.File`, :n:`From Lib Require Foo.File`,
   :n:`From Lib Require File` or :n:`From Lib.Foo Require File`.  The `-R path Lib`
   command line parameter allows loading the file with the additional alternatives
   :n:`Require Foo.File` and :n:`Require File`  In particular,
   `From` is useful to ensure that the file comes from a particular
   package or subpackage.  Use of `-Q` is better for avoiding ambiguous
   path names.

   Exact matches are preferred when looking for a file with the logical name
   :n:`@dirpath.{* @ident__implicit. }@qualid` or
   :n:`{* @ident__implicit. }@qualid`
   (that is, matches where the implicit part is empty). If the name exactly
   matches in multiple `-R` or `-Q` options, the file corresponding to the last
   `-R` or `-Q` specified is used.  (In :cmd:`Print LoadPath`, that's the first
   match from the top.)

   If there is no exact match, the
   matches from the last `-R` or `-Q` are selected. If this
   results in a unique match, the corresponding file is selected. If
   this results in several matches, it is an error. The difference
   between the `-R` and the `-Q` option is that non-exact matches are
   allowed for `-Q` only if `From` is present.  Matching is done when the script
   is compiled or processed rather than when its .vo file is loaded.  .vo files use
   fully-qualified names.

   We recommend you use `-R` only to refer to files in the same package.  Use `-Q`
   (if necessary) to refer to files in a different package.

   .. exn:: Cannot load @qualid: no physical path bound to @dirpath.
      :undocumented:

   .. exn:: Cannot find library foo in loadpath.

      The command did not find the
      file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
      directory which is not in your :term:`load path`.

   .. exn:: Required library @qualid matches several files in path (found file__1.vo, file__2.vo, ...).

      The file to load must be required with a more discriminating
      suffix, or, at worst, with its full logical name.

   .. exn:: Compiled library @ident.vo makes inconsistent assumptions over library @qualid.

      The command tried to load library file :n:`@ident`.vo that
      depends on some specific version of library :n:`@qualid` which is not the
      one already loaded in the current Rocq session. Probably :n:`@ident.v` was
      not properly recompiled with the last version of the file containing
      module :token:`qualid`.

   .. exn:: Bad magic number.

      The file :n:`@ident.vo` was found but either it is not a
      Rocq compiled module, or it was compiled with an incompatible
      version of Rocq.

   .. exn:: The file @ident.vo contains library @qualid__1 and not library @qualid__2.

      The library :n:`@qualid__2` is indirectly required by a :cmd:`Require`.
      The :term:`load path` maps :n:`@qualid__2` to :n:`@ident.vo`,
      which was compiled using a load path that bound it to :n:`@qualid__1`.  Usually
      the appropriate solution is to recompile :n:`@ident.v` using the correct
      :term:`load path`.

   .. warn:: Require inside a module is deprecated and strongly discouraged. You can Require a module at toplevel and optionally Import it inside another one.

      Note that the :cmd:`Import` and :cmd:`Export` commands can be used inside modules.

      .. seealso:: Chapter :ref:`therocqcommands`

.. cmd:: Print Libraries

   This command displays the list of library files loaded in the
   current Rocq session.

.. cmd:: Declare ML Module {+ @string }

   Loads OCaml plugins and their dependencies dynamically.  The :n:`@string`
   arguments must be valid `findlib <http://projects.camlcity.org/projects/findlib.html>`_
   plugin names, for example ``rocq-runtime.plugins.ltac``.

   Effects (such as adding new commands) from the explicitly requested
   plugin are activated, but effects from implicitly loaded
   dependencies are not activated.

   The first component of the plugin name is a package name that has to
   be in scope of ``findlib``'s' search path. One can see the paths
   explored by ``findlib`` by running ``ocamlfind printconf`` and get
   the list of available libraries by running ``ocamlfind list | grep
   coq`` (Coq libraries are typically named ``coq-something``).

   This command is reserved for plugin developers, who should provide
   a ``.v`` file containing the command. Users of the plugin will
   usually require the resulting ``.vo`` file which will then
   transitively load the required plugin.

   If you are writing a plugin, you thus need to generate the right
   metadata so ``findlib`` can locate your plugin. This usually involves
   generating some kind of ``META`` file and placing it in a place where
   ``findlib`` can see it. Different build systems provide different
   helpers to do this: see :ref:`here for rocq makefile <rocq_makefile>`,
   and :ref:`here for Dune <building_dune>`.

   This command supports the :attr:`local` attribute.  If present,
   the listed files are not exported, even if they're outside a section.

   .. exn:: File not found on loadpath: @string.

      ``findlib`` is not able to find the plugin name. Possible reasons
      are:

      * The plugin does not exist or is misspelled. You can get the list
        of available libraries by running ``ocamlfind list | grep coq``.
      * The metadata for ``findlib`` has not been set properly (see
        above).

   .. exn:: Dynlink error: execution of module initializers in the
            shared library failed: Coq Error: @string is not a valid
            plugin name anymore. Plugins should be loaded using their
            public name according to findlib, for example
            package-name.foo and not foo_plugin.

      The plugin declaration in some ``.mlg`` file does not match the
      ``findlib`` plugin name. In the example of
      ``rocq-runtime.plugins.ltac``, one has to write ``DECLARE PLUGIN
      "rocq-runtime.plugins.ltac"``.

.. cmd:: Print ML Modules

   Print the name of all findlib libraries loaded with
   :cmd:`Declare ML Module`.

Load paths
----------

.. versionchanged:: 8.18

   Commands to manage :term:`load paths <load path>` within Rocq have been
   removed. Load paths can be managed using Rocq command line options or
   enviroment variables (see :ref:`logical-paths-load-path`).

.. cmd:: Print LoadPath {? @dirpath }

   Displays the current Rocq :term:`load path`.  If :n:`@dirpath` is specified,
   displays only the paths that extend that prefix.  In the output,
   the logical path `<>` represents an empty logical path.

.. cmd:: Print ML Path

   Displays the current OCaml loadpath, as provided by the
   :ref:`command line option <command-line-options>` :n:`-I @string`
   (cf. :cmd:`Declare ML Module`).

.. _extra_dependencies:

Extra Dependencies
------------------

Dependencies on external files, i.e. non ``.v`` files, can be declared as
follows:

.. cmd:: From @dirpath Extra Dependency @string {? as @ident }
   :name: From … Dependency

   Adds an additional dependency of the current `.v`  file on an external file.  This
   information is included in the ``rocq dep`` tool generated list of dependencies.
   The file name :n:`@string` must exist relative to one of the top directories
   associated with :n:`@dirpath`.  :n:`@string` can include directory separators
   (``/``) to select a file in a subdirectory.
   Path elements in :n:`@string` must be valid Rocq identifiers, e.g. they cannot
   contain characters such as ``-`` or ``,``.  See :ref:`lexical-conventions`.

When :n:`@ident` is provided, that name can be used by OCaml code, typically
in a plugin, to access the full path of the external file via the API
``ComExtraDeps.query_extra_dep``.

   .. warn:: File ... found twice in ...

      The file is found in more than once in the top directories
      associated with the given :n:`@dirpath`. In this case the first occurrence
      is selected.

.. _backtracking_subsection:

Backtracking
------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a Rocq file loaded via
``Load`` or compiled by ``rocq compile``.


.. cmd:: Reset @ident

   This command removes all the objects in the environment since :n:`@ident`
   was introduced, including :n:`@ident`. :n:`@ident` may be the name of a defined or
   declared object as well as the name of a section. One cannot reset
   over the name of a module or of an object inside a module.

.. cmd:: Reset Initial

   Goes back to the initial state, just after the start
   of the interactive session.


.. cmd:: Back {? @natural }

   Undoes all the effects of the last :n:`@natural @sentence`\s.  If
   :n:`@natural` is not specified, the command undoes one sentence.
   Sentences read from a `.v` file via a :cmd:`Load` are considered a
   single sentence.  While :cmd:`Back` can undo tactics and commands executed
   within proof mode, once you exit proof mode, such as with :cmd:`Qed`, all
   the statements executed within are thereafter considered a single sentence.
   :cmd:`Back` immediately following :cmd:`Qed` gets you back to the state
   just after the statement of the proof.

   .. exn:: Invalid backtrack.

      The user wants to undo more commands than available in the history.

.. cmd:: BackTo @natural

   This command brings back the system to the state labeled :n:`@natural`,
   forgetting the effect of all commands executed after this state. The
   state label is an integer which grows after each successful command.
   It is displayed in the prompt when in -emacs mode. Just as :cmd:`Back` (see
   above), the :cmd:`BackTo` command now handles proof states. For that, it may
   have to undo some extra commands and end on a state :n:`@natural′ ≤ @natural` if
   necessary.

.. _quitting-and-debugging:

Quitting and debugging
--------------------------

.. cmd:: Quit

   Causes Rocq to exit.  Valid only in `rocq repl-with-drop`.


.. cmd:: Drop

   This command temporarily enters the OCaml toplevel.
   It is a debug facility used by Rocq's implementers.  Valid only in `rocq repl-with-drop`.
   The OCaml command:

   ::

      #use "include";;

   adds the right loadpaths and loads some toplevel printers for all
   abstract types of Rocq- section_path, identifiers, terms, judgments, ….
   You can also use the file base_include instead, that loads only the
   pretty-printers for section_paths and identifiers. You can return back
   to Rocq with the command:

   ::

      go();;

.. cmd:: Time @sentence

   Executes :n:`@sentence` and displays the
   time needed to execute it.


.. cmd:: Instructions @sentence

   Executes :n:`@sentence` and displays the number of CPU instructions needed
   to execute it. This command is currently only supported on Linux systems,
   but does not fail on unsupported sustems, where it instead prints an error
   message in the place of the instruction count.


.. cmd:: Profile {? @string } @sentence

   Executes :n:`@sentence` and displays profiling information. If
   :n:`@string` is given, a full trace is written to
   ":n:`@string`.json".

   If :n:`@string` is a relative filename, it refers to the directory
   specified by the :ref:`command line option <command-line-options>`
   `-output-directory`, if set and otherwise, the current directory.
   Use :cmd:`Pwd` to display the current directory.


.. cmd:: Redirect @string @sentence

   Executes :n:`@sentence`, redirecting its
   output to the file ":n:`@string`.out".

   If :n:`@string` is a relative filename, it refers to the directory
   specified by the command line option `-output-directory`, if set
   (see :ref:`command-line-options`) and otherwise, the current
   directory. Use :cmd:`Pwd` to display the current directory.

.. cmd:: Timeout @natural @sentence

   Executes :n:`@sentence`. If the operation
   has not terminated after :n:`@natural` seconds, then it is interrupted and an error message is
   displayed.

   .. opt:: Default Timeout @natural

      When this :term:`option` is set, each :n:`@sentence` is treated
      as if it was prefixed with :cmd:`Timeout` :n:`@natural`, except
      for :cmd:`Timeout` commands themselves.  If unset, no timeout is
      applied.


.. cmd:: Fail @sentence

   For debugging scripts, sometimes it is desirable to know whether a
   command or a tactic fails. If :n:`@sentence` fails, then
   :n:`Fail @sentence` succeeds (except for
   anomalies or for critical failures such as "stack overflow"), without changing the
   proof state.  In interactive mode, the system prints a message
   confirming the failure.

   .. exn:: The command has not failed!

      If the given :n:`@command` succeeds, then :n:`Fail @sentence`
      fails with this error message.

.. cmd:: Succeed @sentence

   If :n:`@sentence` succeeds, then :n:`Succeed @sentence` succeeds without changing the
   proof state.  If :n:`@sentence` fails, then :n:`Succeed @sentence` fails showing the error
   message for :n:`@sentence`.
   In interactive mode, the system prints the message :n:`The command has succeeded and its effects have been reverted.` confirming the success.
   This command can be useful for writing tests.

.. note::

   :cmd:`Time`, :cmd:`Redirect`, :cmd:`Timeout`, :cmd:`Fail` and :cmd:`Succeed` are
   :production:`control_command`\s. For these commands, attributes and goal
   selectors, when specified, are part of the :n:`@sentence` argument, and thus come after
   the control command prefix and before the inner command or tactic. For
   example: `Time #[ local ] Definition foo := 0.` or `Fail Timeout 10 all: auto.`

.. _controlling-display:

Controlling display
-----------------------

.. flag:: Silent

   This :term:`flag` controls the normal displaying.

.. opt:: Warnings "{+, {? {| - | + } } @ident }"

   This :term:`option` configures the display of warnings. The :n:`@ident`\s
   are warning or category names. Adding `-` in front of a warning or category
   disables it, adding `+` makes it an error.

   Warning name and categories are printed between brackets when the warning
   is displayed (the warning name appears first). Warnings can belong to
   multiple categories. The special category `all` contains all warnings, and
   the special category `default` contains the warnings enabled by default.

   Rocq defines a set of core warning categories, which may be extended by
   plugins, so this list is not exhaustive. The core categories are:
   `automation`,
   `bytecode-compiler`,
   `coercions`,
   `deprecated`,
   `extraction`,
   `filesystem`,
   `fixpoints`,
   `fragile`,
   `funind`,
   `implicits`,
   `ltac`,
   `ltac2`,
   `native-compiler`,
   `numbers`,
   `parsing`,
   `pedantic`,
   `records`,
   `rewrite-rules`,
   `ssr`,
   `syntax`,
   `tactics`,
   `user-warn`,
   `vernacular`.

   .. This list is from lib/cWarnings.ml

   The flags are
   interpreted from left to right, so in case of an overlap, the flags on the
   right have higher priority, meaning that `A,-A` is equivalent to `-A`.

   See also the :attr:`warnings` attribute, which can be used to
   configure the display of warnings for a single command.

.. opt:: Debug "{+, {? - } @ident }"

   This :term:`option` configures the display of debug messages. Each :n:`@ident` enables debug messages
   for that component, while  :n:`-@ident` disables messages for the component.
   ``all`` activates or deactivates all other components.  ``backtrace`` controls printing of
   error backtraces.

   :cmd:`Test` `Debug` displays the list of components and their enabled/disabled state.

.. opt:: Printing Width @natural

   This :term:`option` sets which left-aligned part of the width of the screen is used
   for display. At the time of writing this documentation, the default value
   is 78.

.. opt:: Printing Depth @natural

   This :term:`option` controls the nesting depth of the formatter used for pretty-
   printing. Beyond this depth, display of subterms is replaced by dots. At the
   time of writing this documentation, the default value is 50.

.. flag:: Printing Compact Contexts

   This :term:`flag` controls the compact display mode for goals contexts. When on,
   the printer tries to reduce the vertical size of goals contexts by putting
   several variables (even if of different types) on the same line provided it
   does not exceed the printing width (see :opt:`Printing Width`). At the time
   of writing this documentation, it is off by default.

.. flag:: Printing Unfocused

   This :term:`flag` controls whether unfocused goals are displayed. Such goals are
   created by focusing other goals with :ref:`bullets <bullets>` or
   :ref:`curly braces <curly-braces>`. It is off by default.

.. flag:: Printing Dependent Evars Line

   This :term:`flag` controls the printing of the “(dependent evars: …)” information
   after each tactic.  The information is used by the Prooftree tool in Proof
   General. (https://askra.de/software/prooftree)

.. extracted from Gallina extensions chapter

.. _printing_constructions_full:

Printing constructions in full
------------------------------

.. flag:: Printing All

   Coercions, implicit arguments, the type of pattern matching, but also
   notations (see :ref:`syntax-extensions-and-notation-scopes`) can obfuscate the behavior of some
   tactics (typically the tactics applying to occurrences of subterms are
   sensitive to the implicit arguments). Turning this :term:`flag` on
   deactivates all high-level printing features such as coercions,
   implicit arguments, returned type of pattern matching, notations and
   various syntactic sugar for pattern matching or record projections.
   Otherwise said, :flag:`Printing All` includes the effects of the flags
   :flag:`Printing Implicit`, :flag:`Printing Coercions`, :flag:`Printing Synth`,
   :flag:`Printing Projections`, and :flag:`Printing Notations`. To reactivate
   the high-level printing features, use the command ``Unset Printing All``.

   .. note:: In some cases, setting :flag:`Printing All` may display terms
      that are so big they become very hard to read.  One technique to work around
      this is use :cmd:`Undelimit Scope` and/or :cmd:`Close Scope` to turn off the
      printing of notations bound to particular scope(s).  This can be useful when
      notations in a given scope are getting in the way of understanding
      a goal, but turning off all notations with :flag:`Printing All` would make
      the goal unreadable.

      .. see a contrived example here: https://github.com/coq/coq/pull/11718#discussion_r415481854

.. _controlling-typing-flags:

Controlling Typing Flags
----------------------------

.. flag:: Guard Checking

   This :term:`flag` can be used to enable/disable the guard checking of
   fixpoints. Warning: this can break the consistency of the system, use at your
   own risk. Decreasing argument can still be specified: the decrease is not checked
   anymore but it still affects the reduction of the term. Unchecked fixpoints are
   printed by :cmd:`Print Assumptions`.

.. attr:: bypass_check(guard{? = {| yes | no } })
   :name: bypass_check(guard)

   This :term:`boolean attribute` is similar to the :flag:`Guard Checking` flag, but on a per-declaration
   basis. Disable guard checking locally with ``bypass_check(guard)``.

.. flag:: Positivity Checking

   This :term:`flag` can be used to enable/disable the positivity checking of inductive
   types and the productivity checking of coinductive types. Warning: this can
   break the consistency of the system, use at your own risk. Unchecked
   (co)inductive types are printed by :cmd:`Print Assumptions`.

.. attr:: bypass_check(positivity{? = {| yes | no } })
   :name: bypass_check(positivity)

   This :term:`boolean attribute` is similar to the :flag:`Positivity Checking` flag, but on a per-declaration basis.
   Disable positivity checking locally with ``bypass_check(positivity)``.

.. flag:: Universe Checking

   This :term:`flag` can be used to enable/disable the checking of universes, providing a
   form of "type in type".  Warning: this breaks the consistency of the system, use
   at your own risk.  Constants relying on "type in type" are printed by
   :cmd:`Print Assumptions`. It has the same effect as `-type-in-type` command line
   argument (see :ref:`command-line-options`).

.. attr:: bypass_check(universes{? = {| yes | no } })
   :name: bypass_check(universes)

   This :term:`boolean attribute` is similar to the :flag:`Universe Checking` flag, but on a per-declaration basis.
   Disable universe checking locally with ``bypass_check(universes)``.

.. cmd:: Print Typing Flags

   Print the status of the three typing flags: guard checking, positivity checking
   and universe checking.

.. example::

   .. rocqtop:: all reset

        Unset Guard Checking.

        Print Typing Flags.

        Fixpoint f (n : nat) : False
          := f n.

        Fixpoint ackermann (m n : nat) {struct m} : nat :=
          match m with
          | 0 => S n
          | S m =>
            match n with
            | 0 => ackermann m 1
            | S n => ackermann m (ackermann (S m) n)
            end
          end.

        Print Assumptions ackermann.

   Note that the proper way to define the Ackermann function is to use
   an inner fixpoint:

   .. rocqtop:: all reset

        Fixpoint ack m :=
          fix ackm n :=
          match m with
          | 0 => S n
          | S m' =>
            match n with
            | 0 => ack m' 1
            | S n' => ack m' (ackm n')
            end
          end.

Typing flags may not be changed while inside sections.

.. _internal-registration-commands:

Internal registration commands
--------------------------------

Due to their internal nature, the commands that are presented in this section
are not for general use. They are meant to appear only in standard libraries and
in support libraries of plug-ins.

.. _exposing-constants-to-ocaml-libraries:

Exposing constants to OCaml libraries
```````````````````````````````````````

.. cmd:: Register @qualid__1 as @qualid__2

   Makes the constant :n:`@qualid__1` accessible to OCaml libraries under
   the name :n:`@qualid__2`.  The constant can then be dynamically located
   in OCaml code by
   calling :n:`Rocqlib.lib_ref "@qualid__2"`.  The OCaml code doesn't need
   to know where the constant is defined (what file, module, library, etc.).

   As a special case, when the first segment of :n:`@qualid__2` is :g:`kernel`,
   the constant is exposed to the kernel. For instance, the `PrimInt63` module
   features the following declaration:

   This command supports attributes :attr:`local`, :attr:`export` and :attr:`global`.
   The default is :attr:`global`, even inside sections.

   .. rocqdoc::

      Register bool as kernel.ind_bool.

   This makes the kernel aware of the `bool` type, which is used, for example,
   to define the return type of the :g:`#int63_eq` primitive.

   .. seealso:: :ref:`primitive-integers`

.. cmd:: Print Registered

   List the currently registered constants.

.. cmd:: Register Scheme @qualid__1 as @qualid__2 for @qualid__3

   Make the constant :n:`@qualid__1` accessible to the "scheme"
   mechanism for scheme kind :n:`@qualid__2` and inductive
   :n:`@qualid__3`.

   This command supports attributes :attr:`local`, :attr:`export` and :attr:`global`.
   The default is :attr:`global`, even inside sections.

.. cmd:: Print Registered Schemes

   List the currently registered schemes.

   This can be useful to find information about the (currently
   undocumented) scheme kinds.

Inlining hints for the fast reduction machines
``````````````````````````````````````````````

.. cmd:: Register Inline @qualid

   Gives a hint to the reduction machines (VM and native) that
   the body of the constant :n:`@qualid` should be inlined in the generated code.

Registering primitive operations
````````````````````````````````

.. cmd:: Primitive @ident_decl {? : @term } := #@ident

   Makes the primitive type or primitive operator :n:`#@ident` defined in OCaml
   accessible in Rocq commands and tactics.
   For internal use by implementors of Rocq's standard library or standard library
   replacements.  No space is allowed after the `#`.  Invalid values give a syntax
   error.

   For example, the standard library files `PrimInt63.v` and `PrimFloat.v` use :cmd:`Primitive`
   to support, respectively, the features described in :ref:`primitive-integers` and
   :ref:`primitive-floats`.

   The types associated with an operator must be declared to the kernel before declaring operations
   that use the type.  Do this with :cmd:`Primitive` for primitive types and
   :cmd:`Register` with the :g:`kernel` prefix for other types.  For example,
   in `PrimInt63.v`, `#int63_type` must be declared before the associated operations.

   .. exn:: The type @ident must be registered before this construction can be typechecked.
      :undocumented:

      The type must be defined with :cmd:`Primitive` command before this
      :cmd:`Primitive` command (declaring an operation using the type) will succeed.
