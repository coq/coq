.. _vernacularcommands:

Vernacular commands
=============================

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

   .. exn:: Universe instance should have length @num.
      :undocumented:

   .. exn:: This object does not support universe names.
      :undocumented:


.. cmd:: Print All

   This command displays information about the current state of the
   environment, including sections and modules.

.. cmd:: Inspect @num

   This command displays the :n:`@num` last objects of the
   current environment, including sections and modules.

.. cmd:: Print Section @qualid

   Displays the objects defined since the beginning of the section named :n:`@qualid`.

   .. todo: "A.B" is permitted but unnecessary for modules/sections.
      should the command just take an @ident?

Query commands
--------------

Unlike other commands, :production:`query_command`\s may be prefixed with
a goal selector (:n:`@num:`) to specify which goal context it applies to.
If no selector is provided,
the command applies to the current goal.  If no proof is open, then the command only applies
to accessible objects.  (see Section :ref:`invocation-of-tactics`).

.. cmd:: About @reference {? @univ_name_list }

   Displays information about the :n:`@reference` object, which,
   if a proof is open,  may be a hypothesis of the selected goal,
   or an accessible theorem, axiom, etc.:
   its kind (module, constant, assumption, inductive,
   constructor, abbreviation, …), long name, type, implicit arguments and
   argument scopes (as set in the definition of :token:`reference` or
   subsequently with the :cmd:`Arguments` command). It does not print the body of definitions or proofs.

.. cmd:: Check @term

   Displays the type of :n:`@term`. When called in proof mode, the
   term is checked in the local context of the selected goal.

.. cmd:: Eval @red_expr in @term

   Performs the specified reduction on :n:`@term` and displays
   the resulting term with its type. If a proof is open, :n:`@term`
   may reference hypotheses of the selected goal.

   .. seealso:: Section :ref:`performingcomputations`.


.. cmd:: Compute @term

   Evaluates :n:`@term` using the bytecode-based virtual machine.
   It is a shortcut for :cmd:`Eval` :n:`vm_compute in @term`.

   .. seealso:: Section :ref:`performingcomputations`.

.. cmd:: Search {+ @search_query } {? {| inside | outside } {+ @qualid } }

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
      | {? {| head | hyp | concl | headhyp | headconcl } : } @one_term
      | is : @logical_kind

   Searched objects can be filtered by patterns, by the constants they
   contain (identified by their name or a notation) and by their
   names.
   The location of the pattern or constant within a term

   :n:`@one_term`
      Search for objects whose type contains a subterm matching the
      pattern :n:`@one_term`.  Holes of the pattern are indicated by
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
         | {| Definition | Example | Context | Primitive }
         | {| Coercion | Instance | Scheme | Canonical | SubClass }
         | {| Field | Method }

      Filters objects by the keyword that was used to define them
      (`Theorem`, `Lemma`, `Axiom`, `Variable`, `Context`,
      `Primitive`...) or its status (`Coercion`, `Instance`, `Scheme`,
      `Canonical`, `SubClass`, Field` for record fields, `Method` for class
      fields).  Note that `Coercion`\s, `Canonical Structure`\s, Instance`\s and `Scheme`\s can be
      defined without using those keywords.  See :ref:`this example <search-by-keyword>`.

   Additional clauses:

   * :n:`inside {+ @qualid }` - limit the search to the specified modules
   * :n:`outside {+ @qualid }` - exclude the specified modules from the search

   .. exn:: Module/section @qualid not found.

      There is no constant in the environment named :n:`@qualid`, where :n:`@qualid`
      is in an `inside` or `outside` clause.

   .. _search-pattern:

   .. example:: Searching for a pattern

      .. coqtop:: none reset

         Require Import PeanoNat.

      We can repeat meta-variables to narrow down the search.  Here,
      we are looking for commutativity lemmas.

      .. coqtop:: all

         Search (_ ?n ?m = _ ?m ?n).

   .. _search-part-ident:

   .. example:: Searching for part of an identifier

      .. coqtop:: all reset

         Search "_assoc".

   .. _search-by-notation:

   .. example:: Searching for a reference by notation

      .. coqtop:: all reset

         Search "+".

   .. _search-disambiguate-notation:

   .. example:: Disambiguating between part of identifier and notation

      .. coqtop:: none reset

         Require Import PeanoNat.

      In this example, we show two ways of searching for all the
      objects whose type contains `Nat.modulo` but which do not
      contain the substring "mod".

      .. coqtop:: all

         Search "'mod'" -"mod".
         Search "mod"%nat -"mod".

   .. _search-hyp:

   .. example:: Search in hypotheses

      The following search shows the objects whose type contains
      `bool` in an hypothesis as a strict subterm only:

      .. coqtop:: none reset

         Add Search Blacklist "internal_".

      .. coqtop:: all

         Search hyp:bool -headhyp:bool.

   .. _search-concl:

   .. example:: Search in conclusion

      The following search shows the objects whose type contains `bool`
      in the conclusion as a strict subterm only:

      .. coqtop:: all

         Search concl:bool -headconcl:bool.

   .. _search-by-keyword:

   .. example:: Search by keyword or status

      The following search shows the definitions whose type is a `nat`
      or a function which returns a `nat` and the lemmas about `+`:

      .. coqtop:: all reset

         Search [ is:Definition headconcl:nat | is:Lemma (_ + _) ].

      The following search shows the instances whose type includes the
      classes `Reflexive` or `Symmetric`:

      .. coqtop:: none reset

         Require Import Morphisms.

      .. coqtop:: all

         Search is:Instance [ Reflexive | Symmetric ].

.. cmd:: SearchHead @one_term {? {| inside | outside } {+ @qualid } }

   .. deprecated:: 8.12

      Use the `headconcl:` clause of :cmd:`Search` instead.

   Displays the name and type of all hypotheses of the
   selected goal (if any) and theorems of the current context that have the
   form :n:`{? forall {* @binder }, } {* P__i -> } C` where :n:`@one_term`
   matches a subterm of `C` in head position.  For example, a :n:`@one_term` of `f _ b`
   matches `f a b`, which is a subterm of `C` in head position when `C` is `f a b c`.

   See :cmd:`Search` for an explanation of the `inside`/`outside` clauses.

   .. example:: :cmd:`SearchHead` examples

      .. coqtop:: none reset

         Add Search Blacklist "internal_".

      .. coqtop:: all warn

         SearchHead le.
         SearchHead (@eq bool).

.. cmd:: SearchPattern @one_term {? {| inside | outside } {+ @qualid } }

   Displays the name and type of all hypotheses of the
   selected goal (if any) and theorems of the current context
   ending with :n:`{? forall {* @binder }, } {* P__i -> } C` that match the pattern
   :n:`@one_term`.

   See :cmd:`Search` for an explanation of the `inside`/`outside` clauses.

   .. example:: :cmd:`SearchPattern` examples

      .. coqtop:: in

         Require Import Arith.

      .. coqtop:: all

         SearchPattern (_ + _ = _ + _).
         SearchPattern (nat -> bool).
         SearchPattern (forall l : list _, _ l l).

      .. coqtop:: all

         SearchPattern (?X1 + _ = _ + ?X1).

.. cmd:: SearchRewrite @one_term {? {| inside | outside } {+ @qualid } }

   Displays the name and type of all hypotheses of the
   selected goal (if any) and theorems of the current context that have the form
   :n:`{? forall {* @binder }, } {* P__i -> } LHS = RHS` where :n:`@one_term`
   matches either `LHS` or `RHS`.

   See :cmd:`Search` for an explanation of the `inside`/`outside` clauses.

   .. example:: :cmd:`SearchRewrite` examples

      .. coqtop:: in

         Require Import Arith.

      .. coqtop:: all

         SearchRewrite (_ + _ + _).

.. table:: Search Blacklist @string
   :name: Search Blacklist

   Specifies a set of strings used to exclude lemmas from the results of :cmd:`Search`,
   :cmd:`SearchHead`, :cmd:`SearchPattern` and :cmd:`SearchRewrite` queries.  A lemma whose
   fully-qualified name contains any of the strings will be excluded from the
   search results.  The default blacklisted substrings are ``_subterm``, ``_subproof`` and
   ``Private_``.

   Use the :cmd:`Add` and :cmd:`Remove` commands to update the set of
   blacklisted strings.

.. flag:: Search Output Name Only

   This flag restricts the output of search commands to identifier names;
   turning it on causes invocations of :cmd:`Search`, :cmd:`SearchHead`,
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

   Displays the full name of objects from |Coq|'s various qualified namespaces such as terms,
   modules and Ltac, thereby showing the module they are defined in.  It also displays notation definitions.

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

   Like :cmd:`Locate`, but limits the search to tactics

.. cmd:: Locate Library @qualid

   Displays the full name, status and file system path of the module :n:`@qualid`, whether loaded or not.

.. cmd:: Locate File @string

   Displays the file system path of the file ending with :n:`@string`.
   Typically, :n:`@string` has a suffix such as ``.cmo`` or ``.vo`` or ``.v`` file, such as :n:`Nat.v`.

      .. todo: also works for directory names such as "Data" (parent of Nat.v)
         also "Data/Nat.v" works, but not a substring match

.. example:: Locate examples

   .. coqtop:: all

      Locate nat.
      Locate Datatypes.O.
      Locate Init.Datatypes.O.
      Locate Coq.Init.Datatypes.O.
      Locate I.Dont.Exist.

.. _printing-flags:

Printing flags
-------------------------------

.. flag:: Fast Name Printing

   When turned on, |Coq| uses an asymptotically faster algorithm for the
   generation of unambiguous names of bound variables while printing terms.
   While faster, it is also less clever and results in a typically less elegant
   display, e.g. it will generate more names rather than reusing certain names
   across subterms. This flag is not enabled by default, because as Ltac
   observes bound names, turning it on can break existing proof scripts.


.. _loading-files:

Loading files
-----------------

|Coq| offers the possibility of loading different parts of a whole
development stored in separate files. Their contents will be loaded as
if they were entered from the keyboard. This means that the loaded
files are text files containing sequences of commands for |Coq|’s
toplevel. This kind of file is called a *script* for |Coq|. The standard
(and default) extension of |Coq|’s script files is .v.


.. cmd:: Load {? Verbose } {| @string | @ident }

   Loads a file.  If :n:`@ident` is specified, the command loads a file
   named :n:`@ident.v`, searching successively in
   each of the directories specified in the *loadpath*. (see Section
   :ref:`libraries-and-filesystem`)

   If :n:`@string` is specified, it must specify a complete filename.
   `~` and .. abbreviations are
   allowed as well as shell variables. If no extension is specified, |Coq|
   will use the default extension ``.v``.

   Files loaded this way can't leave proofs open, nor can :cmd:`Load`
   be used inside a proof.

   We discourage the use of :cmd:`Load`; use :cmd:`Require` instead.
   :cmd:`Require` loads `.vo` files that were previously
   compiled from `.v` files.

   :n:`Verbose` displays the |Coq| output for each command and tactic
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
Chapter :ref:`thecoqcommands` for documentation on how to compile a file). A compiled
file is a particular case of a module called a *library file*.


.. cmd:: Require {? {| Import | Export } } {+ @qualid }
   :name: Require; Require Import; Require Export

   Loads compiled modules into the |Coq| environment.  For each :n:`@qualid`, which has the form
   :n:`{* @ident__prefix . } @ident`, the command searches for the logical name represented
   by the :n:`@ident__prefix`\s and loads the compiled file :n:`@ident.vo` from the associated
   filesystem directory.

   The process is applied recursively to all the loaded files;
   if they contain :cmd:`Require` commands, those commands are executed as well.
   The compiled files must have been compiled with the same version of |Coq|.
   The compiled files are neither replayed nor rechecked.

   * :n:`Import` - additionally does an :cmd:`Import` on the loaded module, making components defined
     in the module available by their short names
   * :n:`Export` - additionally does an :cmd:`Export` on the loaded module, making components defined
     in the module available by their short names *and* marking them to be exported by the current
     module

   If the required module has already been loaded, :n:`Import` and :n:`Export` make the command
   equivalent to :cmd:`Import` or :cmd:`Export`.

   The loadpath must contain the same mapping used to compile the file
   (see Section :ref:`libraries-and-filesystem`). If
   several files match, one of them is picked in an unspecified fashion.
   Therefore, library authors should use a unique name for each module and
   users are encouraged to use fully-qualified names
   or the :cmd:`From … Require` command to load files.


   .. todo common user error on dirpaths see https://github.com/coq/coq/pull/11961#discussion_r402852390

   .. cmd:: From @dirpath Require {? {| Import | Export } } {+ @qualid }
      :name: From … Require

      Works like :cmd:`Require`, but loads, for each :n:`@qualid`,
      the library whose fully-qualified name matches :n:`@dirpath.{* @ident . }@qualid`
      for some :n:`{* @ident . }`. This is useful to ensure that the :n:`@qualid` library
      comes from a particular package.

   .. exn:: Cannot load @qualid: no physical path bound to @dirpath.
      :undocumented:

   .. exn:: Cannot find library foo in loadpath.

      The command did not find the
      file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
      directory which is not in your LoadPath (see Section :ref:`libraries-and-filesystem`).

   .. exn:: Compiled library @ident.vo makes inconsistent assumptions over library @qualid.

      The command tried to load library file :n:`@ident`.vo that
      depends on some specific version of library :n:`@qualid` which is not the
      one already loaded in the current |Coq| session. Probably :n:`@ident.v` was
      not properly recompiled with the last version of the file containing
      module :token:`qualid`.

   .. exn:: Bad magic number.

      The file :n:`@ident.vo` was found but either it is not a
      |Coq| compiled module, or it was compiled with an incompatible
      version of |Coq|.

   .. exn:: The file @ident.vo contains library @qualid__1 and not library @qualid__2.

      The library :n:`@qualid__2` is indirectly required by a :cmd:`Require` or
      :cmd:`From … Require` command.  The loadpath maps :n:`@qualid__2` to :n:`@ident.vo`,
      which was compiled using a loadpath that bound it to :n:`@qualid__1`.  Usually
      the appropriate solution is to recompile :n:`@ident.v` using the correct loadpath.
      See :ref:`libraries-and-filesystem`.

   .. warn:: Require inside a module is deprecated and strongly discouraged. You can Require a module at toplevel and optionally Import it inside another one.

      Note that the :cmd:`Import` and :cmd:`Export` commands can be used inside modules.

      .. seealso:: Chapter :ref:`thecoqcommands`

.. cmd:: Print Libraries

   This command displays the list of library files loaded in the
   current |Coq| session.

.. cmd:: Declare ML Module {+ @string }

   This commands dynamically loads OCaml compiled code from
   a :n:`.mllib` file.
   It is used to load plugins dynamically.  The
   files must be accessible in the current OCaml loadpath (see the
   command :cmd:`Add ML Path`).  The :n:`.mllib` suffix may be omitted.

   This command is reserved for plugin developers, who should provide
   a .v file containing the command. Users of the plugins will then generally
   load the .v file.

   This command supports the :attr:`local` attribute.  If present,
   the listed files are not exported, even if they're outside a section.

   .. exn:: File not found on loadpath: @string.
      :undocumented:


.. cmd:: Print ML Modules

   This prints the name of all OCaml modules loaded with :cmd:`Declare ML Module`.
   To know from where these module were loaded, the user
   should use the command :cmd:`Locate File`.


.. _loadpath:

Loadpath
------------

Loadpaths are preferably managed using |Coq| command line options (see
Section :ref:`libraries-and-filesystem`) but there remain vernacular commands to manage them
for practical purposes. Such commands are only meant to be issued in
the toplevel, and using them in source files is discouraged.


.. cmd:: Pwd

   This command displays the current working directory.


.. cmd:: Cd {? @string }

   If :n:`@string` is specified, changes the current directory according to :token:`string` which
   can be any valid path.  Otherwise, it displays the current directory.


.. cmd:: Add LoadPath @string as @dirpath

   .. insertprodn dirpath dirpath

   .. prodn::
      dirpath ::= {* @ident . } @ident

   This command is equivalent to the command line option
   :n:`-Q @string @dirpath`. It adds a mapping to the loadpath from
   the logical name :n:`@dirpath` to the file system directory :n:`@string`.

   * :n:`@dirpath` is a prefix of a module name.  The module name hierarchy
     follows the file system hierarchy.  On Linux, for example, the prefix
     `A.B.C` maps to the directory :n:`@string/B/C`.  Avoid using spaces after a `.` in the
     path because the parser will interpret that as the end of a command or tactic.

.. cmd:: Add Rec LoadPath @string as @dirpath

   This command is equivalent to the command line option
   :n:`-R @string @dirpath`. It adds the physical directory string and all its
   subdirectories to the current |Coq| loadpath.


.. cmd:: Remove LoadPath @string

   This command removes the path :n:`@string` from the current |Coq| loadpath.


.. cmd:: Print LoadPath {? @dirpath }

   This command displays the current |Coq| loadpath.  If :n:`@dirpath` is specified,
   displays only the paths that extend that prefix.


.. cmd:: Add ML Path @string

   This command adds the path :n:`@string` to the current OCaml
   loadpath (cf. :cmd:`Declare ML Module`).


.. cmd:: Print ML Path

   This command displays the current OCaml loadpath. This
   command makes sense only under the bytecode version of ``coqtop``, i.e.
   using option ``-byte``
   (cf. :cmd:`Declare ML Module`).


.. _backtracking_subsection:

Backtracking
------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a vernacular file loaded via
``Load`` or compiled by ``coqc``.


.. cmd:: Reset @ident

   This command removes all the objects in the environment since :n:`@ident`
   was introduced, including :n:`@ident`. :n:`@ident` may be the name of a defined or
   declared object as well as the name of a section. One cannot reset
   over the name of a module or of an object inside a module.

   .. exn:: @ident: no such entry.
      :undocumented:

.. cmd:: Reset Initial

   Goes back to the initial state, just after the start
   of the interactive session.


.. cmd:: Back {? @num }

   Undoes all the effects of the last :n:`@num @sentence`\s.  If
   :n:`@num` is not specified, the command undoes one sentence.
   Sentences read from a `.v` file via a :cmd:`Load` are considered a
   single sentence.  While :cmd:`Back` can undo tactics and commands executed
   within proof mode, once you exit proof mode, such as with :cmd:`Qed`, all
   the statements executed within are thereafter considered a single sentence.
   :cmd:`Back` immediately following :cmd:`Qed` gets you back to the state
   just after the statement of the proof.

   .. exn:: Invalid backtrack.

      The user wants to undo more commands than available in the history.

.. cmd:: BackTo @num

   This command brings back the system to the state labeled :n:`@num`,
   forgetting the effect of all commands executed after this state. The
   state label is an integer which grows after each successful command.
   It is displayed in the prompt when in -emacs mode. Just as :cmd:`Back` (see
   above), the :cmd:`BackTo` command now handles proof states. For that, it may
   have to undo some extra commands and end on a state :n:`@num′ ≤ @num` if
   necessary.

.. _quitting-and-debugging:

Quitting and debugging
--------------------------

.. cmd:: Quit

   Causes |Coq| to exit.  Valid only in coqtop.


.. cmd:: Drop

   This command temporarily enters the OCaml toplevel.
   It is a debug facility used by |Coq|’s implementers.  Valid only in the
   bytecode version of coqtop.
   The OCaml command:

   ::

      #use "include";;

   adds the right loadpaths and loads some toplevel printers for all
   abstract types of |Coq|- section_path, identifiers, terms, judgments, ….
   You can also use the file base_include instead, that loads only the
   pretty-printers for section_paths and identifiers. You can return back
   to |Coq| with the command:

   ::

      go();;

   .. warning::

      #. It only works with the bytecode version of |Coq| (i.e. `coqtop.byte`,
         see Section `interactive-use`).
      #. You must have compiled |Coq| from the source package and set the
         environment variable COQTOP to the root of your copy of the sources
         (see Section `customization-by-environment-variables`).


.. cmd:: Time @sentence

   Executes :n:`@sentence` and displays the
   time needed to execute it.


.. cmd:: Redirect @string @sentence

   Executes :n:`@sentence`, redirecting its
   output to the file ":n:`@string`.out".


.. cmd:: Timeout @num @sentence

   Executes :n:`@sentence`. If the operation
   has not terminated after :n:`@num` seconds, then it is interrupted and an error message is
   displayed.

   .. opt:: Default Timeout @num
      :name: Default Timeout

      If set, each :n:`@sentence` is treated as if it was prefixed with :cmd:`Timeout` :n:`@num`,
      except for :cmd:`Timeout` commands themselves.  If unset,
      no timeout is applied.


.. cmd:: Fail @sentence

   For debugging scripts, sometimes it is desirable to know whether a
   command or a tactic fails. If :n:`@sentence` fails, then
   :n:`Fail @sentence` succeeds (except for
   critical errors, such as "stack overflow"), without changing the
   proof state.  In interactive mode, the system prints a message
   confirming the failure.

   .. exn:: The command has not failed!

      If the given :n:`@command` succeeds, then :n:`Fail @sentence`
      fails with this error message.

.. note::

   :cmd:`Time`, :cmd:`Redirect`, :cmd:`Timeout` and :cmd:`Fail` are
   :production:`control_command`\s. For these commands, attributes and goal
   selectors, when specified, are part of the :n:`@sentence` argument, and thus come after
   the control command prefix and before the inner command or tactic. For
   example: `Time #[ local ] Definition foo := 0.` or `Fail Timeout 10 all: auto.`

.. _controlling-display:

Controlling display
-----------------------

.. flag:: Silent

   This flag controls the normal displaying.

.. opt:: Warnings "{+, {? {| - | + } } @ident }"
   :name: Warnings

   This option configures the display of warnings. It is experimental, and
   expects, between quotes, a comma-separated list of warning names or
   categories. Adding - in front of a warning or category disables it, adding +
   makes it an error. It is possible to use the special categories all and
   default, the latter containing the warnings enabled by default. The flags are
   interpreted from left to right, so in case of an overlap, the flags on the
   right have higher priority, meaning that `A,-A` is equivalent to `-A`.

.. opt:: Printing Width @num
   :name: Printing Width

   This command sets which left-aligned part of the width of the screen is used
   for display. At the time of writing this documentation, the default value
   is 78.

.. opt:: Printing Depth @num
   :name: Printing Depth

   This option controls the nesting depth of the formatter used for pretty-
   printing. Beyond this depth, display of subterms is replaced by dots. At the
   time of writing this documentation, the default value is 50.

.. flag:: Printing Compact Contexts

   This flag controls the compact display mode for goals contexts. When on,
   the printer tries to reduce the vertical size of goals contexts by putting
   several variables (even if of different types) on the same line provided it
   does not exceed the printing width (see :opt:`Printing Width`). At the time
   of writing this documentation, it is off by default.

.. flag:: Printing Unfocused

   This flag controls whether unfocused goals are displayed. Such goals are
   created by focusing other goals with bullets (see :ref:`bullets` or
   :ref:`curly braces <curly-braces>`). It is off by default.

.. flag:: Printing Dependent Evars Line

   This flag controls the printing of the “(dependent evars: …)” information
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
   sensitive to the implicit arguments). Turning this flag on
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

.. _vernac-controlling-the-reduction-strategies:

Controlling the reduction strategies and the conversion algorithm
----------------------------------------------------------------------


|Coq| provides reduction strategies that the tactics can invoke and two
different algorithms to check the convertibility of types. The first
conversion algorithm lazily compares applicative terms while the other
is a brute-force but efficient algorithm that first normalizes the
terms before comparing them. The second algorithm is based on a
bytecode representation of terms similar to the bytecode
representation used in the ZINC virtual machine :cite:`Leroy90`. It is
especially useful for intensive computation of algebraic values, such
as numbers, and for reflection-based tactics. The commands to fine-
tune the reduction strategies and the lazy conversion algorithm are
described first.

.. cmd:: Opaque {+ @reference }

   This command accepts the :attr:`global` attribute.  By default, the scope
   of :cmd:`Opaque` is limited to the current section or module.

   This command has an effect on unfoldable constants, i.e. on constants
   defined by :cmd:`Definition` or :cmd:`Let` (with an explicit body), or by a command
   assimilated to a definition such as :cmd:`Fixpoint`, :cmd:`Program Definition`, etc,
   or by a proof ended by :cmd:`Defined`. The command tells not to unfold the
   constants in the :n:`@reference` sequence in tactics using δ-conversion (unfolding
   a constant is replacing it by its definition).

   :cmd:`Opaque` has also an effect on the conversion algorithm of |Coq|, telling
   it to delay the unfolding of a constant as much as possible when |Coq|
   has to check the conversion (see Section :ref:`conversion-rules`) of two distinct
   applied constants.

   .. seealso::

      Sections :ref:`performingcomputations`, :ref:`tactics-automating`,
      :ref:`proof-editing-mode`

.. cmd:: Transparent {+ @reference }

   This command accepts the :attr:`global` attribute.  By default, the scope
   of :cmd:`Transparent` is limited to the current section or module.

   This command is the converse of :cmd:`Opaque` and it applies on unfoldable
   constants to restore their unfoldability after an Opaque command.

   Note in particular that constants defined by a proof ended by Qed are
   not unfoldable and Transparent has no effect on them. This is to keep
   with the usual mathematical practice of *proof irrelevance*: what
   matters in a mathematical development is the sequence of lemma
   statements, not their actual proofs. This distinguishes lemmas from
   the usual defined constants, whose actual values are of course
   relevant in general.

   .. exn:: The reference @qualid was not found in the current environment.

      There is no constant named :n:`@qualid` in the environment.

      .. seealso::

         Sections :ref:`performingcomputations`,
         :ref:`tactics-automating`, :ref:`proof-editing-mode`

.. _vernac-strategy:

.. cmd:: Strategy {+ @strategy_level [ {+ @reference } ] }

   .. insertprodn strategy_level strategy_level_or_var

   .. prodn::
      strategy_level ::= opaque
      | @int
      | expand
      | transparent
      strategy_level_or_var ::= @strategy_level
      | @ident

   This command accepts the :attr:`local` attribute, which limits its effect
   to the current section or module, in which case the section and module
   behavior is the same as :cmd:`Opaque` and :cmd:`Transparent` (without :attr:`global`).

   This command generalizes the behavior of the :cmd:`Opaque` and :cmd:`Transparent`
   commands. It is used to fine-tune the strategy for unfolding
   constants, both at the tactic level and at the kernel level. This
   command associates a :n:`@strategy_level` with the qualified names in the :n:`@reference`
   sequence. Whenever two
   expressions with two distinct head constants are compared (for
   instance, this comparison can be triggered by a type cast), the one
   with lower level is expanded first. In case of a tie, the second one
   (appearing in the cast type) is expanded.

   Levels can be one of the following (higher to lower):

    + ``opaque`` : level of opaque constants. They cannot be expanded by
      tactics (behaves like +∞, see next item).
    + :n:`@int` : levels indexed by an integer. Level 0 corresponds to the
      default behavior, which corresponds to transparent constants. This
      level can also be referred to as ``transparent``. Negative levels
      correspond to constants to be expanded before normal transparent
      constants, while positive levels correspond to constants to be
      expanded after normal transparent constants.
    + ``expand`` : level of constants that should be expanded first (behaves
      like −∞)
    + ``transparent`` : Equivalent to level 0

.. cmd:: Print Strategy @reference

   This command prints the strategy currently associated with :n:`@reference`. It
   fails if :n:`@reference` is not an unfoldable reference, that is, neither a
   variable nor a constant.

   .. exn:: The reference is not unfoldable.
      :undocumented:

.. cmd:: Print Strategies

   Print all the currently non-transparent strategies.


.. cmd:: Declare Reduction @ident := @red_expr

   Declares a short name for the reduction expression :n:`@red_expr`, for
   instance ``lazy beta delta [foo bar]``. This short name can then be used
   in :n:`Eval @ident in` or ``eval`` constructs. This command
   accepts the :attr:`local` attribute, which indicates that the reduction
   will be discarded at the end of the
   file or module. The name is not qualified. In
   particular declaring the same name in several modules or in several
   functor applications will be rejected if these declarations are not
   local. The name :n:`@ident` cannot be used directly as an Ltac tactic, but
   nothing prevents the user from also performing a
   :n:`Ltac @ident := @red_expr`.

   .. seealso:: :ref:`performingcomputations`


.. _controlling-locality-of-commands:

Controlling the locality of commands
-----------------------------------------

.. attr:: global
          local

   Some commands support a :attr:`local` or :attr:`global` attribute
   to control the scope of their effect.  There is also a legacy (and
   much more commonly used) syntax using the ``Local`` or ``Global``
   prefixes (see :n:`@legacy_attr`).  There are four kinds of
   commands:

   + Commands whose default is to extend their effect both outside the
     section and the module or library file they occur in.  For these
     commands, the :attr:`local` attribute limits the effect of the command to the
     current section or module it occurs in.  As an example, the :cmd:`Coercion`
     and :cmd:`Strategy` commands belong to this category.
   + Commands whose default behavior is to stop their effect at the end
     of the section they occur in but to extend their effect outside the module or
     library file they occur in. For these commands, the :attr:`local` attribute limits the
     effect of the command to the current module if the command does not occur in a
     section and the :attr:`global` attribute extends the effect outside the current
     sections and current module if the command occurs in a section. As an example,
     the :cmd:`Arguments`, :cmd:`Ltac` or :cmd:`Notation` commands belong
     to this category. Notice that a subclass of these commands do not support
     extension of their scope outside sections at all and the :attr:`global` attribute is not
     applicable to them.
   + Commands whose default behavior is to stop their effect at the end
     of the section or module they occur in.  For these commands, the :attr:`global`
     attribute extends their effect outside the sections and modules they
     occur in.  The :cmd:`Transparent` and :cmd:`Opaque` commands
     belong to this category.
   + Commands whose default behavior is to extend their effect outside
     sections but not outside modules when they occur in a section and to
     extend their effect outside the module or library file they occur in
     when no section contains them. For these commands, the :attr:`local` attribute
     limits the effect to the current section or module while the :attr:`global`
     attribute extends the effect outside the module even when the command
     occurs in a section.  The :cmd:`Set` and :cmd:`Unset` commands belong to this
     category.

.. attr:: export

   Some commands support an :attr:`export` attribute.  The effect of
   the attribute is to make the effect of the command available when
   the module containing it is imported.  It is supported in
   particular by the :cmd:`Hint`, :cmd:`Set` and :cmd:`Unset`
   commands.

.. _controlling-typing-flags:

Controlling Typing Flags
----------------------------

.. flag:: Guard Checking

   This flag can be used to enable/disable the guard checking of
   fixpoints. Warning: this can break the consistency of the system, use at your
   own risk. Decreasing argument can still be specified: the decrease is not checked
   anymore but it still affects the reduction of the term. Unchecked fixpoints are
   printed by :cmd:`Print Assumptions`.

.. flag:: Positivity Checking

   This flag can be used to enable/disable the positivity checking of inductive
   types and the productivity checking of coinductive types. Warning: this can
   break the consistency of the system, use at your own risk. Unchecked
   (co)inductive types are printed by :cmd:`Print Assumptions`.

.. flag:: Universe Checking

   This flag can be used to enable/disable the checking of universes, providing a
   form of "type in type".  Warning: this breaks the consistency of the system, use
   at your own risk.  Constants relying on "type in type" are printed by
   :cmd:`Print Assumptions`. It has the same effect as `-type-in-type` command line
   argument (see :ref:`command-line-options`).

.. cmd:: Print Typing Flags

   Print the status of the three typing flags: guard checking, positivity checking
   and universe checking.

See also :flag:`Cumulative StrictProp` in the |SProp| chapter.

.. example::

   .. coqtop:: all reset

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

   .. coqtop:: all reset

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


.. _internal-registration-commands:

Internal registration commands
--------------------------------

Due to their internal nature, the commands that are presented in this section
are not for general use. They are meant to appear only in standard libraries and
in support libraries of plug-ins.

.. _exposing-constants-to-ocaml-libraries:

Exposing constants to OCaml libraries
`````````````````````````````````````

.. cmd:: Register @qualid__1 as @qualid__2

   Makes the constant :n:`@qualid__1` accessible to OCaml libraries under
   the name :n:`@qualid__2`.  The constant can then be dynamically located
   in OCaml code by
   calling :n:`Coqlib.lib_ref "@qualid__2"`.  The OCaml code doesn't need
   to know where the constant is defined (what file, module, library, etc.).

   As a special case, when the first segment of :n:`@qualid__2` is :g:`kernel`,
   the constant is exposed to the kernel. For instance, the `Int63` module
   features the following declaration:

   .. coqdoc::

      Register bool as kernel.ind_bool.

   This makes the kernel aware of the `bool` type, which is used, for example,
   to define the return type of the :g:`#int63_eq` primitive.

   .. seealso:: :ref:`primitive-integers`

Inlining hints for the fast reduction machines
``````````````````````````````````````````````

.. cmd:: Register Inline @qualid

   Gives a hint to the reduction machines (VM and native) that
   the body of the constant :n:`@qualid` should be inlined in the generated code.

Registering primitive operations
````````````````````````````````

.. cmd:: Primitive @ident {? : @term } := #@ident__prim

   Makes the primitive type or primitive operator :n:`#@ident__prim` defined in OCaml
   accessible in |Coq| commands and tactics.
   For internal use by implementors of |Coq|'s standard library or standard library
   replacements.  No space is allowed after the `#`.  Invalid values give a syntax
   error.

   For example, the standard library files `Int63.v` and `PrimFloat.v` use :cmd:`Primitive`
   to support, respectively, the features described in :ref:`primitive-integers` and
   :ref:`primitive-floats`.

   The types associated with an operator must be declared to the kernel before declaring operations
   that use the type.  Do this with :cmd:`Primitive` for primitive types and
   :cmd:`Register` with the :g:`kernel` prefix for other types.  For example,
   in `Int63.v`, `#int63_type` must be declared before the associated operations.

   .. exn:: The type @ident must be registered before this construction can be typechecked.
      :undocumented:

      The type must be defined with :cmd:`Primitive` command before this
      :cmd:`Primitive` command (declaring an operation using the type) will succeed.
