.. include:: ../preamble.rst
.. include:: ../replaces.rst

.. _vernacularcommands:

Vernacular commands
=============================

.. _displaying:

Displaying
--------------


.. _Print:

.. cmd:: Print @qualid
   :name: Print

   This command displays on the screen information about the declared or
   defined object referred by :n:`@qualid`.

   Error messages:

   .. exn:: @qualid not a defined object.

   .. exn:: Universe instance should have length @num.

   .. exn:: This object does not support universe names.


   .. cmdv:: Print Term @qualid
      :name: Print Term

      This is a synonym of :cmd:`Print` :n:`@qualid` when :n:`@qualid`
      denotes a global constant.

   .. cmdv:: Print {? Term } @qualid\@@name

      This locally renames the polymorphic universes of :n:`@qualid`.
      An underscore means the raw universe is printed.


.. cmd:: About @qualid
   :name: About

   This displays various information about the object
   denoted by :n:`@qualid`: its kind (module, constant, assumption, inductive,
   constructor, abbreviation, …), long name, type, implicit arguments and
   argument scopes. It does not print the body of definitions or proofs.

   .. cmdv:: About @qualid\@@name

      This locally renames the polymorphic universes of :n:`@qualid`.
      An underscore means the raw universe is printed.


.. cmd:: Print All

   This command displays information about the current state of the
   environment, including sections and modules.

   .. cmdv:: Inspect @num
      :name: Inspect

      This command displays the :n:`@num` last objects of the
      current environment, including sections and modules.

   .. cmdv:: Print Section @ident

      The name :n:`@ident` should correspond to a currently open section,
      this command displays the objects defined since the beginning of this
      section.


.. _flags-options-tables:

Flags, Options and Tables
-----------------------------

|Coq| configurability is based on flags (e.g. :opt:`Printing All`), options
(e.g. :opt:`Printing Width`), or tables (e.g. :cmd:`Add Printing Record`). The
names of flags, options and tables are made of non-empty sequences of
identifiers (conventionally with capital initial letter). The general commands
handling flags, options and tables are given below.

.. TODO : flag is not a syntax entry

.. cmd:: Set @flag

   This command switches :n:`@flag` on. The original state of :n:`@flag`
   is restored when the current module ends.

   .. cmdv:: Local Set @flag

      This command switches :n:`@flag` on. The original state
      of :n:`@flag` is restored when the current *section* ends.

   .. cmdv:: Global Set @flag

      This command switches :n:`@flag` on. The original state
      of :n:`@flag` is *not* restored at the end of the module. Additionally, if
      set in a file, :n:`@flag` is switched on when the file is `Require`-d.

   .. cmdv:: Export Set @flag

      This command switches :n:`@flag` on. The original state
      of :n:`@flag` is restored at the end of the current module, but :n:`@flag`
      is switched on when this module is imported.


.. cmd:: Unset @flag

   This command switches :n:`@flag` off. The original state of
   :n:`@flag` is restored when the current module ends.

   .. cmdv:: Local Unset @flag

      This command switches :n:`@flag` off. The original
      state of :n:`@flag` is restored when the current *section* ends.

   .. cmdv:: Global Unset @flag

      This command switches :n:`@flag` off. The original
      state of :n:`@flag` is *not* restored at the end of the module. Additionally,
      if set in a file, :n:`@flag` is switched off when the file is `Require`-d.

   .. cmdv:: Export Unset @flag

      This command switches :n:`@flag` off. The original state
      of :n:`@flag` is restored at the end of the current module, but :n:`@flag`
      is switched off when this module is imported.


.. cmd:: Test @flag

   This command prints whether :n:`@flag` is on or off.


.. cmd:: Set @option @value

   This command sets :n:`@option` to :n:`@value`. The original value of ` option` is
   restored when the current module ends.

   .. TODO : option and value are not syntax entries

   .. cmdv:: Local Set @option @value

      This command sets :n:`@option` to :n:`@value`. The
      original value of :n:`@option` is restored at the end of the module.

   .. cmdv:: Global Set @option @value

      This command sets :n:`@option` to :n:`@value`. The
      original value of :n:`@option` is *not* restored at the end of the module.
      Additionally, if set in a file, :n:`@option` is set to value when the file
      is `Require`-d.

   .. cmdv:: Export Set @option

      This command set :n:`@option` to :n:`@value`. The original state
      of :n:`@option` is restored at the end of the current module, but :n:`@option`
      is set to :n:`@value` when this module is imported.


.. cmd:: Unset @option

   This command turns off :n:`@option`.

   .. cmdv:: Local Unset @option

      This command turns off :n:`@option`. The original state of :n:`@option`
      is restored when the current *section* ends.

   .. cmdv:: Global Unset @option

      This command turns off :n:`@option`. The original state of :n:`@option`
      is *not* restored at the end of the module. Additionally, if unset in a file,
      :n:`@option` is reset to its default value when the file is `Require`-d.

   .. cmdv:: Export Unset @option

      This command turns off :n:`@option`. The original state of :n:`@option`
      is restored at the end of the current module, but :n:`@option` is set to
      its default value when this module is imported.


.. cmd:: Test @option

   This command prints the current value of :n:`@option`.


.. TODO : table is not a syntax entry

.. cmd:: Add @table @value
   :name: Add `table` `value`

.. cmd:: Remove @table @value
   :name: Remove `table` `value`

.. cmd:: Test @table @value
   :name: Test `table` `value`

.. cmd:: Test @table for @value
   :name: Test `table` for `value`

.. cmd:: Print Table @table

These are general commands for tables.


.. cmd:: Print Options

   This command lists all available flags, options and tables.

   .. cmdv:: Print Tables

      This is a synonymous of :cmd:`Print Options`.


.. _requests-to-the-environment:

Requests to the environment
-------------------------------

.. cmd:: Check @term

   This command displays the type of :n:`@term`. When called in proof mode, the
   term is checked in the local context of the current subgoal.


   .. TODO : selector is not a syntax entry

   .. cmdv:: @selector: Check @term

      This variant specifies on which subgoal to perform typing
      (see Section :ref:`invocation-of-tactics`).


.. TODO : convtactic is not a syntax entry

.. cmd:: Eval @convtactic in @term

   This command performs the specified reduction on :n:`@term`, and displays
   the resulting term with its type. The term to be reduced may depend on
   hypothesis introduced in the first subgoal (if a proof is in
   progress).

   See also: Section :ref:`performingcomputations`.


.. cmd:: Compute @term

   This command performs a call-by-value evaluation of term by using the
   bytecode-based virtual machine. It is a shortcut for ``Eval vm_compute in``
   :n:`@term`.

   See also: Section :ref:`performingcomputations`.


.. cmd:: Print Assumptions @qualid

   This commands display all the assumptions (axioms, parameters and
   variables) a theorem or definition depends on. Especially, it informs
   on the assumptions with respect to which the validity of a theorem
   relies.

   .. cmdv:: Print Opaque Dependencies @qualid
      :name: Print Opaque Dependencies

      Displays the set of opaque constants :n:`@qualid` relies on in addition to
      the assumptions.

   .. cmdv:: Print Transparent Dependencies @qualid
      :name: Print Transparent Dependencies

      Displays the set of transparent constants :n:`@qualid` relies on
      in addition to the assumptions.

   .. cmdv:: Print All Dependencies @qualid
      :name: Print All Dependencies

      Displays all assumptions and constants :n:`@qualid` relies on.


.. cmd:: Search @qualid

   This command displays the name and type of all objects (hypothesis of
   the current goal, theorems, axioms, etc) of the current context whose
   statement contains :n:`@qualid`. This command is useful to remind the user
   of the name of library lemmas.

   .. exn:: The reference @qualid was not found in the current environment.

      There is no constant in the environment named qualid.

   .. cmdv:: Search @string

      If :n:`@string` is a valid identifier, this command
      displays the name and type of all objects (theorems, axioms, etc) of
      the current context whose name contains string. If string is a
      notation’s string denoting some reference :n:`@qualid` (referred to by its
      main symbol as in `"+"` or by its notation’s string as in `"_ + _"` or
      `"_ 'U' _"`, see Section :ref:`notations`), the command works like ``Search`` :n:`@qualid`.

   .. cmdv:: Search @string%@key

      The string string must be a notation or the main
      symbol of a notation which is then interpreted in the scope bound to
      the delimiting key :n:`@key` (see Section :ref:`LocalInterpretationRulesForNotations`).

   .. cmdv:: Search @term_pattern

      This searches for all statements or types of
      definition that contains a subterm that matches the pattern
      `term_pattern` (holes of the pattern are either denoted by `_` or by
      `?ident` when non linear patterns are expected).

   .. cmdv:: Search { + [-]@term_pattern_string }

      where
      :n:`@term_pattern_string` is a term_pattern, a string, or a string followed
      by a scope delimiting key `%key`.  This generalization of ``Search`` searches
      for all objects whose statement or type contains a subterm matching
      :n:`@term_pattern` (or :n:`@qualid` if :n:`@string` is the notation for a reference
      qualid) and whose name contains all string of the request that
      correspond to valid identifiers. If a term_pattern or a string is
      prefixed by `-`, the search excludes the objects that mention that
      term_pattern or that string.

   .. cmdv:: Search @term_pattern_string … @term_pattern_string inside {+ @qualid }

      This restricts the search to constructions defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: Search @term_pattern_string … @term_pattern_string outside {+ @qualid }

      This restricts the search to constructions not defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: @selector: Search [-]@term_pattern_string … [-]@term_pattern_string

      This specifies the goal on which to search hypothesis (see
      Section :ref:`invocation-of-tactics`).
      By default the 1st goal is searched. This variant can
      be combined with other variants presented here.

      .. example::

         .. coqtop:: in

            Require Import ZArith.

         .. coqtop:: all

            Search Z.mul Z.add "distr".

            Search "+"%Z "*"%Z "distr" -positive -Prop.

            Search (?x * _ + ?x * _)%Z outside OmegaLemmas.

   .. cmdv:: SearchAbout

      .. deprecated:: 8.5

      Up to |Coq| version 8.4, :cmd:`Search` had the behavior of current
      :cmd:`SearchHead` and the behavior of current :cmd:`Search` was obtained with
      command :cmd:`SearchAbout`. For compatibility, the deprecated name
      :cmd:`SearchAbout` can still be used as a synonym of :cmd:`Search`. For
      compatibility, the list of objects to search when using :cmd:`SearchAbout`
      may also be enclosed by optional ``[ ]`` delimiters.


.. cmd:: SearchHead @term

   This command displays the name and type of all hypothesis of the
   current goal (if any) and theorems of the current context whose
   statement’s conclusion has the form `(term t1 .. tn)`. This command is
   useful to remind the user of the name of library lemmas.

   .. example::

      .. coqtop:: reset all

         SearchHead le.

         SearchHead (@eq bool).

   .. cmdv:: SearchHead @term inside {+ @qualid }

      This restricts the search to constructions defined in the modules named
      by the given :n:`qualid` sequence.

   .. cmdv:: SearchHead term outside {+ @qualid }

      This restricts the search to constructions not defined in the modules
      named by the given :n:`qualid` sequence.

   .. exn:: Module/section @qualid not found.

      No module :n:`@qualid` has been required (see Section :ref:`compiled-files`).

   .. cmdv:: @selector: SearchHead @term

      This specifies the goal on which to
      search hypothesis (see Section :ref:`invocation-of-tactics`).
      By default the 1st goal is searched. This variant can be combined
      with other variants presented here.

   .. note:: Up to |Coq| version 8.4, ``SearchHead`` was named ``Search``.


.. cmd:: SearchPattern @term

   This command displays the name and type of all hypothesis of the
   current goal (if any) and theorems of the current context whose
   statement’s conclusion or last hypothesis and conclusion matches the
   expressionterm where holes in the latter are denoted by `_`.
   It is a variant of Search @term_pattern that does not look for subterms
   but searches for statements whose conclusion has exactly the expected
   form, or whose statement finishes by the given series of
   hypothesis/conclusion.

   .. example::

      .. coqtop:: in

         Require Import Arith.

      .. coqtop:: all

         SearchPattern (_ + _ = _ + _).

         SearchPattern (nat -> bool).

         SearchPattern (forall l : list _, _ l l).

   Patterns need not be linear: you can express that the same expression
   must occur in two places by using pattern variables `?ident`.


   .. example::

      .. coqtop:: all

         SearchPattern (?X1 + _ = _ + ?X1).

   .. cmdv:: SearchPattern @term inside {+ @qualid }

      This restricts the search to constructions defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: SearchPattern @term outside {+ @qualid }

      This restricts the search to constructions not defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: @selector: SearchPattern @term

      This specifies the goal on which to
      search hypothesis (see Section :ref:`invocation-of-tactics`).
      By default the 1st goal is
      searched. This variant can be combined with other variants presented
      here.


.. cmd:: SearchRewrite @term

   This command displays the name and type of all hypothesis of the
   current goal (if any) and theorems of the current context whose
   statement’s conclusion is an equality of which one side matches the
   expression term. Holes in term are denoted by “_”.

   .. example::

      .. coqtop:: in

         Require Import Arith.

      .. coqtop:: all

         SearchRewrite (_ + _ + _).

   .. cmdv:: SearchRewrite term inside {+ @qualid }

      This restricts the search to constructions defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: SearchRewrite @term outside {+ @qualid }

      This restricts the search to constructions not defined in the modules
      named by the given :n:`qualid` sequence.

   .. cmdv:: @selector: SearchRewrite @term

      This specifies the goal on which to
      search hypothesis (see Section :ref:`invocation-of-tactics`).
      By default the 1st goal is
      searched. This variant can be combined with other variants presented
      here.

.. note::

   .. cmd:: Add Search Blacklist @string

      For the ``Search``, ``SearchHead``, ``SearchPattern`` and ``SearchRewrite``
      queries, it is possible to globally filter the search results using this
      command. A lemma whose fully-qualified name
      contains any of the declared strings will be removed from the
      search results. The default blacklisted substrings are ``_subproof`` and
      ``Private_``.

   .. cmd:: Remove Search Blacklist @string

      This command allows expunging this blacklist.


.. cmd:: Locate @qualid

   This command displays the full name of objects whose name is a prefix
   of the qualified identifier :n:`@qualid`, and consequently the |Coq| module in
   which they are defined. It searches for objects from the different
   qualified name spaces of |Coq|: terms, modules, Ltac, etc.

   .. example::

      .. coqtop:: all

         Locate nat.

         Locate Datatypes.O.

         Locate Init.Datatypes.O.

         Locate Coq.Init.Datatypes.O.

         Locate I.Dont.Exist.

   .. cmdv:: Locate Term @qualid

      As Locate but restricted to terms.

   .. cmdv:: Locate Module @qualid

      As Locate but restricted to modules.

   .. cmdv:: Locate Ltac @qualid

      As Locate but restricted to tactics.

See also: Section :ref:`locating-notations`


.. _loading-files:

Loading files
-----------------

|Coq| offers the possibility of loading different parts of a whole
development stored in separate files. Their contents will be loaded as
if they were entered from the keyboard. This means that the loaded
files are ASCII files containing sequences of commands for |Coq|’s
toplevel. This kind of file is called a *script* for |Coq|. The standard
(and default) extension of |Coq|’s script files is .v.


.. cmd:: Load @ident

   This command loads the file named :n:`ident`.v, searching successively in
   each of the directories specified in the *loadpath*. (see Section
   :ref:`libraries-and-filesystem`)

   Files loaded this way cannot leave proofs open, and the ``Load``
   command cannot be used inside a proof either.

   .. cmdv:: Load @string

      Loads the file denoted by the string :n:`@string`, where
      string is any complete filename. Then the `~` and .. abbreviations are
      allowed as well as shell variables. If no extension is specified, |Coq|
      will use the default extension ``.v``.

   .. cmdv:: Load Verbose @ident

   .. cmdv:: Load Verbose @string

      Display, while loading,
      the answers of |Coq| to each command (including tactics) contained in
      the loaded file See also: Section :ref:`controlling-display`.

   .. exn:: Can’t find file @ident on loadpath.

   .. exn:: Load is not supported inside proofs.

   .. exn:: Files processed by Load cannot leave open proofs.

.. _compiled-files:

Compiled files
------------------

This section describes the commands used to load compiled files (see
Chapter :ref:`thecoqcommands` for documentation on how to compile a file). A compiled
file is a particular case of module called *library file*.


.. cmd:: Require @qualid

   This command looks in the loadpath for a file containing module :n:`@qualid`
   and adds the corresponding module to the environment of |Coq|. As
   library files have dependencies in other library files, the command
   :cmd:`Require` :n:`@qualid` recursively requires all library files the module
   qualid depends on and adds the corresponding modules to the
   environment of |Coq| too. |Coq| assumes that the compiled files have been
   produced by a valid |Coq| compiler and their contents are then not
   replayed nor rechecked.

   To locate the file in the file system, :n:`@qualid` is decomposed under the
   form `dirpath.ident` and the file `ident.vo` is searched in the physical
   directory of the file system that is mapped in |Coq| loadpath to the
   logical path dirpath (see Section :ref:`libraries-and-filesystem`). The mapping between
   physical directories and logical names at the time of requiring the
   file must be consistent with the mapping used to compile the file. If
   several files match, one of them is picked in an unspecified fashion.


   .. cmdv:: Require Import @qualid

      This loads and declares the module :n:`@qualid`
      and its dependencies then imports the contents of :n:`@qualid` as described
      :ref:`here <import_qualid>`. It does not import the modules on which
      qualid depends unless these modules were themselves required in module
      :n:`@qualid`
      using :cmd:`Require Export`, as described below, or recursively required
      through a sequence of :cmd:`Require Export`.  If the module required has
      already been loaded, :cmd:`Require Import` :n:`@qualid` simply imports it, as
      :cmd:`Import` :n:`@qualid` would.

   .. cmdv:: Require Export @qualid

      This command acts as ``Require Import`` :n:`@qualid`,
      but if a further module, say `A`, contains a command ``Require Export`` `B`,
      then the command ``Require Import`` `A` also imports the module `B.`

   .. cmdv:: Require [Import | Export] {+ @qualid }

      This loads the
      modules named by the :n:`qualid` sequence and their recursive
      dependencies. If
      ``Import`` or ``Export`` is given, it also imports these modules and
      all the recursive dependencies that were marked or transitively marked
      as ``Export``.

   .. cmdv:: From @dirpath Require @qualid

      This command acts as ``Require``, but picks
      any library whose absolute name is of the form dirpath.dirpath’.qualid
      for some `dirpath’`. This is useful to ensure that the :n:`@qualid` library
      comes from a given package by making explicit its absolute root.

   .. exn:: Cannot load qualid: no physical path bound to dirpath.

   .. exn:: Cannot find library foo in loadpath.

      The command did not find the
      file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
      directory which is not in your LoadPath (see Section :ref:`libraries-and-filesystem`).

   .. exn:: Compiled library @ident.vo makes inconsistent assumptions over library qualid.

      The command tried to load library file :n:`@ident`.vo that
      depends on some specific version of library :n:`@qualid` which is not the
      one already loaded in the current |Coq| session. Probably `ident.v` was
      not properly recompiled with the last version of the file containing
      module :n:`@qualid`.

   .. exn:: Bad magic number.

      The file `ident.vo` was found but either it is not a
      |Coq| compiled module, or it was compiled with an incompatible
      version of |Coq|.

   .. exn:: The file `ident.vo` contains library dirpath and not library dirpath’.

      The library file `dirpath’` is indirectly required by the
      ``Require`` command but it is bound in the current loadpath to the
      file `ident.vo` which was bound to a different library name `dirpath` at
      the time it was compiled.


   .. exn:: Require is not allowed inside a module or a module type.

      This command
      is not allowed inside a module or a module type being defined. It is
      meant to describe a dependency between compilation units. Note however
      that the commands ``Import`` and ``Export`` alone can be used inside modules
      (see Section :ref:`Import <import_qualid>`).



See also: Chapter :ref:`thecoqcommands`


.. cmd:: Print Libraries

   This command displays the list of library files loaded in the
   current |Coq| session. For each of these libraries, it also tells if it
   is imported.


.. cmd:: Declare ML Module {+ @string }

   This commands loads the OCaml compiled files
   with names given by the :n:`@string` sequence
   (dynamic link). It is mainly used to load tactics dynamically. The
   files are searched into the current OCaml loadpath (see the
   command ``Add ML Path`` in Section :ref:`libraries-and-filesystem`).
   Loading of OCaml files is only possible under the bytecode version of
   ``coqtop`` (i.e. ``coqtop`` called with option ``-byte``, see chapter
   :ref:`thecoqcommands`), or when |Coq| has been compiled with a
   version of OCaml that supports native Dynlink (≥ 3.11).

   .. cmdv:: Local Declare ML Module {+ @string }

      This variant is not exported to the modules that import the module
      where they occur, even if outside a section.

   .. exn:: File not found on loadpath: @string.

   .. exn:: Loading of ML object file forbidden in a native Coq.


.. cmd:: Print ML Modules

   This prints the name of all OCaml modules loaded with ``Declare
   ML Module``. To know from where these module were loaded, the user
   should use the command ``Locate File`` (see :ref:`here <locate-file>`)


.. _loadpath:

Loadpath
------------

Loadpaths are preferably managed using |Coq| command line options (see
Section `libraries-and-filesystem`) but there remain vernacular commands to manage them
for practical purposes. Such commands are only meant to be issued in
the toplevel, and using them in source files is discouraged.


.. cmd:: Pwd

   This command displays the current working directory.


.. cmd:: Cd @string

   This command changes the current directory according to :n:`@string` which
   can be any valid path.

   .. cmdv:: Cd

      Is equivalent to Pwd.


.. cmd:: Add LoadPath @string as @dirpath

   This command is equivalent to the command line option
   ``-Q`` :n:`@string` :n:`@dirpath`. It adds the physical directory string to the current
   |Coq| loadpath and maps it to the logical directory dirpath.

   .. cmdv:: Add LoadPath @string

      Performs as Add LoadPath :n:`@string` as :n:`@dirpath` but
      for the empty directory path.


.. cmd:: Add Rec LoadPath @string as @dirpath

   This command is equivalent to the command line option
   ``-R`` :n:`@string` :n:`@dirpath`. It adds the physical directory string and all its
   subdirectories to the current |Coq| loadpath.

   .. cmdv:: Add Rec LoadPath @string

      Works as :cmd:`Add Rec LoadPath` :n:`@string` as :n:`@dirpath` but for the empty
      logical directory path.


.. cmd:: Remove LoadPath @string

   This command removes the path :n:`@string` from the current |Coq| loadpath.


.. cmd:: Print LoadPath

   This command displays the current |Coq| loadpath.

   .. cmdv:: Print LoadPath @dirpath

      Works as :cmd:`Print LoadPath` but displays only
      the paths that extend the :n:`@dirpath` prefix.


.. cmd:: Add ML Path @string

   This command adds the path :n:`@string` to the current OCaml
   loadpath (see the command `Declare ML Module`` in Section :ref:`compiled-files`).


.. cmd:: Add Rec ML Path @string

   This command adds the directory :n:`@string` and all its subdirectories to
   the current OCaml loadpath (see the command :cmd:`Declare ML Module`).


.. cmd:: Print ML Path @string

   This command displays the current OCaml loadpath. This
   command makes sense only under the bytecode version of ``coqtop``, i.e.
   using option ``-byte``
   (see the command Declare ML Module in Section :ref:`compiled-files`).

.. _locate-file:

.. cmd:: Locate File @string

   This command displays the location of file string in the current
   loadpath. Typically, string is a .cmo or .vo or .v file.


.. cmd:: Locate Library @dirpath

   This command gives the status of the |Coq| module dirpath. It tells if
   the module is loaded and if not searches in the load path for a module
   of logical name :n:`@dirpath`.


.. _backtracking:

Backtracking
----------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a vernacular file loaded via
``Load`` or compiled by ``coqc``.


.. cmd:: Reset @ident

   This command removes all the objects in the environment since :n:`@ident`
   was introduced, including :n:`@ident`. :n:`@ident` may be the name of a defined or
   declared object as well as the name of a section. One cannot reset
   over the name of a module or of an object inside a module.

   .. exn:: @ident: no such entry.

   .. cmdv:: Reset Initial

      Goes back to the initial state, just after the start
      of the interactive session.


.. cmd:: Back

   This command undoes all the effects of the last vernacular command.
   Commands read from a vernacular file via a :cmd:`Load` are considered as a
   single command. Proof management commands are also handled by this
   command (see Chapter :ref:`proofhandling`). For that, Back may have to undo more than
   one command in order to reach a state where the proof management
   information is available. For instance, when the last command is a
   :cmd:`Qed`, the management information about the closed proof has been
   discarded. In this case, :cmd:`Back` will then undo all the proof steps up to
   the statement of this proof.

   .. cmdv:: Back @num

      Undo :n:`@num` vernacular commands. As for Back, some extra
      commands may be undone in order to reach an adequate state. For
      instance Back :n:`@num` will not re-enter a closed proof, but rather go just
      before that proof.

   .. exn:: Invalid backtrack.

      The user wants to undo more commands than available in the history.

.. cmd:: BackTo @num

   This command brings back the system to the state labeled :n:`@num`,
   forgetting the effect of all commands executed after this state. The
   state label is an integer which grows after each successful command.
   It is displayed in the prompt when in -emacs mode. Just as :cmd:`Back` (see
   above), the :cmd:`BackTo` command now handles proof states. For that, it may
   have to undo some extra commands and end on a state `num′ ≤ num` if
   necessary.

   .. cmdv:: Backtrack @num @num @num

      .. deprecated:: 8.4

      :cmd:`Backtrack` is a *deprecated* form of
      :cmd:`BackTo` which allows explicitly manipulating the proof environment. The
      three numbers represent the following:

      + *first number* : State label to reach, as for :cmd:`BackTo`.
      + *second number* : *Proof state number* to unbury once aborts have been done.
        |Coq| will compute the number of :cmd:`Undo` to perform (see Chapter :ref:`proofhandling`).
      + *third number* : Number of :cmd:`Abort` to perform, i.e. the number of currently
        opened nested proofs that must be canceled (see Chapter :ref:`proofhandling`).

   .. exn:: Invalid backtrack.

      The destination state label is unknown.


.. _quitting-and-debugging:

Quitting and debugging
--------------------------


.. cmd:: Quit

   This command permits to quit |Coq|.


.. cmd:: Drop

   This is used mostly as a debug facility by |Coq|’s implementors and does
   not concern the casual user. This command permits to leave |Coq|
   temporarily and enter the OCaml toplevel. The OCaml
   command:

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


.. TODO : command is not a syntax entry

.. cmd:: Time @command

   This command executes the vernacular command :n:`@command` and displays the
   time needed to execute it.


.. cmd:: Redirect @string @command

   This command executes the vernacular command :n:`@command`, redirecting its
   output to ":n:`@string`.out".


.. cmd:: Timeout @num @command

   This command executes the vernacular command :n:`@command`. If the command
   has not terminated after the time specified by the :n:`@num` (time
   expressed in seconds), then it is interrupted and an error message is
   displayed.

   .. opt:: Default Timeout @num

      This option controls a default timeout for subsequent commands, as if they
      were passed to a :cmd:`Timeout` command. Commands already starting by a
      :cmd:`Timeout` are unaffected.


.. cmd:: Fail @command

   For debugging scripts, sometimes it is desirable to know
   whether a command or a tactic fails. If the given :n:`@command`
   fails, the ``Fail`` statement succeeds, without changing the proof
   state, and in interactive mode, the system
   prints a message confirming the failure.
   If the given :n:`@command` succeeds, the statement is an error, and
   it prints a message indicating that the failure did not occur.

   .. exn:: The command has not failed!


.. _controlling-display:

Controlling display
-----------------------

.. opt:: Silent

   This option controls the normal displaying.

.. opt:: Warnings "{+, {? %( - %| + %) } @ident }"

   This option configures the display of warnings. It is experimental, and
   expects, between quotes, a comma-separated list of warning names or
   categories. Adding - in front of a warning or category disables it, adding +
   makes it an error. It is possible to use the special categories all and
   default, the latter containing the warnings enabled by default. The flags are
   interpreted from left to right, so in case of an overlap, the flags on the
   right have higher priority, meaning that `A,-A` is equivalent to `-A`.

.. opt:: Search Output Name Only

   This option restricts the output of search commands to identifier names;
   turning it on causes invocations of :cmd:`Search`, :cmd:`SearchHead`,
   :cmd:`SearchPattern`, :cmd:`SearchRewrite` etc. to omit types from their
   output, printing only identifiers.

.. opt:: Printing Width @num

   This command sets which left-aligned part of the width of the screen is used
   for display. At the time of writing this documentation, the default value
   is 78.

.. opt:: Printing Depth @num

   This option controls the nesting depth of the formatter used for pretty-
   printing. Beyond this depth, display of subterms is replaced by dots. At the
   time of writing this documentation, the default value is 50.

.. opt:: Printing Compact Contexts

   This option controls the compact display mode for goals contexts. When on,
   the printer tries to reduce the vertical size of goals contexts by putting
   several variables (even if of different types) on the same line provided it
   does not exceed the printing width (see :opt:`Printing Width`). At the time
   of writing this documentation, it is off by default.

.. opt:: Printing Unfocused

   This option controls whether unfocused goals are displayed. Such goals are
   created by focusing other goals with bullets (see :ref:`bullets` or
   :ref:`curly braces <curly-braces>`). It is off by default.

.. opt:: Printing Dependent Evars Line

   This option controls the printing of the “(dependent evars: …)” line when
   ``-emacs`` is passed.


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

.. cmd:: Opaque {+ @qualid }

   This command has an effect on unfoldable constants, i.e. on constants
   defined by :cmd:`Definition` or :cmd:`Let` (with an explicit body), or by a command
   assimilated to a definition such as :cmd:`Fixpoint`, :cmd:`Program Definition`, etc,
   or by a proof ended by :cmd:`Defined`. The command tells not to unfold the
   constants in the :n:`@qualid` sequence in tactics using δ-conversion (unfolding
   a constant is replacing it by its definition).

   :cmd:`Opaque` has also an effect on the conversion algorithm of |Coq|, telling
   it to delay the unfolding of a constant as much as possible when |Coq|
   has to check the conversion (see Section :ref:`conversion-rules`) of two distinct
   applied constants.

   .. cmdv:: Global Opaque {+ @qualid }
      :name: Global Opaque

      The scope of :cmd:`Opaque` is limited to the current section, or current
      file, unless the variant :cmd:`Global Opaque` is used.

   See also: sections :ref:`performingcomputations`, :ref:`tactics-automatizing`,
   :ref:`proof-editing-mode`

   .. exn:: The reference @qualid was not found in the current environment.

      There is no constant referred by :n:`@qualid` in the environment.
      Nevertheless, if you asked :cmd:`Opaque` `foo` `bar` and if `bar` does
      not exist, `foo` is set opaque.

.. cmd:: Transparent {+ @qualid }

   This command is the converse of :cmd:`Opaque` and it applies on unfoldable
   constants to restore their unfoldability after an Opaque command.

   Note in particular that constants defined by a proof ended by Qed are
   not unfoldable and Transparent has no effect on them. This is to keep
   with the usual mathematical practice of *proof irrelevance*: what
   matters in a mathematical development is the sequence of lemma
   statements, not their actual proofs. This distinguishes lemmas from
   the usual defined constants, whose actual values are of course
   relevant in general.

   .. cmdv:: Global Transparent {+ @qualid }
      :name: Global Transparent

      The scope of Transparent is limited to the current section, or current
      file, unless the variant :cmd:`Global Transparent` is
      used.

   .. exn:: The reference @qualid was not found in the current environment.

      There is no constant referred by :n:`@qualid` in the environment.

   See also: sections :ref:`performingcomputations`,
   :ref:`tactics-automatizing`, :ref:`proof-editing-mode`

.. _vernac-strategy:

.. cmd:: Strategy @level [ {+ @qualid } ]

   This command generalizes the behavior of Opaque and Transparent
   commands. It is used to fine-tune the strategy for unfolding
   constants, both at the tactic level and at the kernel level. This
   command associates a level to the qualified names in the :n:`@qualid`
   sequence. Whenever two
   expressions with two distinct head constants are compared (for
   instance, this comparison can be triggered by a type cast), the one
   with lower level is expanded first. In case of a tie, the second one
   (appearing in the cast type) is expanded.

   Levels can be one of the following (higher to lower):

    + ``opaque`` : level of opaque constants. They cannot be expanded by
      tactics (behaves like +∞, see next item).
    + :n:`@num` : levels indexed by an integer. Level 0 corresponds to the
      default behavior, which corresponds to transparent constants. This
      level can also be referred to as transparent. Negative levels
      correspond to constants to be expanded before normal transparent
      constants, while positive levels correspond to constants to be
      expanded after normal transparent constants.
    + ``expand`` : level of constants that should be expanded first (behaves
      like −∞)

    .. cmdv:: Local Strategy @level [ {+ @qualid } ]

       These directives survive section and module closure, unless the
       command is prefixed by ``Local``. In the latter case, the behavior
       regarding sections and modules is the same as for the :cmd:`Transparent` and
       :cmd:`Opaque` commands.


.. cmd:: Print Strategy @qualid

   This command prints the strategy currently associated to :n:`@qualid`. It
   fails if :n:`@qualid` is not an unfoldable reference, that is, neither a
   variable nor a constant.

   .. exn:: The reference is not unfoldable.

   .. cmdv:: Print Strategies

      Print all the currently non-transparent strategies.


.. cmd:: Declare Reduction @ident := @convtactic

   This command allows giving a short name to a reduction expression, for
   instance lazy beta delta [foo bar]. This short name can then be used
   in ``Eval`` :n:`@ident` ``in`` ... or ``eval`` directives. This command
   accepts the
   Local modifier, for discarding this reduction name at the end of the
   file or module. For the moment the name cannot be qualified. In
   particular declaring the same name in several modules or in several
   functor applications will be refused if these declarations are not
   local. The name :n:`@ident` cannot be used directly as an Ltac tactic, but
   nothing prevents the user to also perform a
   ``Ltac`` `ident` ``:=`` `convtactic`.

   See also: sections :ref:`performingcomputations`


.. _controlling-locality-of-commands:

Controlling the locality of commands
-----------------------------------------


.. cmd:: Local @command
.. cmd:: Global @command

Some commands support a Local or Global prefix modifier to control the
scope of their effect. There are four kinds of commands:


+ Commands whose default is to extend their effect both outside the
  section and the module or library file they occur in.  For these
  commands, the Local modifier limits the effect of the command to the
  current section or module it occurs in.  As an example, the ``Coercion``
  (see Section :ref:`coercions`) and ``Strategy`` (see :ref:`here <vernac-strategy>`)
  commands belong to this category.
+ Commands whose default behavior is to stop their effect at the end
  of the section they occur in but to extent their effect outside the module or
  library file they occur in. For these commands, the Local modifier limits the
  effect of the command to the current module if the command does not occur in a
  section and the Global modifier extends the effect outside the current
  sections and current module if the command occurs in a section. As an example,
  the :cmd:`Implicit Arguments`, :cmd:`Ltac` or :cmd:`Notation` commands belong
  to this category. Notice that a subclass of these commands do not support
  extension of their scope outside sections at all and the Global is not
  applicable to them.
+ Commands whose default behavior is to stop their effect at the end
  of the section or module they occur in.  For these commands, the Global
  modifier extends their effect outside the sections and modules they
  occurs in.  The ``Transparent`` and ``Opaque`` (see Section :ref:`vernac-controlling-the-reduction-strategies`) commands  belong to this category.
+ Commands whose default behavior is to extend their effect outside
  sections but not outside modules when they occur in a section and to
  extend their effect outside the module or library file they occur in
  when no section contains them.For these commands, the Local modifier
  limits the effect to the current section or module while the Global
  modifier extends the effect outside the module even when the command
  occurs in a section.  The ``Set`` and ``Unset`` commands belong to this
  category.
