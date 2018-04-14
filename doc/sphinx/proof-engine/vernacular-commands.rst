.. include:: ../preamble.rst
.. include:: ../replaces.rst

.. _vernacularcommands:

Vernacular commands
=============================

.. _displaying:

Displaying
--------------


.. _Print:

.. cmd:: Print @qualid.

This command displays on the screen information about the declared or
defined object referred by :n:`@qualid`.


Error messages:


.. exn:: @qualid not a defined object

.. exn:: Universe instance should have length :n:`num`.

.. exn:: This object does not support universe names.


Variants:


.. cmdv:: Print Term @qualid.

This is a synonym to ``Print`` :n:`@qualid` when :n:`@qualid`
denotes a global constant.

.. cmdv:: About @qualid.

This displays various information about the object
denoted by :n:`@qualid`: its kind (module, constant, assumption, inductive,
constructor, abbreviation, …), long name, type, implicit arguments and
argument scopes. It does not print the body of definitions or proofs.

.. cmdv:: Print @qualid\@@name

This locally renames the polymorphic universes of :n:`@qualid`.
An underscore means the raw universe is printed.
This form can be used with ``Print Term`` and ``About``.

.. cmd:: Print All.

This command displays information about the current state of the
environment, including sections and modules.


Variants:


.. cmdv:: Inspect @num.

This command displays the :n:`@num` last objects of the
current environment, including sections and modules.

.. cmdv:: Print Section @ident.

The name :n:`@ident` should correspond to a currently open section,
this command displays the objects defined since the beginning of this
section.


.. _flags-options-tables:

Flags, Options and Tables
-----------------------------

|Coq| configurability is based on flags (e.g. ``Set Printing All`` in
Section :ref:`printing_constructions_full`), options (e.g. ``Set Printing Widthinteger`` in Section
:ref:`controlling-display`), or tables (e.g. ``Add Printing Record ident``, in Section
:ref:`record-types`).
The names of flags, options and tables are made of non-empty sequences of identifiers
(conventionally with capital initial
letter). The general commands handling flags, options and tables are
given below.

.. TODO : flag is not a syntax entry

.. cmd:: Set @flag.

This command switches :n:`@flag` on. The original state of :n:`@flag` is restored
when the current module ends.


Variants:

.. cmdv:: Local Set @flag.

This command switches :n:`@flag` on. The original state
of :n:`@flag` is restored when the current *section* ends.

.. cmdv:: Global Set @flag.

This command switches :n:`@flag` on. The original state
of :n:`@flag` is *not* restored at the end of the module. Additionally, if
set in a file, :n:`@flag` is switched on when the file is `Require`-d.



.. cmd:: Unset @flag.

This command switches :n:`@flag` off. The original state of :n:`@flag` is restored
when the current module ends.


Variants:

.. cmdv:: Local Unset @flag.

This command switches :n:`@flag` off. The original
state of :n:`@flag` is restored when the current *section* ends.

.. cmdv:: Global Unset @flag.

This command switches :n:`@flag` off. The original
state of :n:`@flag` is *not* restored at the end of the module. Additionally,
if set in a file, :n:`@flag` is switched off when the file is `Require`-d.



.. cmd:: Test @flag.

This command prints whether :n:`@flag` is on or off.


.. cmd:: Set @option @value.

This command sets :n:`@option` to :n:`@value`. The original value of ` option` is
restored when the current module ends.


Variants:

.. TODO : option and value are not syntax entries

.. cmdv:: Local Set @option @value.

This command sets :n:`@option` to :n:`@value`. The
original value of :n:`@option` is restored at the end of the module.

.. cmdv:: Global Set @option @value.

This command sets :n:`@option` to :n:`@value`. The
original value of :n:`@option` is *not* restored at the end of the module.
Additionally, if set in a file, :n:`@option` is set to value when the file
is `Require`-d.



.. cmd::  Unset @option.

This command resets option to its default value.


Variants:


.. cmdv:: Local Unset @option.

This command resets :n:`@option` to its default
value. The original state of :n:`@option` is restored when the current
*section* ends.

.. cmdv:: Global Unset @option.

This command resets :n:`@option` to its default
value. The original state of :n:`@option` is *not* restored at the end of the
module. Additionally, if unset in a file, :n:`@option` is reset to its
default value when the file is `Require`-d.



.. cmd:: Test @option.

This command prints the current value of :n:`@option`.


.. TODO : table is not a syntax entry

.. cmd:: Add @table @value.
.. cmd:: Remove @table @value.
.. cmd:: Test @table @value.
.. cmd:: Test @table for @value.
.. cmd:: Print Table @table.

These are  general commands for tables.

.. cmd:: Print Options.

This command lists all available flags, options and tables.


Variants:


.. cmdv:: Print Tables.

This is a synonymous of ``Print Options``.


.. _requests-to-the-environment:

Requests to the environment
-------------------------------

.. cmd:: Check @term.

This command displays the type of :n:`@term`. When called in proof mode, the
term is checked in the local context of the current subgoal.


Variants:

.. TODO : selector is not a syntax entry

.. cmdv:: @selector: Check @term.

specifies on which subgoal to perform typing
(see Section :ref:`invocation-of-tactics`).

.. TODO : convtactic is not a syntax entry

.. cmd:: Eval @convtactic in @term.

This command performs the specified reduction on :n:`@term`, and displays
the resulting term with its type. The term to be reduced may depend on
hypothesis introduced in the first subgoal (if a proof is in
progress).


See also: Section :ref:`performingcomputations`.


.. cmd:: Compute @term.

This command performs a call-by-value evaluation of term by using the
bytecode-based virtual machine. It is a shortcut for ``Eval vm_compute in``
:n:`@term`.


See also: Section :ref:`performingcomputations`.


.. cmd::Extraction @term.

This command displays the extracted term from :n:`@term`. The extraction is
processed according to the distinction between ``Set`` and ``Prop``; that is
to say, between logical and computational content (see Section
:ref:`sorts`). The extracted term is displayed in OCaml
syntax,
where global identifiers are still displayed as in |Coq| terms.


Variants:


.. cmdv:: Recursive Extraction {+ @qualid }.

Recursively extracts all
the material needed for the extraction of the qualified identifiers.


See also: Chapter :ref:`extraction`.


.. cmd:: Print Assumptions @qualid.

This commands display all the assumptions (axioms, parameters and
variables) a theorem or definition depends on. Especially, it informs
on the assumptions with respect to which the validity of a theorem
relies.


Variants:


.. cmdv:: Print Opaque Dependencies @qualid.

Displays the set of opaque constants :n:`@qualid` relies on in addition to
the assumptions.

.. cmdv:: Print Transparent Dependencies @qualid.

Displays the set of
transparent constants :n:`@qualid` relies on in addition to the assumptions.

.. cmdv:: Print All Dependencies @qualid.

Displays all assumptions and constants :n:`@qualid` relies on.



.. cmd:: Search @qualid.

This command displays the name and type of all objects (hypothesis of
the current goal, theorems, axioms, etc) of the current context whose
statement contains :n:`@qualid`. This command is useful to remind the user
of the name of library lemmas.


Error messages:


.. exn:: The reference @qualid was not found in the current environment

There is no constant in the environment named qualid.

Variants:

.. cmdv:: Search @string.

If :n:`@string` is a valid identifier, this command
displays the name and type of all objects (theorems, axioms, etc) of
the current context whose name contains string. If string is a
notation’s string denoting some reference :n:`@qualid` (referred to by its
main symbol as in `"+"` or by its notation’s string as in `"_ + _"` or
`"_ 'U' _"`, see Section :ref:`notations`), the command works like ``Search`` :n:`@qualid`.

.. cmdv:: Search @string%@key.

The string string must be a notation or the main
symbol of a notation which is then interpreted in the scope bound to
the delimiting key :n:`@key` (see Section :ref:`LocalInterpretationRulesForNotations`).

.. cmdv:: Search @term_pattern.

This searches for all statements or types of
definition that contains a subterm that matches the pattern
`term_pattern` (holes of the pattern are either denoted by `_` or by
`?ident` when non linear patterns are expected).

.. cmdv:: Search { + [-]@term_pattern_string }.

where
:n:`@term_pattern_string` is a term_pattern, a string, or a string followed
by a scope delimiting key `%key`.  This generalization of ``Search`` searches
for all objects whose statement or type contains a subterm matching
:n:`@term_pattern` (or :n:`@qualid` if :n:`@string` is the notation for a reference
qualid) and whose name contains all string of the request that
correspond to valid identifiers. If a term_pattern or a string is
prefixed by `-`, the search excludes the objects that mention that
term_pattern or that string.

.. cmdv:: Search @term_pattern_string … @term_pattern_string inside {+ @qualid } .

This restricts the search to constructions defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: Search @term_pattern_string … @term_pattern_string outside {+ @qualid }.

This restricts the search to constructions not defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: @selector: Search [-]@term_pattern_string … [-]@term_pattern_string.

This specifies the goal on which to search hypothesis (see
Section :ref:`invocation-of-tactics`).
By default the 1st goal is searched. This variant can
be combined with other variants presented here.


.. coqtop:: in

   Require Import ZArith.

.. coqtop:: all

   Search Z.mul Z.add "distr".

   Search "+"%Z "*"%Z "distr" -positive -Prop.

   Search (?x * _ + ?x * _)%Z outside OmegaLemmas.

.. note:: Up to |Coq| version 8.4, ``Search`` had the behavior of current
   ``SearchHead`` and the behavior of current Search was obtained with
   command ``SearchAbout``. For compatibility, the deprecated name
   SearchAbout can still be used as a synonym of Search. For
   compatibility, the list of objects to search when using ``SearchAbout``
   may also be enclosed by optional ``[ ]`` delimiters.


.. cmd:: SearchHead @term.

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion has the form `(term t1 .. tn)`. This command is
useful to remind the user of the name of library lemmas.



.. coqtop:: reset all

   SearchHead le.

   SearchHead (@eq bool).


Variants:

.. cmdv:: SearchHead @term inside {+ @qualid }.

This restricts the search to constructions defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: SearchHead term outside {+ @qualid }.

This restricts the search to constructions not defined in the modules named by the given :n:`qualid` sequence.

Error messages:

.. exn:: Module/section @qualid not found

No module :n:`@qualid` has been required
(see Section :ref:`compiled-files`).

.. cmdv:: @selector: SearchHead @term.

This specifies the goal on which to
search hypothesis (see Section :ref:`invocation-of-tactics`).
By default the 1st goal is
searched. This variant can be combined with other variants presented
here.

.. note:: Up to |Coq| version 8.4, ``SearchHead`` was named ``Search``.


.. cmd:: SearchPattern @term.

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion or last hypothesis and conclusion matches the
expressionterm where holes in the latter are denoted by `_`.
It is a
variant of Search @term_pattern that does not look for subterms but
searches for statements whose conclusion has exactly the expected
form, or whose statement finishes by the given series of
hypothesis/conclusion.

.. coqtop:: in

   Require Import Arith.

.. coqtop:: all

    SearchPattern (_ + _ = _ + _).

    SearchPattern (nat -> bool).

    SearchPattern (forall l : list _, _ l l).

Patterns need not be linear: you can express that the same expression
must occur in two places by using pattern variables `?ident`.


.. coqtop:: all

   SearchPattern (?X1 + _ = _ + ?X1).

Variants:


.. cmdv:: SearchPattern @term inside {+ @qualid } .

This restricts the search to constructions defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: SearchPattern @term outside {+ @qualid }.

This restricts the search to constructions not defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: @selector: SearchPattern @term.

This specifies the goal on which to
search hypothesis (see Section :ref:`invocation-of-tactics`). By default the 1st goal is
searched. This variant can be combined with other variants presented
here.



.. cmdv:: SearchRewrite @term.

This command displays the name and type of all hypothesis of the
current goal (if any) and theorems of the current context whose
statement’s conclusion is an equality of which one side matches the
expression term. Holes in term are denoted by “_”.

.. coqtop:: in

    Require Import Arith.

.. coqtop:: all

    SearchRewrite (_ + _ + _).

Variants:


.. cmdv:: SearchRewrite term inside {+ @qualid }.

This restricts the search to constructions defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: SearchRewrite @term outside {+ @qualid }.

This restricts the search to constructions not defined in the modules named by the given :n:`qualid` sequence.

.. cmdv:: @selector: SearchRewrite @term.

This specifies the goal on which to
search hypothesis (see Section :ref:`invocation-of-tactics`). By default the 1st goal is
searched. This variant can be combined with other variants presented
here.

.. note::

   For the ``Search``, ``SearchHead``, ``SearchPattern`` and ``SearchRewrite``
   queries, it
   is possible to globally filter the search results via the command
   ``Add Search Blacklist`` :n:`@substring`. A lemma whose fully-qualified name
   contains any of the declared substrings will be removed from the
   search results. The default blacklisted substrings are ``_subproof``
   ``Private_``. The command ``Remove Search Blacklist ...`` allows expunging
   this blacklist.


.. cmd:: Locate @qualid.

This command displays the full name of objects whose name is a prefix
of the qualified identifier :n:`@qualid`, and consequently the |Coq| module in
which they are defined. It searches for objects from the different
qualified name spaces of |Coq|: terms, modules, Ltac, etc.

.. coqtop:: none

    Set Printing Depth 50.

.. coqtop:: all

    Locate nat.

    Locate Datatypes.O.

    Locate Init.Datatypes.O.

    Locate Coq.Init.Datatypes.O.

    Locate I.Dont.Exist.

Variants:


.. cmdv:: Locate Term @qualid.

As Locate but restricted to terms.

.. cmdv:: Locate Module @qualid.

As Locate but restricted to modules.

.. cmdv:: Locate Ltac @qualid.

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


.. cmd:: Load @ident.

This command loads the file named :n:`ident`.v, searching successively in
each of the directories specified in the *loadpath*. (see Section
:ref:`libraries-and-filesystem`)

Files loaded this way cannot leave proofs open, and the ``Load``
command cannot be used inside a proof either.

Variants:


.. cmdv:: Load @string.

Loads the file denoted by the string :n:`@string`, where
string is any complete filename. Then the `~` and .. abbreviations are
allowed as well as shell variables. If no extension is specified, |Coq|
will use the default extension ``.v``.

.. cmdv:: Load Verbose @ident.

.. cmdv:: Load Verbose @string.

Display, while loading,
the answers of |Coq| to each command (including tactics) contained in
the loaded file See also: Section :ref:`controlling-display`.

Error messages:

.. exn:: Can’t find file @ident on loadpath

.. exn:: Load is not supported inside proofs

.. exn:: Files processed by Load cannot leave open proofs

.. _compiled-files:

Compiled files
------------------

This section describes the commands used to load compiled files (see
Chapter :ref:`thecoqcommands` for documentation on how to compile a file). A compiled
file is a particular case of module called *library file*.


.. cmd:: Require @qualid.

This command looks in the loadpath for a file containing module :n:`@qualid`
and adds the corresponding module to the environment of |Coq|. As
library files have dependencies in other library files, the command
``Require`` :n:`@qualid` recursively requires all library files the module
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


Variants:

.. cmdv:: Require Import @qualid.

This loads and declares the module :n:`@qualid`
and its dependencies then imports the contents of :n:`@qualid` as described
:ref:`here <import_qualid>`. It does not import the modules on which
qualid depends unless these modules were themselves required in module
:n:`@qualid`
using ``Require Export``, as described below, or recursively required
through a sequence of ``Require Export``.  If the module required has
already been loaded, ``Require Import`` :n:`@qualid` simply imports it, as ``Import``
:n:`@qualid` would.

.. cmdv:: Require Export @qualid.

This command acts as ``Require Import`` :n:`@qualid`,
but if a further module, say `A`, contains a command ``Require Export`` `B`,
then the command ``Require Import`` `A` also imports the module `B.`

.. cmdv:: Require [Import | Export] {+ @qualid }.

This loads the
modules named by the :n:`qualid` sequence and their recursive
dependencies. If
``Import`` or ``Export`` is given, it also imports these modules and
all the recursive dependencies that were marked or transitively marked
as ``Export``.

.. cmdv:: From @dirpath Require @qualid.

This command acts as ``Require``, but picks
any library whose absolute name is of the form dirpath.dirpath’.qualid
for some `dirpath’`. This is useful to ensure that the :n:`@qualid` library
comes from a given package by making explicit its absolute root.



Error messages:

.. exn:: Cannot load qualid: no physical path bound to dirpath

.. exn:: Cannot find library foo in loadpath

The command did not find the
file foo.vo. Either foo.v exists but is not compiled or foo.vo is in a
directory which is not in your LoadPath (see Section :ref:`libraries-and-filesystem`).

.. exn:: Compiled library ident.vo makes inconsistent assumptions over library qualid

The command tried to load library file `ident.vo` that
depends on some specific version of library :n:`@qualid` which is not the
one already loaded in the current |Coq| session. Probably `ident.v` was
not properly recompiled with the last version of the file containing
module :n:`@qualid`.

.. exn:: Bad magic number

The file `ident.vo` was found but either it is not a
|Coq| compiled module, or it was compiled with an incompatible
version of |Coq|.

.. exn:: The file `ident.vo` contains library dirpath and not library dirpath’

The library file `dirpath’` is indirectly required by the
``Require`` command but it is bound in the current loadpath to the
file `ident.vo` which was bound to a different library name `dirpath` at
the time it was compiled.


.. exn:: Require is not allowed inside a module or a module type

This command
is not allowed inside a module or a module type being defined. It is
meant to describe a dependency between compilation units. Note however
that the commands ``Import`` and ``Export`` alone can be used inside modules
(see Section :ref:`Import <import_qualid>`).



See also: Chapter :ref:`thecoqcommands`


.. cmd:: Print Libraries.

This command displays the list of library files loaded in the
current |Coq| session. For each of these libraries, it also tells if it
is imported.


.. cmd:: Declare ML Module {+ @string } .

This commands loads the OCaml compiled files
with names given by the :n:`@string` sequence
(dynamic link). It is mainly used to load tactics dynamically. The
files are searched into the current OCaml loadpath (see the
command ``Add ML Path`` in Section :ref:`libraries-and-filesystem`). Loading of OCaml files is only possible under the bytecode version of ``coqtop`` (i.e.
``coqtop`` called with option ``-byte``, see chapter :ref:`thecoqcommands`), or when |Coq| has been compiled with a
version of OCaml that supports native Dynlink (≥ 3.11).


Variants:


.. cmdv:: Local Declare ML Module {+ @string }.

This variant is not
exported to the modules that import the module where they occur, even
if outside a section.



Error messages:

.. exn:: File not found on loadpath : @string

.. exn:: Loading of ML object file forbidden in a native |Coq|



.. cmd:: Print ML Modules.

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


.. cmd:: Pwd.

This command displays the current working directory.


.. cmd:: Cd @string.

This command changes the current directory according to :n:`@string` which
can be any valid path.


Variants:


.. cmdv:: Cd.

Is equivalent to Pwd.



.. cmd:: Add LoadPath @string as @dirpath.

This command is equivalent to the command line option
``-Q`` :n:`@string` :n:`@dirpath`. It adds the physical directory string to the current
|Coq| loadpath and maps it to the logical directory dirpath.

Variants:


.. cmdv:: Add LoadPath @string.

Performs as Add LoadPath :n:`@string` as :n:`@dirpath` but
for the empty directory path.



.. cmd:: Add Rec LoadPath @string as @dirpath.

This command is equivalent to the command line option
``-R`` :n:`@string` :n:`@dirpath`. It adds the physical directory string and all its
subdirectories to the current |Coq| loadpath.

Variants:


.. cmdv:: Add Rec LoadPath @string.

Works as ``Add Rec LoadPath`` :n:`@string` as :n:`@dirpath` but for the empty
logical directory path.



.. cmd:: Remove LoadPath @string.

This command removes the path :n:`@string` from the current |Coq| loadpath.


.. cmd:: Print LoadPath.

This command displays the current |Coq| loadpath.


Variants:


.. cmdv:: Print LoadPath @dirpath.

Works as ``Print LoadPath`` but displays only
the paths that extend the :n:`@dirpath` prefix.


.. cmd:: Add ML Path @string.

This command adds the path :n:`@string` to the current OCaml
loadpath (see the command `Declare ML Module`` in Section :ref:`compiled-files`).


.. cmd:: Add Rec ML Path @string.

This command adds the directory :n:`@string` and all its subdirectories to
the current OCaml loadpath (see the command ``Declare ML Module``
in Section :ref:`compiled-files`).


.. cmd:: Print ML Path @string.

This command displays the current OCaml loadpath. This
command makes sense only under the bytecode version of ``coqtop``, i.e.
using option ``-byte``
(see the command Declare ML Module in Section :ref:`compiled-files`).

.. _locate-file:

.. cmd:: Locate File @string.

This command displays the location of file string in the current
loadpath. Typically, string is a .cmo or .vo or .v file.


.. cmd:: Locate Library @dirpath.

This command gives the status of the |Coq| module dirpath. It tells if
the module is loaded and if not searches in the load path for a module
of logical name :n:`@dirpath`.


.. _backtracking:

Backtracking
----------------

The backtracking commands described in this section can only be used
interactively, they cannot be part of a vernacular file loaded via
``Load`` or compiled by ``coqc``.


.. cmd:: Reset @ident.

This command removes all the objects in the environment since :n:`@ident`
was introduced, including :n:`@ident`. :n:`@ident` may be the name of a defined or
declared object as well as the name of a section. One cannot reset
over the name of a module or of an object inside a module.


Error messages:

.. exn:: @ident: no such entry

Variants:

.. cmd:: Reset Initial.

Goes back to the initial state, just after the start
of the interactive session.



.. cmd:: Back.

This commands undoes all the effects of the last vernacular command.
Commands read from a vernacular file via a ``Load`` are considered as a
single command. Proof management commands are also handled by this
command (see Chapter :ref:`proofhandling`). For that, Back may have to undo more than
one command in order to reach a state where the proof management
information is available. For instance, when the last command is a
``Qed``, the management information about the closed proof has been
discarded. In this case, ``Back`` will then undo all the proof steps up to
the statement of this proof.


Variants:


.. cmdv:: Back @num.

Undoes :n:`@num` vernacular commands. As for Back, some extra
commands may be undone in order to reach an adequate state. For
instance Back :n:`@num` will not re-enter a closed proof, but rather go just
before that proof.



Error messages:


.. exn:: Invalid backtrack

The user wants to undo more commands than available in the history.

.. cmd:: BackTo @num.

This command brings back the system to the state labeled :n:`@num`,
forgetting the effect of all commands executed after this state. The
state label is an integer which grows after each successful command.
It is displayed in the prompt when in -emacs mode. Just as ``Back`` (see
above), the ``BackTo`` command now handles proof states. For that, it may
have to undo some extra commands and end on a state `num′ ≤ num` if
necessary.


Variants:


.. cmdv:: Backtrack @num @num @num.

`Backtrack` is a *deprecated* form of
`BackTo` which allows explicitly manipulating the proof environment. The
three numbers represent the following:

    + *first number* : State label to reach, as for BackTo.
    + *second number* : *Proof state number* to unbury once aborts have been done.
      |Coq| will compute the number of Undo to perform (see Chapter :ref:`proofhandling`).
    + *third number* : Number of Abort to perform, i.e. the number of currently
      opened nested proofs that must be canceled (see Chapter :ref:`proofhandling`).




Error messages:


.. exn:: Invalid backtrack


The destination state label is unknown.


.. _quitting-and-debugging:

Quitting and debugging
--------------------------


.. cmd:: Quit.

This command permits to quit |Coq|.


.. cmd:: Drop.

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



Warnings:


#. It only works with the bytecode version of |Coq| (i.e. `coqtop.byte`,
   see Section `interactive-use`).
#. You must have compiled |Coq| from the source package and set the
   environment variable COQTOP to the root of your copy of the sources
   (see Section `customization-by-environment-variables`).



.. TODO : command is not a syntax entry

.. cmd:: Time @command.

This command executes the vernacular command :n:`@command` and displays the
time needed to execute it.


.. cmd:: Redirect @string @command.

This command executes the vernacular command :n:`@command`, redirecting its
output to ":n:`@string`.out".


.. cmd:: Timeout @num @command.

This command executes the vernacular command :n:`@command`. If the command
has not terminated after the time specified by the :n:`@num` (time
expressed in seconds), then it is interrupted and an error message is
displayed.


.. cmd:: Set Default Timeout @num.

After using this command, all subsequent commands behave as if they
were passed to a Timeout command. Commands already starting by a
`Timeout` are unaffected.


.. cmd:: Unset Default Timeout.

This command turns off the use of a default timeout.

.. cmd:: Test Default Timeout.

This command displays whether some default timeout has been set or not.

.. cmd:: Fail @command.

For debugging scripts, sometimes it is desirable to know
whether a command or a tactic fails. If the given :n:`@command`
fails, the ``Fail`` statement succeeds, without changing the proof
state, and in interactive mode, the system
prints a message confirming the failure.
If the given :n:`@command` succeeds, the statement is an error, and
it prints a message indicating that the failure did not occur.

Error messages:

.. exn:: The command has not failed!

.. _controlling-display:

Controlling display
-----------------------


.. cmd:: Set Silent.

This command turns off the normal displaying.


.. cmd:: Unset Silent.

This command turns the normal display on.

.. todo:: check that spaces are handled well

.. cmd:: Set Warnings ‘‘(@ident {* , @ident } )’’.

This command configures the display of warnings. It is experimental,
and expects, between quotes, a comma-separated list of warning names
or categories. Adding - in front of a warning or category disables it,
adding + makes it an error. It is possible to use the special
categories all and default, the latter containing the warnings enabled
by default. The flags are interpreted from left to right, so in case
of an overlap, the flags on the right have higher priority, meaning
that `A,-A` is equivalent to `-A`.


.. cmd:: Set Search Output Name Only.

This command restricts the output of search commands to identifier
names; turning it on causes invocations of ``Search``, ``SearchHead``,
``SearchPattern``, ``SearchRewrite`` etc. to omit types from their output,
printing only identifiers.


.. cmd:: Unset Search Output Name Only.

This command turns type display in search results back on.


.. cmd:: Set Printing Width @integer.

This command sets which left-aligned part of the width of the screen
is used for display.


.. cmd:: Unset Printing Width.

This command resets the width of the screen used for display to its
default value (which is 78 at the time of writing this documentation).


.. cmd:: Test Printing Width.

This command displays the current screen width used for display.


.. cmd:: Set Printing Depth @integer.

This command sets the nesting depth of the formatter used for pretty-
printing. Beyond this depth, display of subterms is replaced by dots.


.. cmd:: Unset Printing Depth.

This command resets the nesting depth of the formatter used for
pretty-printing to its default value (at the time of writing this
documentation, the default value is 50).


.. cmd:: Test Printing Depth.

This command displays the current nesting depth used for display.


.. cmd:: Unset Printing Compact Contexts.

This command resets the displaying of goals contexts to non compact
mode (default at the time of writing this documentation). Non compact
means that consecutive variables of different types are printed on
different lines.


.. cmd:: Set Printing Compact Contexts.

This command sets the displaying of goals contexts to compact mode.
The printer tries to reduce the vertical size of goals contexts by
putting several variables (even if of different types) on the same
line provided it does not exceed the printing width (See Set Printing
Width above).


.. cmd:: Test Printing Compact Contexts.

This command displays the current state of compaction of goal.


.. cmd:: Unset Printing Unfocused.

This command resets the displaying of goals to focused goals only
(default). Unfocused goals are created by focusing other goals with
bullets (see :ref:`bullets`) or curly braces (see `here <curly-braces>`).


.. cmd:: Set Printing Unfocused.

This command enables the displaying of unfocused goals. The goals are
displayed after the focused ones and are distinguished by a separator.


.. cmd:: Test Printing Unfocused.

This command displays the current state of unfocused goals display.


.. cmd:: Set Printing Dependent Evars Line.

This command enables the printing of the “(dependent evars: …)” line
when -emacs is passed.


.. cmd:: Unset Printing Dependent Evars Line.

This command disables the printing of the “(dependent evars: …)” line
when -emacs is passed.

.. _vernac-controlling-the-reduction-strategies:

Controlling the reduction strategies and the conversion algorithm
----------------------------------------------------------------------


|Coq| provides reduction strategies that the tactics can invoke and two
different algorithms to check the convertibility of types. The first
conversion algorithm lazily compares applicative terms while the other
is a brute-force but efficient algorithm that first normalizes the
terms before comparing them. The second algorithm is based on a
bytecode representation of terms similar to the bytecode
representation used in the ZINC virtual machine [`98`]. It is
especially useful for intensive computation of algebraic values, such
as numbers, and for reflection-based tactics. The commands to fine-
tune the reduction strategies and the lazy conversion algorithm are
described first.

.. cmd:: Opaque {+ @qualid }.

This command has an effect on unfoldable constants, i.e. on constants
defined by ``Definition`` or ``Let`` (with an explicit body), or by a command
assimilated to a definition such as ``Fixpoint``, ``Program Definition``, etc,
or by a proof ended by ``Defined``. The command tells not to unfold the
constants in the :n:`@qualid` sequence in tactics using δ-conversion (unfolding
a constant is replacing it by its definition).

``Opaque`` has also an effect on the conversion algorithm of |Coq|, telling
it to delay the unfolding of a constant as much as possible when |Coq|
has to check the conversion (see Section :ref:`conversion-rules`) of two distinct
applied constants.

The scope of ``Opaque`` is limited to the current section, or current
file, unless the variant ``Global Opaque`` is used.


See also: sections :ref:`performingcomputations`, :ref:`tactics-automatizing`, :ref:`proof-editing-mode`


Error messages:


.. exn:: The reference @qualid was not found in the current environment

There is no constant referred by :n:`@qualid` in the environment.
Nevertheless, if you asked ``Opaque`` `foo` `bar` and if `bar` does not exist, `foo` is set opaque.

.. cmd:: Transparent {+ @qualid }.

This command is the converse of `Opaque`` and it applies on unfoldable
constants to restore their unfoldability after an Opaque command.

Note in particular that constants defined by a proof ended by Qed are
not unfoldable and Transparent has no effect on them. This is to keep
with the usual mathematical practice of *proof irrelevance*: what
matters in a mathematical development is the sequence of lemma
statements, not their actual proofs. This distinguishes lemmas from
the usual defined constants, whose actual values are of course
relevant in general.

The scope of Transparent is limited to the current section, or current
file, unless the variant ``Global Transparent`` is
used.


Error messages:


.. exn:: The reference @qualid was not found in the current environment

There is no constant referred by :n:`@qualid` in the environment.



See also: sections :ref:`performingcomputations`, :ref:`tactics-automatizing`, :ref:`proof-editing-mode`

.. _vernac-strategy:

.. cmd:: Strategy @level [ {+ @qualid } ].

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


These directives survive section and module closure, unless the
command is prefixed by Local. In the latter case, the behavior
regarding sections and modules is the same as for the ``Transparent`` and
``Opaque`` commands.


.. cmd:: Print Strategy @qualid.

This command prints the strategy currently associated to :n:`@qualid`. It
fails if :n:`@qualid` is not an unfoldable reference, that is, neither a
variable nor a constant.


Error messages:


.. exn:: The reference is not unfoldable.



Variants:


.. cmdv:: Print Strategies.

Print all the currently non-transparent strategies.



.. cmd:: Declare Reduction @ident := @convtactic.

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


.. cmd:: Local @command.
.. cmd:: Global @command.

Some commands support a Local or Global prefix modifier to control the
scope of their effect. There are four kinds of commands:


+ Commands whose default is to extend their effect both outside the
  section and the module or library file they occur in.  For these
  commands, the Local modifier limits the effect of the command to the
  current section or module it occurs in.  As an example, the ``Coercion``
  (see Section :ref:`coercions`) and ``Strategy`` (see :ref:`here <vernac-strategy>`)
  commands belong to this category.
+ Commands whose default behavior is to stop their effect at the end
  of the section they occur in but to extent their effect outside the
  module or library file they occur in.  For these commands, the Local
  modifier limits the effect of the command to the current module if the
  command does not occur in a section and the Global modifier extends
  the effect outside the current sections and current module if the
  command occurs in a section.  As an example, the ``Implicit Arguments`` (see
  Section :ref:`implicitarguments`), Ltac (see Chapter :ref:`TODO-9-tactic-language`) or ``Notation`` (see Section
  :ref:`notations`) commands belong to this category.  Notice that a subclass of
  these commands do not support extension of their scope outside
  sections at all and the Global is not applicable to them.
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
