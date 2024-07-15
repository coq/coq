.. _thecoqcommands:

Coq commands
====================

There are several Coq commands:

+ ``coqide``: a graphical integrated development environment, described
  :ref:`here <coqintegrateddevelopmentenvironment>`.  In addition, there are
  several other IDEs such as Proof General, vsCoq and Coqtail that are not
  included with the Coq installation.
+ ``coqtop``: a legacy terminal-oriented, non-graphical interfaces for Coq
+ ``coqc``: the Coq compiler (batch compilation)
+ ``coqchk``: the Coq checker (validation of compiled libraries)

Many of the parameters to start these tools are shared and are described below.
Passing the `-help` option on the command line will print a summary of the
available command line parameters.  There are also man pages for each of these,
but they are probably less current than `-help` or this document).

.. _interactive-use:

Interactive use (coqtop)
------------------------

In the interactive mode, also known as the Coq toplevel, users can
develop their theories and proofs step by step. The Coq toplevel is run
by the command ``coqtop``.

There are two different binary images of Coq: the byte-code one and the
native-code one (if OCaml provides a native-code compiler for
your platform, which is supposed in the following). By default,
``coqtop`` executes the native-code version; run ``coqtop.byte`` to get
the byte-code version.

The byte-code toplevel is based on an OCaml toplevel (to
allow dynamic linking of tactics). You can switch to the OCaml toplevel
with the command ``Drop.``, and come back to the Coq
toplevel with the command ``#go;;``.

.. flag:: Coqtop Exit On Error

   This :term:`flag`, off by default, causes coqtop to exit with status code
   ``1`` if a command produces an error instead of recovering from it.

Batch compilation (coqc)
------------------------

The ``coqc`` command compiles a Coq proof script file with a ".v" suffix
to create a compiled file with a ".vo" suffix.  (See :ref:`compiled-files`.)
The last component of the filename must be a valid Coq identifier as described in
:ref:`lexical-conventions`; it should contain only letters, digits or
underscores (_) with a ".v" suffix on the final component.
For example ``/bar/foo/toto.v`` is valid, but ``/bar/foo/to-to.v`` is not.

We recommend specifying a :term:`logical path` (which is also the module name)
with the `-R` or the `-Q` options.
Generally we recommend using utilities such as `make` (using `coq_makefile`
to generate the `Makefile`) or `dune` to build Coq projects.
See :ref:`coq_makefile` and :ref:`building_dune`.

.. example:: Compiling and loading a single file

   If `foo.v` is in Coq's current directory, you can use `coqc foo.v`
   to compile it and then `Require foo.` in your script.  But this
   doesn't scale well for larger projects.

   Generally it's better to define a new module:
   To compile `foo.v` as part of a module `Mod1` that is rooted
   at `.` (i.e. the directory containing `foo.v`), run `coqc -Q . Mod1 foo.v`.

   To make the module available in `CoqIDE`, include the following line in the
   `_CoqProject` file (see :ref:`coq_makefile`) in the directory from which you
   start `CoqIDE` or give it as an argument to the ``coqide`` command.
   *<PATH>* is the pathname of the directory containing the module,
   which can be an absolute path or relative to Coq's current directory.  For now,
   you must close and reload a named script file for `CoqIDE` to pick up the change,
   or restart `CoqIDE`.
   The project file name is configurable in `Edit / Preferences / Project`.

      .. coqdoc::
         -R <PATH> Mod1

Customization at launch time
---------------------------------

Command parameters
------------------

There are 3 mechanisms for passing parameters to Coq commands.
In order of importance they are:

- :ref:`command line options <command-line-options>`,
- :ref:`environment variables <customization-by-environment-variables>` and
- the `coqrc` start up script

`coqrc` start up script
~~~~~~~~~~~~~~~~~~~~~~~

When Coq is launched, it can implicitly prepend a startup script to any document
read by Coq, whether it is an interactive session or a file to compile.
The startup script can come from a configuration directory or it can be
specified on the command line.

Coq uses the first file found in this list as the startup script:

- ``$XDG_CONFIG_HOME/coqrc.<VERSION>``
- ``$XDG_CONFIG_HOME/coqrc``
- ``$HOME/.coqrc.<VERSION>``
- ``$HOME/.coqrc``

where ``$XDG_CONFIG_HOME`` is an environment variable.  ``$HOME`` is the user's
home directory.  ``<VERSION>`` is the version of Coq (as shown by `coqc --version`,
for example).

``-init-file file`` on the command line uses the specified file instead of a startup
script from a configuration directory.  ``-q`` prevents the use of a startup script.

.. _customization-by-environment-variables:

Environment variables
~~~~~~~~~~~~~~~~~~~~~

``$COQPATH`` can be used to specify the :term:`load path`. It is a list of directories separated by
``:`` (``;`` on Windows). Coq will also honor ``$XDG_DATA_HOME`` and
``$XDG_DATA_DIRS`` (see Section :ref:`logical-paths-load-path`).

.. TODO PR: Correct ref above?

Some Coq commands call other Coq commands. In this case, they look for
the commands in directory specified by ``$COQBIN``. If this variable is
not set, they look for the commands in the executable path.

.. _COQ_COLORS:

``$COQ_COLORS`` can be used to specify the set
of colors used by ``coqtop`` to highlight its output. It uses the same
syntax as the ``$LS_COLORS`` variable from GNU’s ls, that is, a colon-separated
list of assignments of the form :n:`name={*; attr}` where
``name`` is the name of the corresponding highlight tag and each ``attr`` is an
ANSI escape code. The list of highlight tags can be retrieved with the
``-list-tags`` command-line option of ``coqtop``.

The string uses ANSI escape codes to represent attributes.  For example:

        ``export COQ_COLORS=”diff.added=4;48;2;0;0;240:diff.removed=41”``

sets the highlights for added text in diffs to underlined (the 4) with a background RGB
color (0, 0, 240) and for removed text in diffs to a red background.
Note that if you specify ``COQ_COLORS``, the predefined attributes are ignored.

.. _OCAMLRUNPARAM:

``$OCAMLRUNPARAM``, described
`here <https://caml.inria.fr/pub/docs/manual-ocaml/runtime.html#s:ocamlrun-options>`_,
can be used to specify certain runtime and memory usage parameters.  In most cases,
experimenting with these settings will likely not cause a significant performance difference
and should be harmless.

If the variable is not set, Coq uses the
`default values <https://caml.inria.fr/pub/docs/manual-ocaml/libref/Gc.html#TYPEcontrol>`_,
except that ``space_overhead`` is set to 120 and ``minor_heap_size`` is set to 32Mwords
(256MB with 64-bit executables or 128MB with 32-bit executables).

.. todo: Using the same text "here" for both of the links in the last 2 paragraphs generates
   an incorrect warning: coq-commands.rst:4: WARNING: Duplicate explicit target name: "here".
   The warning doesn't even have the right line number. :-(

.. todo how about COQLIB, COQCORELIB, DOCDIR

.. _COQ_PROFILE_COMPONENTS:

Specifies which components produce events when using the
:ref:`profiling` system. It is a comma separated list of
component names.

If the variable is not set, all components produce events.

Component names are internally defined, but `command` which corresponds to
the interpretation of one command is particularly notable.

.. _command-line-options:

Command line options
~~~~~~~~~~~~~~~~~~~~

The following command-line options are recognized by the commands ``coqc``
and ``coqtop``, unless stated otherwise:

:-I *directory*, -include *directory*: Add physical path *directory*
  to the OCaml loadpath, which is needed to load OCaml object code files
  (``.cmo`` or ``.cmxs``).  Subdirectories are not included.
  See the command :cmd:`Declare ML Module`.

  Directories added with ``-I`` are searched after the current directory,
  in the order in which they were given on the command line

.. TODO PR: is that right about Declare ML Module? it's not a directory like -I

  .. seealso::

     The :cmd:`Declare ML Module` command.

.. _-Q-option:

:-Q *directory dirpath*: Makes the `.vo` files in a :term:`package` available for
  loading with the :cmd:`Require` command by adding new entries to the :term:`load path`.
  The entries map the
  :term:`logical path` *dirpath* to the physical path *directory*.  Then Coq
  recursively adds load path entries for subdirectories.  For example, `-Q . Lib`
  may add the logical path `Lib.SubDir.File`, which maps to the file
  `./SubDir/File.vo`.

  Only subdirectories and files that follow the lexical conventions for
  :n:`@ident`\s are included.  Subdirectories named ``CVS`` or
  ``_darcs`` are excluded. Some operating systems or file systems are
  more restrictive.  For example, Linux’s ext4 file system limits filenames
  to 255 bytes.  The
  default on NTFS (Windows) and HFS+ (MacOS X) file systems is to
  disallow two files in the same directory with names that differ only in their
  case.

  Loading files from packages made available with `-Q` must include
  the :term:`logical name` of the package in `From` clause of the :cmd:`Require`
  command *or* provide a fully qualified name.

:-R *directory dirpath*: Similar to ``-Q`` *directory dirpath*, but allows using
  :cmd:`Require` with a partially qualified name (i.e. without a `From` clause).

:-top *dirpath*: Set the logical module name to :n:`@dirpath` for the
  `coqtop` interactive session. If no module name is specified,
  `coqtop` will default to ``Top``. `coqc` does not accept this option
  because the logical module name is inferred from the name of
  the input file and the corresponding `-R` / `-Q` options.
:-exclude-dir *directory*: Exclude any subdirectory named *directory*
  while processing options such as -R and -Q. By default, only the
  conventional version control management directories named CVS
  and_darcs are excluded.
:-nois, -noinit: Start from an empty state instead of loading the `Init.Prelude`
  module.
:-init-file *file*: Load *file* as the resource file instead of
  loading the default resource file from the standard configuration
  directories.
:-q: Do not to load the default resource file.
:-l *file*, -load-vernac-source *file*: Load and execute the Coq
  script from *file.v*.
:-lv *file*, -load-vernac-source-verbose *file*: Load and execute the
  Coq script from *file.v*. Write its contents to the standard output as
  it is executed.
:-require *qualid*: Load Coq compiled library :n:`@qualid`.
  This is equivalent to running :cmd:`Require` :n:`@qualid`
  (note: the short form `-r *qualid*` is intentionally not provided to
  prevent the risk of collision with `-R`).

  .. _interleave-command-line:

  .. note::

     Note that the relative order of this command-line option and its
     variants (`-ri`, `-re`, `-rfrom`, `-refrom`, `-rifrom`)  and of the `-set` and
     `-unset` options matters since the various :cmd:`Require`,
     :cmd:`Require Import`, :cmd:`Require Export`, :cmd:`Set` and
     :cmd:`Unset` commands will be executed in the order specified on
     the command-line.

:-ri *qualid*, -require-import *qualid*: Load Coq compiled library :n:`@qualid` and import it.
  This is equivalent to running :cmd:`Require Import` :n:`@qualid`.
  See the :ref:`note above <interleave-command-line>` regarding the order
  of command-line options.
:-re *qualid*, -require-export *qualid*: Load Coq compiled library :n:`@qualid` and transitively import it.
  This is equivalent to running :cmd:`Require Export` :n:`@qualid`.
  See the :ref:`note above <interleave-command-line>` regarding the order
  of command-line options.
:-rfrom *dirpath qualid*, -require-from *dirpath qualid*: Load Coq compiled library :n:`@qualid`.
  This is equivalent to running :cmd:`From <From … Require>`
  :n:`@dirpath` :cmd:`Require <From … Require>` :n:`@qualid`.
  See the :ref:`note above <interleave-command-line>` regarding the order
  of command-line options.
:-rifrom *dirpath qualid*, -require-import-from *dirpath qualid*:
  Load Coq compiled library :n:`@qualid` and import it.  This is
  equivalent to running :cmd:`From <From … Require>` :n:`@dirpath`
  :cmd:`Require Import <From … Require>` :n:`@qualid`.  See the
  :ref:`note above <interleave-command-line>` regarding the order of
  command-line options.
:-refrom *dirpath qualid*, -require-export-from *dirpath qualid*:
  Load Coq compiled library :n:`@qualid` and transitively import it.
  This is equivalent to running :cmd:`From <From … Require>`
  :n:`@dirpath` :cmd:`Require Export <From … Require>` :n:`@qualid`.
  See the :ref:`note above <interleave-command-line>` regarding the
  order of command-line options.
:-load-vernac-object *qualid*: Obsolete synonym of :n:`-require qualid`.
:-batch: Exit just after argument parsing. Available for ``coqtop`` only.
:-verbose: Output the content of the input file as it is compiled.
  This option is available for ``coqc`` only.
:-native-compiler (yes|no|ondemand): Enable the :tacn:`native_compute`
  reduction machine and precompilation to ``.cmxs`` files for future use
  by :tacn:`native_compute`.
  Setting ``yes`` enables :tacn:`native_compute`; it also causes Coq
  to precompile the native code for future use; all dependencies need
  to have been precompiled beforehand. Setting ``no`` disables
  :tacn:`native_compute` which defaults back to :tacn:`vm_compute`; no files are precompiled.
  Setting ``ondemand`` enables :tacn:`native_compute`
  but disables precompilation; all missing dependencies will be recompiled
  every time :tacn:`native_compute` is called.

  .. _native-compiler-options:

  .. deprecated:: 8.14

     This flag has been deprecated in favor of the :ref:`coqnative` binary. The
     toolchain has been adapted to transparently rely on the latter, so if you
     use :ref:`coq_makefile` there is nothing to do. Otherwise you should
     substitute calls to `coqc -native-compiler yes` to calls to `coqc` followed
     by `coqnative` on the resulting `vo` file.

  .. versionchanged:: 8.13

     The default value is set at configure time,
     ``-config`` can be used to retrieve it.
     All this can be summarized in the following table:

  .. list-table::
     :header-rows: 1

     * - ``configure``
       - ``coqc``
       - ``native_compute``
       - outcome
       - requirements
     * - yes
       - yes (default)
       - native_compute
       - ``.cmxs``
       - ``.cmxs`` of deps
     * - yes
       - no
       - vm_compute
       - none
       - none
     * - yes
       - ondemand
       - native_compute
       - none
       - none
     * - no
       - yes, no, ondemand
       - vm_compute
       - none
       - none
     * - ondemand
       - yes
       - native_compute
       - ``.cmxs``
       - ``.cmxs`` of deps
     * - ondemand
       - no
       - vm_compute
       - none
       - none
     * - ondemand
       - ondemand (default)
       - native_compute
       - none
       - none

:-native-output-dir *dir*: Set the directory in which to put the aforementioned
  ``.cmxs`` for :tacn:`native_compute`. Defaults to ``.coq-native``.
:-output-directory *dir*, -output-dir *dir*: Sets the output directory for commands that
  write output to files, such as :ref:`extraction` commands, :cmd:`Redirect` and :cmd:`Print Universes`.
:-vos: Indicate Coq to skip the processing of opaque proofs
  (i.e., proofs ending with :cmd:`Qed` or :cmd:`Admitted`), output a ``.vos`` files
  instead of a ``.vo`` file, and to load ``.vos`` files instead of ``.vo`` files
  when interpreting :cmd:`Require` commands.
:-vok: Indicate Coq to check a file completely, to load ``.vos`` files instead
  of ``.vo`` files when interpreting :cmd:`Require` commands, and to output an empty
  ``.vok`` files upon success instead of writing a ``.vo`` file.
:-w (all|none|w₁,…,wₙ): Configure the display of warnings. This
  option expects all, none or a comma-separated list of warning names or
  categories (see Section :ref:`controlling-display`).
:-color (on|off|auto): *Coqtop only*.  Enable or disable color output.
  Default is auto, meaning color is shown only if
  the output channel supports ANSI escape sequences.
:-diffs (on|off|removed): *Coqtop only*.  Controls highlighting of differences
  between proof steps.  ``on`` highlights added tokens, ``removed`` highlights both added and
  removed tokens.  Requires that ``-color`` is enabled.  (see Section
  :ref:`showing_diffs`).
:-beautify: Pretty-print each command to *file.beautified* when
  compiling *file.v*, in order to get old-fashioned
  syntax/definitions/notations.
:-emacs, -ide-slave: Start a special toplevel to communicate with a
  specific IDE.
:-impredicative-set: Change the logical theory of Coq by declaring the
   sort :g:`Set` impredicative.

   .. warning::

      This is known to be inconsistent with some
      standard axioms of classical mathematics such as the functional
      axiom of choice or the principle of description.
:-type-in-type: Collapse the universe hierarchy of Coq.

  .. warning:: This makes the logic inconsistent.
:-mangle-names *ident*: *Experimental.* Do not depend on this option. Replace
  Coq's auto-generated name scheme with names of the form *ident0*, *ident1*,
  etc. Within Coq, the :flag:`Mangle Names` flag turns this behavior on,
  and the :opt:`Mangle Names Prefix` option sets the prefix to use. This feature
  is intended to be used as a linter for developments that want to be robust to
  changes in the auto-generated name scheme. The options are provided to
  facilitate tracking down problems.
:-set *string*: Enable flags and set options. *string* should be
   :n:`@setting_name=value`, the value is interpreted according to the
   type of the option. For flags :n:`@setting_name` is equivalent to
   :n:`@setting_name=true`. For instance ``-set "Universe Polymorphism"``
   will enable :flag:`Universe Polymorphism`. Note that the quotes are
   shell syntax, Coq does not see them.
   See the :ref:`note above <interleave-command-line>` regarding the order
   of command-line options.
:-unset *string*: As ``-set`` but used to disable options and flags.
  *string* must be :n:`"@setting_name"`.
  See the :ref:`note above <interleave-command-line>` regarding the order
  of command-line options.
:-compat *version*: Load a file that sets a few options to maintain
  partial backward-compatibility with a previous version.  This is
  equivalent to :cmd:`Require Import` `Stdlib.Compat.StdlibXXX` with `XXX`
  one of the last three released versions (including the current
  version).  Note that the :ref:`explanations above
  <interleave-command-line>` regarding the order of command-line
  options apply, and this could be relevant if you are resetting some
  of the compatibility options.
:-dump-glob *file*: Dump references for global names in file *file*
  (to be used by coqdoc, see :ref:`coqdoc`). By default, if *file.v* is being
  compiled, *file.glob* is used.
:-no-glob: Disable the dumping of references for global names.
:-image *file*: Set the binary image to be used by ``coqc`` to be *file*
  instead of the standard one. Not of general use.
:-bindir *directory*: Set the directory containing Coq binaries to be
  used by ``coqc``. It is equivalent to doing export COQBIN= *directory*
  before launching ``coqc``.
:-where: Print the location of Coq’s standard library and exit.
:-config: Print the locations of Coq’s binaries, dependencies, and
  libraries, then exit.
:-filteropts: Print the list of command line arguments that `coqtop` has
  recognized as options and exit.
:-v: Print Coq’s version and exit.
:-list-tags: Print the highlight tags known by Coq as well as their
  currently associated color and exit.
:-h, --help: Print a short usage and exit.
:-time: Output timing information for each command to standard output.
:-time-file *file*: Output timing information for each command to the given file.
:-profile *file*: Output :ref:`profiling` information to the given file.

.. _profiling:

Profiling
---------

Use the `coqc` command line argument `-profile` or the environment
variable `PROFILE` in `coq_makefile`, to generate profiling information in
`Google trace format <https://docs.google.com/document/d/1CvAClvFfyA5R-PhYUmn5OOQtYMH4h6I0nSsKchNAySU/edit>`.

The output gives the duration and event counts for the execution of
components of Coq (for instance `process` for the whole file,
`command` for each command, `pretyping` for elaboration).

Environment variable :ref:`COQ_PROFILE_COMPONENTS <COQ_PROFILE_COMPONENTS>` can be used to filter
which components produce events. This may be needed to reduce the
size of the generated file.

The generated file can be visualized with
<https://ui.perfetto.dev> (which can directly load the `.gz`
compressed file produced by `coq_makefile`) or processed using any
JSON-capable system.

Events are annotated with additional information in the `args` field
(either on the beginning `B` or end `E` event):

- `major` and `minor` indicate how many major and minor words were allocated during the event.

- `subtimes` indicates how much time was spent in sub-components and
  how many times each subcomponent was profiled during the event
  (including subcomponents which do not appear in
  `COQ_PROFILE_COMPONENTS`).

- for the `command` event, `cmd` displays the precise location of the
  command and a compressed representation of it (like the `-time` header),
  and `line` is the start line of the command.

.. _compiled-interfaces:

Compiled interfaces (produced using ``-vos``)
----------------------------------------------

Compiled interfaces help saving time while developing Coq formalizations,
by compiling the formal statements exported by a library independently of
the proofs that it contains.

   .. warning::

      Compiled interfaces should only be used for development purposes.
      At the end of the day, one still needs to proof check all files
      by producing standard ``.vo`` files. (Technically, when using ``-vos``,
      fewer universe constraints are collected.)
      Moreover, this feature is still experimental, it may be subject to
      change without prior notice.

**Principle.**

The compilation using ``coqc -vos foo.v`` produces a file called ``foo.vos``,
which is similar to ``foo.vo`` except that all opaque proofs are skipped in
the compilation process.

The compilation using ``coqc -vok foo.v`` checks that the file ``foo.v``
correctly compiles, including all its opaque proofs. If the compilation
succeeds, then the output is a file called ``foo.vok``, with empty contents.
This file is only a placeholder indicating that ``foo.v`` has been successfully
compiled. (This placeholder is useful for build systems such as ``make``.)

When compiling a file ``bar.v`` that depends on ``foo.v`` (for example via
a ``Require Foo.`` command), if the compilation command is ``coqc -vos bar.v``
or ``coqc -vok bar.v``, then the file ``foo.vos`` gets loaded (instead of
``foo.vo``). A special case is if file ``foo.vos`` exists and has empty
contents, and ``foo.vo`` exists, then ``foo.vo`` is loaded.

Appart from the aforementioned case where ``foo.vo`` can be loaded in place
of ``foo.vos``, in general the ``.vos`` and ``.vok`` files live totally
independently from the ``.vo`` files.

**Dependencies generated by ``coq_makefile``.**

The files ``foo.vos`` and ``foo.vok`` both depend on ``foo.v``.

Furthermore, if a file ``foo.v`` requires ``bar.v``, then ``foo.vos``
and ``foo.vok`` also depend on ``bar.vos``.

Note, however, that ``foo.vok`` does not depend on ``bar.vok``.
Hence, as detailed further, parallel compilation of proofs is possible.

In addition, ``coq_makefile`` generates for a file ``foo.v`` a target
``foo.required_vos`` which depends on the list of ``.vos`` files that
``foo.vos`` depends upon (excluding ``foo.vos`` itself). As explained
next, the purpose of this target is to be able to request the minimal
working state for editing interactively the file ``foo.v``.

.. warning::

   When writing a custom build system, be aware that ``coqdep`` only
   produces dependencies related to ``.vos`` and ``.vok`` if the
   ``-vos`` command line flag is passed. This is to maintain
   compatibility with dune (see `ocaml/dune#2642 on github
   <https://github.com/ocaml/dune/issues/2842>`_).

**Typical compilation of a set of file using a build system.**

Assume a file ``foo.v`` that depends on two files ``f1.v`` and ``f2.v``. The
command ``make foo.required_vos`` will compile ``f1.v`` and ``f2.v`` using
the option ``-vos`` to skip the proofs, producing ``f1.vos`` and ``f2.vos``.
At this point, one is ready to work interactively on the file ``foo.v``, even
though it was never needed to compile the proofs involved in the files ``f1.v``
and ``f2.v``.

Assume a set of files ``f1.v ... fn.v`` with linear dependencies. The command
``make vos`` enables compiling the statements (i.e. excluding the proofs) in all
the files. Next, ``make -j vok`` enables compiling all the proofs in parallel.
Thus, calling ``make -j vok`` directly enables taking advantage of a maximal
amount of parallelism during the compilation of the set of files.

Note that this comes at the cost of parsing and typechecking all definitions
twice, once for the ``.vos`` file and once for the ``.vok`` file. However, if
files contain nontrivial proofs, or if the files have many linear chains of
dependencies, or if one has many cores available, compilation should be faster
overall.

**Need for Proof using**

When a theorem is in a section, typechecking the statement of the theorem
may be insufficient to deduce the type of the statement at the end
of the section. For example, the proof of the theorem may make use of section
variables or section hypotheses that are not mentioned in the statement of the
theorem.

For this reason, proofs in sections should begin with :cmd:`Proof using`
instead of :cmd:`Proof`.  The `using` clause should give
the names of the section variables that are required for the proof
that are not involved in the typechecking of the statement. See :flag:`Suggest Proof Using`.
(Note it's fine to use ``Proof using.`` instead of ``Proof.`` for proofs that are not
in a section.)

When using ``-vos``, proofs in sections with :cmd:`Proof using` are skipped.  Proofs
in sections without :cmd:`Proof using` are fully processed (much slower).

**Interaction with standard compilation**

When compiling a file ``foo.v`` using ``coqc`` in the standard way (i.e., without
``-vos`` nor ``-vok``), an empty file ``foo.vos`` and an empty file ``foo.vok``
are created in addition to the regular output file ``foo.vo``.
If ``coqc`` is subsequently invoked on some other file ``bar.v`` using option
``-vos`` or ``-vok``, and that ``bar.v`` requires ``foo.v``, if Coq finds an
empty file ``foo.vos``, then it will load ``foo.vo`` instead of ``foo.vos``.

The purpose of this feature is to allow users to benefit from the ``-vos``
option even if they depend on libraries that were compiled in the traditional
manner (i.e., never compiled using the ``-vos`` option).

.. _coqchk:

Compiled libraries checker (coqchk)
----------------------------------------

The ``coqchk`` command takes a list of library paths as argument, described either
by their logical name or by their physical filename, which must end in ``.vo``. The
corresponding compiled libraries (``.vo`` files) are searched in the path,
recursively processing the libraries they depend on. The content of all these
libraries is then type checked. The effect of ``coqchk`` is only to return with
normal exit code in case of success, and with positive exit code if an error has
been found. Error messages are not deemed to help the user understand what is
wrong. In the current version, it does not modify the compiled libraries to mark
them as successfully checked.

Note that non-logical information is not checked. By logical
information, we mean the type and optional :term:`body` associated with names.
It excludes for instance anything related to the concrete syntax of
objects (customized syntax rules, association between short and long
names), implicit arguments, etc.

This tool can be used for several purposes. One is to check that a
compiled library provided by a third-party has not been forged and
that loading it cannot introduce inconsistencies [#]_. Another point is
to get an even higher level of security. Since ``coqtop`` can be extended
with custom tactics, possibly ill-typed code, it cannot be guaranteed
that the produced compiled libraries are correct. ``coqchk`` is a
standalone verifier, and thus it cannot be tainted by such malicious
code.

Command-line options ``-Q``, ``-R``, ``-where`` and ``-impredicative-set`` are supported
by ``coqchk`` and have the same meaning as for ``coqtop``. As there is no notion of
relative paths in object files ``-Q`` and ``-R`` have exactly the same meaning.

:-norec *module*: Check *module* but do not check its dependencies.
:-admit *module*: Do not check *module* and any of its dependencies,
  unless explicitly required.
:-o: At exit, print a summary about the context. List the names of all
  assumptions and variables (constants without a :term:`body`).
:-silent: Do not write progress information to the standard output.

Environment variable ``$COQLIB`` can be set to override the location of
the standard library.

The algorithm for deciding which modules are checked or admitted is
the following: assuming that ``coqchk`` is called with argument ``M``, option
``-norec N``, and ``-admit A``. Let us write :math:`\overline{S}` for the
set of reflexive transitive dependencies of set :math:`S`. Then:

+ Modules :math:`C = \overline{M} \backslash \overline{A} \cup M \cup N` are loaded and type checked before being added
  to the context.
+ And :math:`M \cup N \backslash C` is the set of modules that are loaded and added to the
  context without type checking. Basic integrity checks (checksums) are
  nonetheless performed.

As a rule of thumb, -admit can be used to tell Coq that some libraries
have already been checked. So ``coqchk A B`` can be split in ``coqchk A`` &&
``coqchk B -admit A`` without type checking any definition twice. Of
course, the latter is slightly slower since it makes more disk access.
It is also less secure since an attacker might have replaced the
compiled library ``A`` after it has been read by the first command, but
before it has been read by the second command.

.. [#] Ill-formed non-logical information might for instance bind
  Coq.Init.Logic.True to short name False, so apparently False is
  inhabited, but using fully qualified names, Coq.Init.Logic.False will
  always refer to the absurd proposition, what we guarantee is that
  there is no proof of this latter constant.
