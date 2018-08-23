.. _thecoqcommands:

The |Coq| commands
====================

There are three |Coq| commands:

+ ``coqtop``: the |Coq| toplevel (interactive mode);
+ ``coqc``: the |Coq| compiler (batch compilation);
+ ``coqchk``: the |Coq| checker (validation of compiled libraries).


The options are (basically) the same for the first two commands, and
roughly described below. You can also look at the ``man`` pages of
``coqtop`` and ``coqc`` for more details.

.. _interactive-use:

Interactive use (coqtop)
------------------------

In the interactive mode, also known as the |Coq| toplevel, the user can
develop his theories and proofs step by step. The |Coq| toplevel is run
by the command ``coqtop``.

There are two different binary images of |Coq|: the byte-code one and the
native-code one (if OCaml provides a native-code compiler for
your platform, which is supposed in the following). By default,
``coqtop`` executes the native-code version; run ``coqtop.byte`` to get
the byte-code version.

The byte-code toplevel is based on an OCaml toplevel (to
allow dynamic linking of tactics). You can switch to the OCaml toplevel
with the command ``Drop.``, and come back to the |Coq|
toplevel with the command ``Coqloop.loop();;``.

Batch compilation (coqc)
------------------------

The ``coqc`` command takes a name *file* as argument. Then it looks for a
vernacular file named *file*.v, and tries to compile it into a
*file*.vo file (See :ref:`compiled-files`).

.. caution::

   The name *file* should be a regular |Coq| identifier as defined in Section :ref:`lexical-conventions`.
   It should contain only letters, digits or underscores (_). For example ``/bar/foo/toto.v`` is valid,
   but ``/bar/foo/to-to.v`` is not.


Customization at launch time
---------------------------------

By resource file
~~~~~~~~~~~~~~~~~~~~~~~

When |Coq| is launched, with either ``coqtop`` or ``coqc``, the
resource file ``$XDG_CONFIG_HOME/coq/coqrc.xxx``, if it exists, will
be implicitly prepended to any document read by Coq, whether it is an
interactive session or a file to compile. Here, ``$XDG_CONFIG_HOME``
is the configuration directory of the user (by default it's ``~/.config``)
and ``xxx`` is the version number (e.g. 8.8). If
this file is not found, then the file ``$XDG_CONFIG_HOME/coqrc`` is
searched. If not found, it is the file ``~/.coqrc.xxx`` which is searched,
and, if still not found, the file ``~/.coqrc``. If the latter is also
absent, no resource file is loaded.
You can also specify an arbitrary name for the resource file
(see option ``-init-file`` below).

The resource file may contain, for instance, ``Add LoadPath`` commands to add
directories to the load path of |Coq|. It is possible to skip the
loading of the resource file with the option ``-q``.

.. _customization-by-environment-variables:

By environment variables
~~~~~~~~~~~~~~~~~~~~~~~~~

Load path can be specified to the |Coq| system by setting up ``$COQPATH``
environment variable. It is a list of directories separated by
``:`` (``;`` on Windows). |Coq| will also honor ``$XDG_DATA_HOME`` and
``$XDG_DATA_DIRS`` (see Section :ref:`libraries-and-filesystem`).

Some |Coq| commands call other |Coq| commands. In this case, they look for
the commands in directory specified by ``$COQBIN``. If this variable is
not set, they look for the commands in the executable path.

.. _COQ_COLORS:

The ``$COQ_COLORS`` environment variable can be used to specify the set
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


.. _command-line-options:

By command line options
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following command-line options are recognized by the commands ``coqc``
and ``coqtop``, unless stated otherwise:

:-I *directory*, -include *directory*: Add physical path *directory*
  to the OCaml loadpath.

  .. seealso::

     :ref:`names-of-libraries` and the
     command Declare ML Module Section :ref:`compiled-files`.
:-Q *directory* dirpath: Add physical path *directory* to the list of
  directories where |Coq| looks for a file and bind it to the logical
  directory *dirpath*. The subdirectory structure of *directory* is
  recursively available from |Coq| using absolute names (extending the
  dirpath prefix) (see Section :ref:`qualified-names`).Note that only those
  subdirectories and files which obey the lexical conventions of what is
  an :n:`@ident` are taken into account. Conversely, the
  underlying file systems or operating systems may be more restrictive
  than |Coq|. While Linux’s ext4 file system supports any |Coq| recursive
  layout (within the limit of 255 bytes per filename), the default on
  NTFS (Windows) or HFS+ (MacOS X) file systems is on the contrary to
  disallow two files differing only in the case in the same directory.

  .. seealso:: Section :ref:`names-of-libraries`.
:-R *directory* dirpath: Do as -Q *directory* dirpath but make the
  subdirectory structure of *directory* recursively visible so that the
  recursive contents of physical *directory* is available from |Coq| using
  short or partially qualified names.

  .. seealso:: Section :ref:`names-of-libraries`.
:-top dirpath: Set the toplevel module name to dirpath instead of Top.
  Not valid for `coqc` as the toplevel module name is inferred from the
  name of the output file.
:-exclude-dir *directory*: Exclude any subdirectory named *directory*
  while processing options such as -R and -Q. By default, only the
  conventional version control management directories named CVS
  and_darcs are excluded.
:-nois: Start from an empty state instead of loading the Init.Prelude
  module.
:-init-file *file*: Load *file* as the resource file instead of
  loading the default resource file from the standard configuration
  directories.
:-q: Do not to load the default resource file.
:-load-ml-source *file*: Load the OCaml source file *file*.
:-load-ml-object *file*: Load the OCaml object file *file*.
:-l *file*, -load-vernac-source *file*: Load and execute the |Coq|
  script from *file.v*.
:-lv *file*, -load-vernac-source-verbose *file*: Load and execute the
  |Coq| script from *file.v*. Write its contents to the standard output as
  it is executed.
:-load-vernac-object dirpath: Load |Coq| compiled library dirpath. This
  is equivalent to runningRequire dirpath.
:-require dirpath: Load |Coq| compiled library dirpath and import it.
  This is equivalent to running Require Import dirpath.
:-batch: Exit just after argument parsing. Available for `coqtop` only.
:-compile *file.v*: Compile file *file.v* into *file.vo*. This option
  implies -batch (exit just after argument parsing). It is available only
  for `coqtop`, as this behavior is the purpose of `coqc`.
:-compile-verbose *file.v*: Same as -compile but also output the
  content of *file.v* as it is compiled.
:-verbose: Output the content of the input file as it is compiled.
  This option is available for `coqc` only; it is the counterpart of
  -compile-verbose.
:-w (all|none|w₁,…,wₙ): Configure the display of warnings. This
  option expects all, none or a comma-separated list of warning names or
  categories (see Section :ref:`controlling-display`).
:-color (on|off|auto): *Coqtop only*.  Enable or disable color output.
  Default is auto, meaning color is shown only if
  the output channel supports ANSI escape sequences.
:-diffs (on|off|removed): *Coqtop only*.  Controls highlighting of differences
  between proof steps.  ``on`` highlights added tokens, ``removed`` highlights both added and
  removed tokens.  Requires that ``–color`` is enabled.  (see Section
  :ref:`showing_diffs`).
:-beautify: Pretty-print each command to *file.beautified* when
  compiling *file.v*, in order to get old-fashioned
  syntax/definitions/notations.
:-emacs, -ide-slave: Start a special toplevel to communicate with a
  specific IDE.
:-impredicative-set: Change the logical theory of |Coq| by declaring the
   sort Set impredicative.

   .. warning::

      This is known to be inconsistent with some
      standard axioms of classical mathematics such as the functional
      axiom of choice or the principle of description.
:-type-in-type: Collapse the universe hierarchy of |Coq|.

  .. warning:: This makes the logic inconsistent.
:-mangle-names *ident*: Experimental: Do not depend on this option. Replace
  Coq's auto-generated name scheme with names of the form *ident0*, *ident1*,
  etc. The command ``Set Mangle Names`` turns the behavior on in a document,
  and ``Set Mangle Names Prefix "ident"`` changes the used prefix. This feature
  is intended to be used as a linter for developments that want to be robust to
  changes in the auto-generated name scheme. The options are provided to
  facilitate tracking down problems.
:-compat *version*: Attempt to maintain some backward-compatibility
  with a previous version.
:-dump-glob *file*: Dump references for global names in file *file*
  (to be used by coqdoc, see :ref:`coqdoc`). By default, if *file.v* is being
  compiled, *file.glob* is used.
:-no-glob: Disable the dumping of references for global names.
:-image *file*: Set the binary image to be used by `coqc` to be *file*
  instead of the standard one. Not of general use.
:-bindir *directory*: Set the directory containing |Coq| binaries to be
  used by `coqc`. It is equivalent to doing export COQBIN= *directory*
  before launching `coqc`.
:-where: Print the location of |Coq|’s standard library and exit.
:-config: Print the locations of |Coq|’s binaries, dependencies, and
  libraries, then exit.
:-filteropts: Print the list of command line arguments that `coqtop` has
  recognized as options and exit.
:-v: Print |Coq|’s version and exit.
:-list-tags: Print the highlight tags known by |Coq| as well as their
  currently associated color and exit.
:-h, --help: Print a short usage and exit.

Compiled libraries checker (coqchk)
----------------------------------------

The ``coqchk`` command takes a list of library paths as argument, described either
by their logical name or by their physical filename, hich must end in ``.vo``. The
corresponding compiled libraries (``.vo`` files) are searched in the path,
recursively processing the libraries they depend on. The content of all these
libraries is then type checked. The effect of ``coqchk`` is only to return with
normal exit code in case of success, and with positive exit code if an error has
been found. Error messages are not deemed to help the user understand what is
wrong. In the current version, it does not modify the compiled libraries to mark
them as successfully checked.

Note that non-logical information is not checked. By logical
information, we mean the type and optional body associated to names.
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
  assumptions and variables (constants without body).
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
