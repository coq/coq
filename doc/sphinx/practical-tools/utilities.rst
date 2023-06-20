.. _utilities:

----------------------
 Building Coq Projects
----------------------

.. _configuration_basics:

Coq configuration basics
------------------------

Describes the basics of Coq configuration that affect
running and compiling Coq scripts.  It recommends preferred ways to
install Coq, manage installed packages and structure your project
directories for ease of use.

Installing Coq and Coq packages with opam
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The easiest way to install Coq is with the
`Coq Platform <https://github.com/coq/platform>`_, which relies
on the `opam package manager <https://coq.inria.fr/opam-using.html>`_.

The Coq platform installation process provides options to automatically install
some of the most frequently used packages at the
same time.  While there's currently no guarantee that user-developed packages
will compile on the current version of Coq, all packages
that Coq platform installs should compile without difficulty--this is part of
the Coq platform release process.

Once you've installed Coq, you can search for additional user-developed packages
from the `package list <https://coq.inria.fr/opam/www/>`_ or other opam repositories.
These commands may be helpful:

- `opam list "coq-*"` to see the list of available and installed packages
- `opam list "coq-*" --installed` to see the list of installed packages
- `opam install <package name>` to install a package on your system.
- `opam update` as needed to update the list of available packages

For example, this command shows the installed packages with the package name,
its version and short description::

   $ opam list "coq-*" --installed
   coq-bignums               8.15.0          Bignums, the Coq library of arbitrary large numbers

Note that packages marked `released` in the package list web page are more stable
than those marked `extra-dev`.  To install `extra-dev` packages,
first add the `coq-extra-dev` opam repository to your local opam installation
with this command::

  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

While this is the easiest way to install packages, it is not the only way.

You will then need to find the :term:`logical name` used to refer to the package
in :cmd:`Require` commands.  There are a couple ways to do this:

- If you installed with opam, use :n:`opam show --list-files coq-bignums | head -n1` -
  the last component of the filename is the logical name (`Bignums`).

- On Linux, :n:`ls $(coqtop -where)/user-contrib` shows the logical names of all
  installed user-contributed packages.  You should be able to guess which one you
  need.

- Use the :cmd:`Print LoadPath` command when running Coq, which shows the mapping
  from :term:`logical path`\s to directories.  Again, you should be able to guess.

The last two methods work even if you didn't install with opam.  Perhaps in the
future the package name to logical name mapping will be more readily available.

Once you know the logical name of the package, use it to load compiled
files from the package with the :cmd:`Require` command.

A :gdef:`package` is a group of files in a top directory and its subdirectories
that's installed as a unit.  Packages are compiled from *projects*.  These terms
are virtually interchangeable.

Setup for working on your own projects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The working and master copies of source code for your own projects should
not be in the directory tree where Coq is installed.  In particular, when you upgrade
to a new version of Coq, any directories you created in the old version won't
be copied or moved.

We encourage you to use a source code control system for any non-trivial
project because it makes it easy to track the history of your changes.
`git <https://git-scm.com/>`_ is the system most used by Coq projects.
Typically, each project has its own git repository.

For a project that has only a single file, you can create the file wherever you like
and then step through it in one of the IDEs for Coq, such as
:ref:`coqintegrateddevelopmentenvironment`,
`ProofGeneral <https://proofgeneral.github.io/>`_,
`vsCoq <https://github.com/coq-community/vscoq>`_
and `Coqtail <https://github.com/whonore/Coqtail>`_.

If your project has multiple files in a single directory that depend on each
other through :cmd:`Require` commands, they must be compiled in an order that
matches their dependencies.
Scripts in `.v` files must be compiled to `.vo` files using `coqc` before they
can be :cmd:`Require`\d in other files.  Currently, the `.vo` file is created in
the same directory as its `.v` file.  For example,
if B.v depends on A.v, then you should compile A.v before B.v.  You can do this
with :n:`coqc A.v` followed by :n:`coqc B.v`, but you may find it tedious to
manage the dependencies, particularly as the number of files increases.

If your project files are in multiple directories, you would also need to pass
additional command-line -Q and -R parameters to your IDE.  More details to manage
and keep track of.

Instead, by creating a `_CoqProject` file, you can automatically generate
a makefile that applies the correct dependencies when it compiles your project.
In addition, the IDEs find and interpret `_CoqProject` files, so project files
spread over multiple directories will work seamlessly.  If you're editing `dir/foo.v`,
the IDEs apply settings from the `_CoqProject` file in `dir` or the closest
ancestor directory.

The `_CoqProject` file identifies the :term:`logical path` to associate with the
directories containing your compiled files.  The `_CoqProject` file is normally
in the top directory of the project.  Occasionally it may be useful to have
additional `_CoqProject` files in subdirectories, for example in order to pass
different startup parameters to Coq for particular scripts.

.. _building_with_coqproject:

Building a project with _CoqProject (overview)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Note: building with `dune` is experimental.  See :ref:`building_dune`.

The `_CoqProject` file contains the information needed to generate a makefile
for building your project.  Your `_CoqProject` file should be in
the top directory of your project's source tree.  We recommend using the
:term:`logical name` of the project as the name of the top directory.

**Note:** Make sure that `_CoqProject` has no file extension.  On Windows, some
tools such as Notepad invisibly append `.txt` even when you ask to save the file
as `_CoqProject`.  Also, File Manager doesn't display file extensions.  You may
be better off using a command line interface and an editor such as `vi` that
always show file extensions.

For example, here is a minimal `_CoqProject` file for the `MyPackage` project
(the logical name of the package), which includes all the ``.v`` files (and
other file types) in the `theories` directory and its subdirectories::

  -R theories MyPackage
  theories

:n:`-R theories MyPackage` (see :ref:`here <-Q-option>`) declares that `theories` is a top
directory of `MyPackage`.  :n:`theories` on the second line declares that all `.v` files
in `theories` and its subdirectories are indeed included in the project.

In addition, you can list individual files, for example the two script files
`theories/File1.v` and `theories/SubDir/File2.v` whose logical paths are `MyPackage.File1` and
`MyPackage.SubDir.File2`::

  -R theories MyPackage
  theories/File1.v
  theories/SubDir/File2.v

The generated makefile only processes the specified files.
You can list multiple directories if you wish.

.. I think dotted names are not useful.  For example, this doesn't produce usable
   .vo files because a.v and b.v are not in an `Abc` subdirectory::

   -R . Michael.Abc
   a.v
   b.v

We suggest choosing a logical name that's different from those used for commonly
used packages, particularly if you plan to make your package available to others.
Or you can easily do a global replace, if necessary, on the package name
before it is (widely) used.  After that, a name change may begin to impact
a large number of users.  Alas, there's currently no easy way to discover what
:term:`logical name`\s have already been used.  The :cmd:`Print LoadPath` command helps
a bit; it shows the logical names defined in the Coq process.

Then:

- Generate a makefile from `_CoqProject` with
  :n:`coq_makefile -f _CoqProject -o CoqMakefile` and

- Compile your project with :n:`make -f CoqMakefile` as needed.

If you add more files to your project that are not in directories listed
in `_CoqProject`, update `_CoqProject` and re-run `coq_makefile` and `make`.

.. todo we should use a standard name for the makefile so IDEs can find it.
   Maybe you should be allowed to include "-o MAKEFILENAME" in the `_CoqProject`,
   maybe default to "makefile"; provide a name only if you want to use a wrapper
   Then mandate that the file be called simply "makefile" so IDEs can find it.

We recommend checking `CoqMakefile` and `CoqMakefile.conf` into your source code
control system.  Also we recommend updating them with `coq_makefile` when you switch
to a new version of Coq.

In CoqIDE, you must explicitly save modified buffers before running `make` and
restart the Coq interpreter in any buffers in which you're running code.
More details :ref:`here <coqide_make_note>`.

See :ref:`coq_makefile` for a complete description of `coq_makefile` and the
files it generates.

.. todo: describe -vos option, a way to do quicker builds with some caveats

.. _logical-paths-load-path:

Logical paths and the load path
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Coq commands such as :cmd:`Require` identify files with :term:`logical paths<logical path>` rather
than file system paths so that scripts don't have to be modified to run on
different computers.  The :cmd:`Print LoadPath` command displays the :gdef:`load path`,
which is a list of (logical path, :term:`physical path`) pairs for directories.

For example, you may see::

  Logical Path / Physical path:
  Bignums /home/jef/coq/lib/coq/user-contrib/Bignums
  Bignums.BigZ /home/jef/coq/lib/coq/user-contrib/Bignums/BigZ
  Ltac2 /home/jef/coq/lib/coq/user-contrib/Ltac2
  Coq /home/jef/coq/lib/coq/theories
  Coq.Numbers /home/jef/coq/lib/coq/theories/Numbers
  Coq.Numbers.Natural /home/jef/coq/lib/coq/theories/Numbers/Natural
  Coq.Numbers.Natural.Binary /home/jef/coq/lib/coq/theories/Numbers/Natural/Binary
  Coq.Numbers.Integer /home/jef/coq/lib/coq/theories/Numbers/Integer
  Coq.Arith /home/jef/coq/lib/coq/theories/Arith
  <> /home/jef/myproj

The components of each pair share suffixes, e.g. `Bignums.BigZ` and `Bignums/BigZ` or
`Coq.Numbers.Natural` and `Numbers/Natural`.  Physical pathnames should
always use `/` rather than `\\`, even when running on Windows.
Packages with a physical path containing `user-contrib` were installed
with the Coq binaries (e.g. `Ltac2`), with the Coq Platform or with opam (e.g. `Bignums`)
or perhaps by other means.  Note that, for these entries, the entire logical path
appears in the directory name.
Packages that begin with `Coq` were installed with the Coq binaries.  Note
that the :term:`logical name` `Coq` doesn't appear in the physical path.

The `<>` in the final entry represents an empty logical pathname, which
permits loading files from the
associated directory with just the basename of the script file,
e.g. specify `Foo` to load `Foo.vo`.  This entry corresponds to the
current directory when Coq was started.  Note that the :cmd:`Cd` command
doesn't change the associated directory--you would need to restart CoqIDE.

With some exceptions noted below, the :term:`load path` is generated from files loaded
from the following directories and their subdirectories in the order shown.  The
associated logical path is determined from the filesystem path, relative to the
directory, e.g. the file `Foo/Bar/script.vo` becomes `Foo.Bar.script`:

- directories specified with :ref:`-R and -Q command line options <-Q-option>`,
- the current directory where the Coq process was launched (without
  including subdirectories),
- the directories listed in the `COQPATH` environment variable (separated with
  colons, or, on Windows, with semicolons)

.. not working - the ``coq`` subdirectory for each directory  listed in the ``XDG_DATA_DIRS``
  environment variable (separated with colons, or, on Windows, with semicolons)

- the ``${XDG_DATA_HOME}/coq/`` directory (see `XDG base directory specification
  <http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html>`_).
  However, CoqIDE relies on the default setting; therefore we recommend not
  setting this variable.
- installed packages from the `user-contrib` directory in the Coq installation,
- the Coq standard library from the `theories` directory in the Coq installation
  (with `Coq` prepended to the logical path),

.. todo: XDG* with example(s) and suggest best practices for their use

.. todo: document loadpath for ml files

Each directory may contain multiple `.v`/`.vo` files.  For example,
:n:`Require Import Coq.Numbers.Natural.Binary.NBinary` loads the file
:n:`NBinary.vo` from the associated directory.  Note that a short name
is often sufficient in :cmd:`Require` instead of a fully qualified
name.

In :cmd:`Require` commands referring to the current package (if `_CoqProject`
uses `-R`) or Coq's standard library can be referenced with a short name without
a `From` clause provided that the logical path is unambiguous (as if they are
available through `-R`).  In contrast, :cmd:`Require` commands that load files from other
locations such as `user-contrib` must either use an exact logical path
or include a `From` clause (as if they are available through `-Q`).  This is done
to reduce the number of ambiguous logical paths.  We encourage using `From`
clauses.

Note that if you use a `_CoqProject` file, the `COQPATH` environment variable is not helpful.
If you use `COQPATH` without a `_CoqProject`, a file in `MyPackage/theories/SubDir/File.v` will be
loaded with the logical name `MyPackage/theories/SubDir.File`, which may not be what you want.

If you associate the same logical name with more than one directory, Coq
looks for the `.vo` file in the most recently added path first (i.e., the one
that appears earlier in the :cmd:`Print LoadPath` output).

Modifying multiple interdependent projects at the same time
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If you want to modify multiple interdependent projects simultaneously,
good practice recommends that
all of them should be uninstalled.  Since the IDEs only apply a single
`_CoqProject` file for each script, the best way to make them work properly is to
temporarily edit the `_CoqProject` for each project so it includes the other
uninstalled projects it depends on, then regenerate the makefile.  This may
make your `_CoqProject` system dependent.  Such dependencies shouldn't be
present in published packages.

For example, if
project `A` requires project `B`, add `-Q <directory path of B> B` to the
`_CoqProject` in `A`.  This will override any installed version of `B` only
when you're working on scripts in `A`.

If you want to build all the related projects at once, you're
on your own.  There's currently no tooling to identify the internal dependencies
between the projects (and thus the order in which to build them).


.. todo I thought @herbelin added code to complain about ambiguous short names
   I made up some stuff below, need to check it:

Installed and uninstalled packages
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The directory structure of installed packages (i.e., in the `user-contrib` directory
of the Coq installation) differs from that generally used for the project source tree.
The installed directory structure omits the pathname given in the `-R` and `-Q`
parameters that aren't part of the logical name of a script.  For example, the `theories`
pathname used in this `_CoqProject` file is omitted from the installed pathname::

  -R theories MyPackage
  theories/File1.v
  theories/SubDir/File2.v

`theories/File1.v` appears in the directory `user-contrib/MyPackage`and `theories/SubDir/File2.v`
 is in `user-contrib/MyPackage/SubDir`

Use :n:`make -f CoqMakefile install` to install a project from a directory.

If you try to step through scripts in installed packages (e.g. to understand
the proofs therein), you may get unexpected failures for two reasons (which
don't apply to scripts in the standard library, which have logical paths
beginning with `Coq`):

* `_CoqProject` files often have at least one `-R` parameter, while
  installed packages are loaded with the less-permissive `-Q` option described in
  the :cmd:`Require` command, which may cause a :cmd:`Require` to fail.  One workaround is
  to create a `_CoqProject` file containing the line `-R . <project directory>` in
  `user-contrib/<project directory>`.  In this case, the `_CoqProject` doesn't
  need to list all the source files.

* Sometimes, the `_CoqProject` file specifies options that affect the
  behavior of Coq, such as `-impredicative-set`.  These can similarly be
  added in `_CoqProject` files in `user-contrib`.

Another way to get around these problems is to download the source tree for the
project in a new directory and compile it before stepping through its scripts.

Upgrading to a new version of Coq
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

`.vo` files are specific to the version of Coq that compiled them.  When you
upgrade to a new version of Coq, you must recompile all the projects
that you want to run in the new version.  This is necessary to assure that
your proofs still work in the new version.  Once their projects build on the
new version, most users no longer have a need to run on the old version.

If, however, you want to overlap working on your project on both the old and new
versions, you'll need to create separate source directories for your project
for the different Coq versions.  Currently the compiled `.vo` files are kept
in the same directory as their corresponding `.v` file.

.. todo: Making your packages available with opam

.. _coq_makefile:

Building a Coq project with coq_makefile (details)
--------------------------------------------------

The ``coq_makefile`` tool is included with Coq and is based on generating a makefile.

The majority of Coq projects are very similar: a collection of ``.v``
files and possibly some ``.ml`` ones (a Coq plugin). The main piece of
metadata needed in order to build the project are the command line
options to ``coqc`` (e.g. ``-R``, ``-Q``, ``-I``, see :ref:`command
line options <command-line-options>`). Collecting the list of files
and options is the job of the ``_CoqProject`` file.

A ``_CoqProject`` file may contain the following kinds of entries in any order,
separated by whitespace:

* Selected options of coqc, which are forwarded directly to it. Currently these
  are ``-Q``, ``-I``, ``-R`` and ``-native-compiler``.
* ``-arg`` options for other options of coqc that don’t fall in the above set.
* Options specific to ``coq_makefile``. Currently there are two options:
  ``-generate-meta-for-package`` (see below for details), and ``-docroot``.
* Directory names, which include all appropriate files in the directory and
  its subdirectories.
* Comments, started with an unquoted ``#`` and continuing to the end of the
  line.

A simple example of a ``_CoqProject`` file follows:

::

    -R theories/ MyCode
    -arg "-w all"
    # include everything under "theories", e.g. foo.v and bar.v
    theories
    -I src/
    # include everything under "src", e.g. baz.mlg bazaux.ml and qux_plugin.mlpack
    src
    -generate-meta-for-package my-package

Lines in the form ``-arg foo`` pass the argument ``foo`` to ``coqc``: in the
example, this passes the two-word option ``-w all`` (see
:ref:`command line options <command-line-options>`).

You must specify a ``-R/-Q`` flag for your
project so its modules are properly qualified. Omitting it will
generate object files that are unusable except by experts.

Projects that include plugins (i.e. `.ml` or `.mlg` OCaml source files) must have a
``META`` file, as per `findlib <http://projects.camlcity.org/projects/findlib.html>`_.
If the project has only a single plugin, the ``META`` file can be
generated automatically when the option ``-generate-meta-for-package my-package``
is given. The generated file makes the plugin available
to the :cmd:`Declare ML Module` as ``my-package.plugin``. If the generated file
doesn't suit your needs (for instance because it depends on some OCaml
packages) or your project has multiple plugins, then create a file named
``META.my-package`` and list it in the ``_CoqProject`` file.
You can use ``ocamlfind lint META.my-package`` to lint the hand written file.
Typically ``my-package`` is the name of the ``OPAM`` package for your
project (which conventionally starts with ``coq-``). If the project
includes a ``.mlg`` file (to be pre-processed by ``coqpp``) that
declares a plugin, then the given name must match the ``findlib`` plugin
name, e.g. ``DECLARE PLUGIN "my-package.plugin"``.

The ``-native-compiler`` option given in the ``_CoqProject`` file overrides
the global one passed at configure time.

CoqIDE, Proof General, VsCoq and Coqtail all
understand ``_CoqProject`` files and can be used to invoke Coq with the desired options.

The ``coq_makefile`` utility can be used to set up a build infrastructure
for the Coq project based on makefiles. We recommend
invoking ``coq_makefile`` this way:

::

    coq_makefile -f _CoqProject -o CoqMakefile


This command generates the following files:

CoqMakefile
  is a makefile for ``GNU Make`` with targets to build the project
  (e.g. generate .vo or .html files from .v or compile .ml* files)
  and install it in the ``user-contrib`` directory where the Coq
  library is installed.

CoqMakefile.conf
  contains make variables assignments that reflect
  the contents of the ``_CoqProject`` file as well as the path relevant to
  Coq.

Run ``coq_makefile --help`` for a description of command line options.

The recommended approach is to invoke ``CoqMakefile`` from a standard
``Makefile`` in the following form:

.. example::

  ::

      # KNOWNTARGETS will not be passed along to CoqMakefile
      KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2
      # KNOWNFILES will not get implicit targets from the final rule, and so
      # depending on them won't invoke the submake
      # Warning: These files get declared as PHONY, so any targets depending
      # on them always get rebuilt
      KNOWNFILES   := Makefile _CoqProject

      .DEFAULT_GOAL := invoke-coqmakefile

      CoqMakefile: Makefile _CoqProject
              $(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

      invoke-coqmakefile: CoqMakefile
              $(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

      .PHONY: invoke-coqmakefile $(KNOWNFILES)

      ####################################################################
      ##                      Your targets here                         ##
      ####################################################################

      # This should be the last rule, to handle any targets not declared above
      %: invoke-coqmakefile
              @true

The advantage of a wrapper, compared to directly calling the generated
``Makefile``, is that it
provides a target independent of the version of Coq to regenerate a
``Makefile`` specific to the current version of Coq. Additionally, the
master ``Makefile`` can be extended with targets not specific to Coq.
Including the generated makefile with an include directive is
discouraged, since the contents of this file, including variable names and
status of rules, may change in the future.

Use the optional file ``CoqMakefile.local`` to extend
``CoqMakefile``. In particular, you can declare custom actions to run
before or after the build process. Similarly you can customize the
install target or even provide new targets. See
:ref:`coqmakefilelocal` for extension-point documentation. Although
you can use all variables defined in ``CoqMakefile`` in the *recipes*
of rules that you write and in the definitions of any variables that
you assign with ``=``, many variables are not available for use if you
assign variable values with ``:=`` nor to define the *targets* of
rules nor in top-level conditionals such as ``ifeq``. Additionally,
you must use `secondary expansion
<https://www.gnu.org/software/make/manual/html_node/Secondary-Expansion.html>`_
to make use of such variables in the prerequisites of rules. To access
variables defined in ``CoqMakefile`` in rule target computation,
top-level conditionals, and ``:=`` variable assignment, for example to
add new dependencies to compiled outputs, use the optional file
``CoqMakefile.local-late``.  See :ref:`coqmakefilelocallate` for a
non-exhaustive list of variables.

The extensions of files listed in ``_CoqProject`` determine
how they are built. In particular:


+ Coq files must use the ``.v`` extension
+ OCaml files must use the ``.ml`` or ``.mli`` extension
+ OCaml files that require pre processing for syntax
  extensions (like ``VERNAC EXTEND``) must use the ``.mlg`` extension
+ In order to generate a plugin one has to list all OCaml
  modules (i.e. ``Baz`` for ``baz.ml``) in a ``.mlpack`` file (or ``.mllib``
  file).


The use of ``.mlpack`` files has to be preferred over ``.mllib`` files,
since it results in a “packed” plugin: All auxiliary modules (as
``Baz`` and ``Bazaux``) are hidden inside the plugin’s "namespace"
(``Qux_plugin``). This reduces the chances of begin unable to load two
distinct plugins because of a clash in their auxiliary module names.

.. todo: don't want "Comments" to appear in the TOC, but won't build with "+++++++"

Comments
~~~~~~~~
``#`` outside of double quotes starts a comment that continues to the end of the
line. Comments are ignored.

Quoting arguments to coqc
+++++++++++++++++++++++++
Any string in a ``_CoqProject`` file may be enclosed in double quotes to include
whitespace characters or ``#``. For example, use ``-arg "-w all"`` to pass the
argument ``-w all`` to coqc. If the argument to coqc needs some quotes as well,
use single-quotes inside the double-quotes. For example ``-arg "-set 'Default
Goal Selector=!'"`` gets passed to coqc as ``-set 'Default Goal Selector=!'``.

But note, that single-quotes in a ``_CoqProject`` file are only special
characters if they appear in the string following ``-arg``. And on their own
they don't quote spaces. For example ``-arg 'foo bar'`` in ``_CoqProject`` is
equivalent to ``-arg foo "bar'"`` (in ``_CoqProject`` notation). ``-arg "'foo
bar'"`` behaves differently and passes ``'foo bar'`` to coqc.

Forbidden filenames
+++++++++++++++++++
The paths of files given in a ``_CoqProject`` file may not contain any of the
following characters: ``\n``, ``\t``, space, ``\``, ``'``, ``"``, ``#``, ``$``,
``%``. These characters have special meaning in Makefiles and
``coq_makefile`` doesn't support encoding them correctly.

Warning: No common logical root
+++++++++++++++++++++++++++++++
When a ``_CoqProject`` file contains something like ``-R theories Foo
theories/Bar.v``, the ``install-doc`` target installs the documentation
generated by ``coqdoc`` into ``user-contrib/Foo/``, in the folder where Coq was
installed.

But if the ``_CoqProject`` file contains something like:

::

    -R theories/Foo Foo
    -R theories/Bar Bar
    theories/Foo/Foo.v
    theories/Bar/Bar.v

the Coq files of the project don’t have a :term:`logical path` in common and
``coq_makefile`` doesn’t know where to install the documentation. It will give
a warning: "No common logical root" and generate a Makefile that installs the
documentation in some folder beginning with "orphan", in the above example,
it'd be ``user-contrib/orphan_Foo_Bar``.

In this case, specify the ``-docroot`` option in _CoqProject to override
the automatically selected logical root.

.. _coqmakefilelocal:

CoqMakefile.local
+++++++++++++++++

The optional file ``CoqMakefile.local`` is included by the generated
file ``CoqMakefile``. It can contain two kinds of directives.

**Variable assignment**

The variable must belong to the variables listed in the ``Parameters``
section of the generated makefile. These include:

:CAMLPKGS:
   can be used to specify third party findlib packages, and is
   passed to the OCaml compiler on building or linking of modules. Eg:
   ``-package yojson``.
:CAMLFLAGS:
   can be used to specify additional flags to the OCaml
   compiler, like ``-bin-annot`` or ``-w``....
:OCAMLWARN:
   it contains a default of ``-warn-error +a-3``, useful to modify
   this setting; beware this is not recommended for projects in
   Coq's CI.
:COQC, COQDEP, COQDOC:
   can be set in order to use alternative binaries
   (e.g. wrappers)
:COQ_SRC_SUBDIRS:
   can be extended by including other paths in which ``*.cm*`` files
   are searched. For example ``COQ_SRC_SUBDIRS+=user-contrib/Unicoq``
   lets you build a plugin containing OCaml code that depends on the
   OCaml code of ``Unicoq``
:COQFLAGS:
   override the flags passed to ``coqc``. By default ``-q``.
:COQEXTRAFLAGS:
   extend the flags passed to ``coqc``
:COQCHKFLAGS:
   override the flags passed to ``coqchk``.  By default ``-silent -o``.
:COQCHKEXTRAFLAGS:
   extend the flags passed to ``coqchk``
:COQDOCFLAGS:
   override the flags passed to ``coqdoc``. By default ``-interpolate -utf8``.
:COQDOCEXTRAFLAGS:
   extend the flags passed to ``coqdoc``
:COQLIBINSTALL, COQPLUGININSTALL, COQDOCINSTALL:
   specify where the Coq libraries, plugins and documentation will be installed.
   By default a combination of ``$(DESTDIR)`` (if defined) with
   ``$(COQLIB)/user-contrib``, ``$(COQCORELIB)/..`` and ``$(DOCDIR)/coq/user-contrib``.

Use :ref:`coqmakefilelocallate` instead to access more variables.

**Rule extension**

The following makefile rules can be extended.

.. example::

    ::

        pre-all::
                echo "This line is print before making the all target"
        install-extra::
                cp ThisExtraFile /there/it/goes

``pre-all::``
  run before the ``all`` target. One can use this to configure
  the project, or initialize sub modules or check dependencies are met.

``post-all::``
  run after the ``all`` target. One can use this to run a test
  suite, or compile extracted code.

``install-extra::``
  run after ``install``. One can use this to install extra files.

``install-doc::``
  One can use this to install extra doc.

``uninstall::``
  \

``uninstall-doc::``
  \

``clean::``
  \

``cleanall::``
  \

``archclean::``
  \

``merlin-hook::``
  One can append lines to the generated ``.merlin`` file extending this
  target.

.. _coqmakefilelocallate:

CoqMakefile.local-late
++++++++++++++++++++++

The optional file ``CoqMakefile.local-late`` is included at the end of the generated
file ``CoqMakefile``.  The following is a partial list of accessible variables:

:COQ_VERSION:
   the version of ``coqc`` being used, which can be used to
   provide different behavior depending on the Coq version
:COQMAKEFILE_VERSION:
   the version of Coq used to generate the
   Makefile, which can be used to detect version mismatches
:ALLDFILES:
   the list of generated dependency files, which can be used,
   for example, to cause ``make`` to recompute dependencies
   when files change by writing ``$(ALLDFILES): myfiles`` or to
   indicate that files must be generated before dependencies can
   be computed by writing ``$(ALLDFILES): | mygeneratedfiles``
:VOFILES, GLOBFILES, CMOFILES, CMXFILES, OFILES, CMAFILES, CMXAFILES, CMIFILES, CMXSFILES:
   lists of files that are generated by various invocations of the compilers

In addition, the following variables may be useful for
deciding what targets to present via ``$(shell ...)``; these
variables are already accessible in recipes for rules added in
``CoqMakefile.local``, but are only accessible from top-level ``$(shell
...)`` invocations in ``CoqMakefile.local-late``:

:COQC, COQDEP, COQDOC, CAMLC, CAMLOPTC:
   compiler binaries
:COQFLAGS, CAMLFLAGS, COQLIBS, COQDEBUG, OCAMLLIBS:
   flags passed to the Coq or OCaml compilers

Timing targets and performance testing
++++++++++++++++++++++++++++++++++++++

The generated ``Makefile`` supports the generation of three kinds of
timing data: per-file build-times, per-line times for an individual
file, and profiling data in Google trace format for an individual
file.

The following targets and Makefile variables allow collection of per-
file timing data:


+ ``TIMED=1``
    passing this variable will cause ``make`` to emit a line
    describing the user-space build-time and peak memory usage for each
    file built.

    .. note::
      On ``Mac OS``, this works best if you’ve installed ``gnu-time``.

    .. example::

       For example, the output of ``make TIMED=1`` may look like
       this:

       ::

          COQDEP Fast.v
          COQDEP Slow.v
          COQC Slow.v
          Slow.vo (user: 0.34 mem: 395448 ko)
          COQC Fast.v
          Fast.vo (user: 0.01 mem: 45184 ko)

+ ``pretty-timed``
    this target stores the output of ``make TIMED=1`` into
    ``time-of-build.log``, and displays a table of the times and peak
    memory usages, sorted from slowest to fastest, which is also
    stored in ``time-of-build-pretty.log``.  If you want to construct
    the ``log`` for targets other than the default one, you can pass
    them via the variable ``TGTS``, e.g., ``make pretty-timed
    TGTS="a.vo b.vo"``.

    .. note::
       This target requires ``python`` to build the table.

    .. note::
       This target will *append* to the timing log; if you want a
       fresh start, you must remove the file ``time-of-build.log`` or
       ``run make cleanall``.

    .. note::
       By default the table displays user times.  If the build log
       contains real times (which it does by default), passing
       ``TIMING_REAL=1`` to ``make pretty-timed`` will use real times
       rather than user times in the table.

    .. note::
       Passing ``TIMING_INCLUDE_MEM=0`` to ``make`` will result in the
       tables not including peak memory usage information.  Passing
       ``TIMING_SORT_BY_MEM=1`` to ``make`` will result in the tables
       be sorted by peak memory usage rather than by the time taken.

    .. example::

      For example, the output of ``make pretty-timed`` may look like this:

      ::

        COQDEP VFILES
        COQC Slow.v
        Slow.vo (real: 0.52, user: 0.39, sys: 0.12, mem: 394648 ko)
        COQC Fast.v
        Fast.vo (real: 0.06, user: 0.02, sys: 0.03, mem: 56980 ko)
            Time |  Peak Mem | File Name
        --------------------------------------------
        0m00.41s | 394648 ko | Total Time / Peak Mem
        --------------------------------------------
        0m00.39s | 394648 ko | Slow.vo
        0m00.02s |  56980 ko | Fast.vo


+ ``print-pretty-timed-diff``
    this target builds a table of timing changes between two compilations; run
    ``make make-pretty-timed-before`` to build the log of the “before” times,
    and run ``make make-pretty-timed-after`` to build the log of the “after”
    times. The table is printed on the command line, and stored in
    ``time-of-build-both.log``. This target is most useful for profiling the
    difference between two commits in a repository.

    .. note::
       This target requires ``python`` to build the table.

    .. note::
       The ``make-pretty-timed-before`` and ``make-pretty-timed-after`` targets will
       *append* to the timing log; if you want a fresh start, you must remove
       the files ``time-of-build-before.log`` and ``time-of-build-after.log`` or run
       ``make cleanall`` *before* building either the “before” or “after”
       targets.

    .. note::
       The table will be sorted first by absolute time
       differences rounded towards zero to a whole-number of seconds, then by
       times in the “after” column, and finally lexicographically by file
       name. This will put the biggest changes in either direction first, and
       will prefer sorting by build-time over subsecond changes in build time
       (which are frequently noise); lexicographic sorting forces an order on
       files which take effectively no time to compile.

       If you prefer a different sorting order, you can pass
       ``TIMING_SORT_BY=absolute`` to sort by the total time taken, or
       ``TIMING_SORT_BY=diff`` to sort by the signed difference in
       time.

    .. note::
       Just like ``pretty-timed``, this table defaults to using user
       times.  Pass ``TIMING_REAL=1`` to ``make`` on the command line
       to show real times instead.

    .. note::
       Just like ``pretty-timed``, passing ``TIMING_INCLUDE_MEM=0`` to
       ``make`` will result in the tables not including peak memory
       usage information.  Passing ``TIMING_SORT_BY_MEM=1`` to
       ``make`` will result in the tables be sorted by peak memory
       usage rather than by the time taken.

    .. example::

        For example, the output table from
        ``make print-pretty-timed-diff`` may look like this:

        ::

             After |  Peak Mem | File Name             |   Before |  Peak Mem ||    Change || Change (mem) |  % Change | % Change (mem)
          -----------------------------------------------------------------------------------------------------------------------------
          0m00.43s | 394700 ko | Total Time / Peak Mem | 0m00.41s | 394648 ko || +0m00.01s ||        52 ko |    +4.87% |         +0.01%
          -----------------------------------------------------------------------------------------------------------------------------
          0m00.39s | 394700 ko | Fast.vo               | 0m00.02s |  56980 ko || +0m00.37s ||    337720 ko | +1850.00% |       +592.69%
          0m00.04s |  56772 ko | Slow.vo               | 0m00.39s | 394648 ko || -0m00.35s ||   -337876 ko |   -89.74% |        -85.61%


The following targets and ``Makefile`` variables allow collection of per-
line timing data:


+ ``TIMING=1``
    passing this variable will cause ``make`` to use ``coqc -time-file`` to
    write to a ``.v.timing`` file for each ``.v`` file compiled, which contains
    line-by-line timing information.

    .. example::

       For example, running ``make all TIMING=1`` may result in a file like this:

       ::

          Chars 0 - 26 [Require~Coq.ZArith.BinInt.] 0.157 secs (0.128u,0.028s)
          Chars 27 - 68 [Declare~Reduction~comp~:=~vm_c...] 0. secs (0.u,0.s)
          Chars 69 - 162 [Definition~foo0~:=~Eval~comp~i...] 0.153 secs (0.136u,0.019s)
          Chars 163 - 208 [Definition~foo1~:=~Eval~comp~i...] 0.239 secs (0.236u,0.s)

+ ``coqtimelog2html``
    ::

       coqtimelog2html file.v file.v.time1 [file.v.time2 [file.v.time3]] > file.v.html

    this command produces a HTML file displaying the original `file.v`
    with highlights for each command indicating how much time the
    command used according to the given timing files. It supports
    between 1 and 3 timing files.

    There is currently no `coq_makefile` target that automatically invokes this tool.

+ ``print-pretty-single-time-diff``
    ::

       print-pretty-single-time-diff AFTER=path/to/file.v.after-timing BEFORE=path/to/file.v.before-timing

    this target will make a sorted table of the per-line timing differences
    between the timing logs in the ``BEFORE`` and ``AFTER`` files, display it, and
    save it to the file specified by the ``TIME_OF_PRETTY_BUILD_FILE`` variable,
    which defaults to ``time-of-build-pretty.log``.
    To generate the ``.v.before-timing`` or ``.v.after-timing`` files, you should
    pass  ``TIMING=before`` or ``TIMING=after`` rather than ``TIMING=1``.

    .. note::
       The sorting used here is the same as in the ``print-pretty-timed-diff`` target.

    .. note::
       This target requires python to build the table.

    .. note::
       This target follows the same sorting order as the
       ``print-pretty-timed-diff`` target, and supports the same
       options for the ``TIMING_SORT_BY`` variable.

    .. note::
       By default, two lines are only considered the same if the
       character offsets and initial code strings are identical.  Passing
       ``TIMING_FUZZ=N`` relaxes this constraint by allowing the
       character locations to differ by up to ``N``, as long
       as the total number of characters and initial code strings
       continue to match.  This is useful when there are small changes
       to a file, and you want to match later lines that have not
       changed even though the character offsets have changed.

    .. note::
       By default the table picks up real times, under the assumption
       that when comparing line-by-line, the real time is a more
       accurate representation as it includes disk time and time spent
       in the native compiler.  Passing ``TIMING_REAL=0`` to ``make``
       will use user times rather than real times in the table.

    .. example::

       For example, running  ``print-pretty-single-time-diff`` might give a table like this:

       ::

          After     | Code                                                | Before    || Change    | % Change
          ---------------------------------------------------------------------------------------------------
          0m00.50s  | Total                                               | 0m04.17s  || -0m03.66s | -87.96%
          ---------------------------------------------------------------------------------------------------
          0m00.145s | Chars 069 - 162 [Definition~foo0~:=~Eval~comp~i...] | 0m00.192s || -0m00.04s | -24.47%
          0m00.126s | Chars 000 - 026 [Require~Coq.ZArith.BinInt.]        | 0m00.143s || -0m00.01s | -11.88%
             N/A    | Chars 027 - 068 [Declare~Reduction~comp~:=~nati...] | 0m00.s    || +0m00.00s | N/A
          0m00.s    | Chars 027 - 068 [Declare~Reduction~comp~:=~vm_c...] |    N/A    || +0m00.00s | N/A
          0m00.231s | Chars 163 - 208 [Definition~foo1~:=~Eval~comp~i...] | 0m03.836s || -0m03.60s | -93.97%


+ ``all.timing.diff``, ``path/to/file.v.timing.diff``
    The ``path/to/file.v.timing.diff`` target will make a ``.v.timing.diff`` file for
    the corresponding ``.v`` file, with a table as would be generated by
    the ``print-pretty-single-time-diff`` target; it depends on having already
    made the corresponding ``.v.before-timing`` and ``.v.after-timing`` files,
    which can be made by passing ``TIMING=before`` and ``TIMING=after``.
    The  ``all.timing.diff`` target will make such timing difference files for
    all of the ``.v`` files that the ``Makefile`` knows about. It will fail if
    some ``.v.before-timing`` or ``.v.after-timing`` files don’t exist.

    .. note::
      This target requires python to build the table.

+ ``PROFILE=1``
  passing this variable or setting it in the environment will cause
  ``make`` to use ``coqc -profile`` to write to a ``.v.prof.json``
  file for each ``.v`` file compiled, which contains :ref:`profiling`
  information.

  The ``.v.prof.json`` is then compressed by ``gzip`` to a ``.v.prof.json.gz``.

Building a subset of the targets with ``-j``
++++++++++++++++++++++++++++++++++++++++++++

To build, say, two targets foo.vo and bar.vo in parallel one can use
``make only TGTS="foo.vo bar.vo" -j``.

.. note::

  ``make foo.vo bar.vo -j`` has a different meaning for the ``make``
  utility, in particular it may build a shared prerequisite twice.

Precompiling for ``native_compute``
+++++++++++++++++++++++++++++++++++

To compile files for ``native_compute``, one can use the
``-native-compiler yes`` option of Coq, by putting it in the ``_CoqProject``
file.

The generated installation target of ``CoqMakefile`` will then take care of
installing the extra ``.coq-native`` directories.

.. note::

   As an alternative to modifying ``_CoqProject``, one can set an
   environment variable when calling ``make``:

   ::

      COQEXTRAFLAGS="-native-compiler yes" make

   This can be useful when files cannot be modified, for instance when
   installing via OPAM a package built with ``coq_makefile``:

   ::

      COQEXTRAFLAGS="-native-compiler yes" opam install coq-package

.. note::

   This requires all dependencies to be themselves compiled with
   ``-native-compiler yes``.

The grammar of _CoqProject
++++++++++++++++++++++++++
A ``_CoqProject`` file encodes a list of strings using the following syntax:

  .. prodn::
     CoqProject ::= {* {| @blank | @comment | @quoted_string | @unquoted_string } }
     blank ::= {| space | horizontal_tab | newline }
     comment ::= # {* comment_char } newline
     quoted_string ::= " {* quoted_char } "
     unquoted_string ::= string_start_char {* unquoted_char }

where the following definitions apply:

* :n:`space`, :n:`horizontal_tab` and :n:`newline` stand for the corresponding
  ASCII characters.
* :n:`comment_char` is the set of all characters except :n:`newline`.
* :n:`quoted_char` is the set of all characters except ``"``.
* :n:`string_start_char` is the set of all characters except those that match :n:`@blank`, or are ``"`` or ``#``.
* :n:`unquoted_char` is the set of all characters except those that match :n:`@blank` or are ``#``.

The parser produces a list of strings in the same order as they were
encountered in ``_CoqProject``. Blanks and comments are removed
and the double quotes of :n:`@quoted_string` tokens are removed as
well. The list is then treated as a list of command-line arguments of
``coq_makefile``.

The semantics of ``-arg`` are as follows: the string given as argument is split
on whitespace, but single quotes prevent splitting. The resulting list of
strings is then passed to coqc.

The current approach has a few limitations: Double quotes in a ``_CoqProject``
file are only special characters at the start of a string. For lack of an
escaping mechanism, it is currently impossible to pass the following kinds of
strings to ``coq_makefile`` using a ``_CoqProject`` file:

* strings starting with ``"``
* strings starting with ``#`` and containing ``"``
* strings containing both whitespace and ``"``

In addition, it is impossible to pass strings containing ``'`` to coqc via
``-arg``.

.. _building_dune:

Building a Coq project with Dune
--------------------------------

Dune, the standard OCaml build tool, has supported building Coq libraries since version 1.9.

.. note::

   Dune's Coq support is still experimental; we strongly recommend
   using Dune 3.2 or later.

.. note::

   The canonical documentation for the Coq Dune extension is
   maintained upstream; please refer to the `Dune manual
   <https://dune.readthedocs.io/>`_ for up-to-date information. The
   documentation below is up to date for Dune 3.2

Building a Coq project with Dune requires setting up a Dune project
for your files. This involves adding a ``dune-project`` and
``pkg.opam`` file to the root (``pkg.opam`` can be empty or generated
by Dune itself), and then providing ``dune`` files in the directories
your ``.v`` files are placed. For the experimental version "0.3" of
the Coq Dune language, Coq library stanzas look like:

.. code:: scheme

    (coq.theory
     (name <module_prefix>)
     (package <opam_package>)
     (synopsis <text>)
     (modules <ordered_set_lang>)
     (libraries <ocaml_libraries>)
     (flags <coq_flags>))

This stanza will build all `.v` files in the given directory, wrapping
the library under ``<module_prefix>``. If you declare an
``<opam_package>``, an ``.install`` file for the library will be
generated; the optional ``(modules <ordered_set_lang>)`` field allows
you to filter the list of modules, and ``(libraries
<ocaml_libraries>)`` allows the Coq theory depend on ML plugins. For
the moment, Dune relies on Coq's standard mechanisms (such as
``COQPATH``) to locate installed Coq libraries.

By default Dune will skip ``.v`` files present in subdirectories. In
order to enable the usual recursive organization of Coq projects add

.. code:: scheme

    (include_subdirs qualified)

to your ``dune`` file.

Once your project is set up, `dune build` will generate the
`pkg.install` files and all the files necessary for the installation
of your project.

Note that projects using Dune to build need to use the compatibility
syntax for `Declare ML Module`, see example below:

.. example::

   A typical stanza for a Coq plugin is split into two parts. An OCaml build directive, which is standard Dune:

   .. code:: scheme

       (library
        (name equations_plugin)
        (public_name equations.plugin)
        (flags :standard -warn-error -3-9-27-32-33-50)
        (libraries coq.plugins.cc coq.plugins.extraction))

       (coq.pp (modules g_equations))

   And a Coq-specific part that depends on it via the ``libraries`` field:

   .. code:: scheme

       (coq.theory
        (name Equations) ; -R flag
        (package equations)
        (synopsis "Equations Plugin")
        (libraries coq.plugins.extraction equations.plugin)
        (modules :standard \ IdDec NoCycle)) ; exclude some modules that don't build

       (include_subdirs qualified)

   For now, each ``.v`` file that loads the plugin must use
   the following special syntax on its `Declare ML Module`
   command for compatibility with current Dune versions (as of Coq 8.16):

   .. code:: coq

       Declare ML Module "equations_plugin:equations.plugin".

.. _coqdep:

coqdep: Computing Module dependencies
-------------------------------------

In order to compute module dependencies (to be used by ``make`` or
``dune``), Coq provides the ``coqdep`` tool.

``coqdep`` computes inter-module dependencies for Coq
programs, and prints the dependencies on the standard output in a
format readable by make. When a directory is given as argument, it is
recursively looked at.

Dependencies of Coq modules are computed by looking at :cmd:`Require`
and :cmd:`Declare ML Module` commands.

See the man page of ``coqdep`` for more details and options.

Both Dune and ``coq_makefile`` use ``coqdep`` to compute the
dependencies among the files part of a Coq project.

.. _coqnative:

Split compilation of native computation files
---------------------------------------------

Coq features a :tacn:`native_compute` tactic to provide fast computation in the
kernel. This process performs compilation of Coq terms to OCaml programs using
the OCaml compiler, which may cause an important overhead. Hence native
compilation is an opt-in configure flag.

When native compilation is activated, Coq generates the compiled files upfront,
i.e. during the ``coqc`` invocation on the corresponding ``.v`` file. This is
impractical because it means one must chose in advance whether they will use
a native-capable Coq installation. In particular, activating native compilation
forces the recompilation of the whole Coq installation. See
:ref:`command line options <command-line-options>` for more details.

Starting from Coq 8.14, a new binary ``coqnative`` is available. It allows
performing split native compilation by generating the native compute files out
of the compiled ``.vo`` file rather than out of the source ``.v`` file.

The ``coqnative`` command takes a name *file.vo* as argument and tries to
perform native compilation on it. It assumes that the Coq libraries on which
*file.vo* depends have been first compiled to their native files, and will fail
otherwise. It accepts the ``-R``, ``-Q``, ``-I`` and ``-nI`` arguments with the
same semantics as if the native compilation process had been performed through
``coqc``. In particular, it means that:

+ ``-R`` and ``-Q`` are equivalent

+ ``-I`` is a no-op that is accepted only for scripting convenience

Using Coq as a library
------------------------

In previous versions, ``coqmktop`` was used to build custom
toplevels - for example for better debugging or custom static
linking. Nowadays, the preferred method is to use ``ocamlfind``.

The most basic custom toplevel is built using:

::

   % ocamlfind ocamlopt -thread -linkall -linkpkg \
                 -package coq.toplevel \
                 topbin/coqtop_bin.ml -o my_toplevel.native


For example, to statically link |Ltac|, you can just do:

::

   % ocamlfind ocamlopt -thread -linkall -linkpkg \
                 -package coq.toplevel,coq.plugins.ltac \
                 topbin/coqtop_bin.ml -o my_toplevel.native

and similarly for other plugins.

Embedded Coq phrases inside |Latex| documents
-----------------------------------------------

When writing documentation about a proof development, one may want
to insert Coq phrases inside a |Latex| document, possibly together
with the corresponding answers of the system. We provide a mechanical
way to process such Coq phrases embedded in |Latex| files: the ``coq-tex``
filter. This filter extracts Coq phrases embedded in |Latex| files,
evaluates them, and insert the outcome of the evaluation after each
phrase.

Starting with a file ``file.tex`` containing Coq phrases, the ``coq-tex``
filter produces a file named ``file.v.tex`` with the Coq outcome.

There are options to produce the Coq parts in smaller font, italic,
between horizontal rules, etc. See the man page of ``coq-tex`` for more
details.


Man pages
---------

There are man pages for the commands ``coqdep`` and ``coq-tex``. Man
pages are installed at installation time (see installation
instructions in file ``INSTALL``, step 6).
