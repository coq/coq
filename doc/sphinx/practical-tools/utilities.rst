.. _utilities:

---------------------
 Utilities
---------------------

The distribution provides utilities to simplify some tedious works
beside proof development, tactics writing or documentation.


Using Coq as a library
----------------------

In previous versions, ``coqmktop`` was used to build custom
toplevels - for example for better debugging or custom static
linking. Nowadays, the preferred method is to use ``ocamlfind``.

The most basic custom toplevel is built using:

::

   % ocamlfind ocamlopt -thread -rectypes -linkall -linkpkg \
                 -package coq.toplevel \
                 topbin/coqtop_bin.ml -o my_toplevel.native


For example, to statically link |Ltac|, you can just do:

::

   % ocamlfind ocamlopt -thread -rectypes -linkall -linkpkg \
                 -package coq.toplevel,coq.plugins.ltac \
                 topbin/coqtop_bin.ml -o my_toplevel.native

and similarly for other plugins.

Building a |Coq| project
------------------------

As of today it is possible to build Coq projects using two tools:

- coq_makefile, which is distributed by Coq and is based on generating a makefile,
- Dune, the standard OCaml build tool, which, since version 1.9, supports building Coq libraries.

.. _coq_makefile:

Building a |Coq| project with coq_makefile
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The majority of |Coq| projects are very similar: a collection of ``.v``
files and eventually some ``.ml`` ones (a |Coq| plugin). The main piece of
metadata needed in order to build the project are the command line
options to ``coqc`` (e.g. ``-R``, ``Q``, ``-I``, see :ref:`command
line options <command-line-options>`). Collecting the list of files
and options is the job of the ``_CoqProject`` file.

A simple example of a ``_CoqProject`` file follows:

::

    -R theories/ MyCode
    -arg -w
    -arg all
    theories/foo.v
    theories/bar.v
    -I src/
    src/baz.mlg
    src/bazaux.ml
    src/qux_plugin.mlpack

where options ``-R``, ``-Q`` and ``-I`` are natively recognized, as well as
file names. The lines of the form ``-arg foo`` are used in order to tell
to literally pass an argument ``foo`` to ``coqc``: in the
example, this allows to pass the two-word option ``-w all`` (see
:ref:`command line options <command-line-options>`).

|CoqIDE|, Proof-General and VSCoq all
understand ``_CoqProject`` files and can be used to invoke |Coq| with the desired options.

The ``coq_makefile`` utility can be used to set up a build infrastructure
for the |Coq| project based on makefiles. The recommended way of
invoking ``coq_makefile`` is the following one:

::

    coq_makefile -f _CoqProject -o CoqMakefile


Such command generates the following files:

CoqMakefile
  is a generic makefile for ``GNU Make`` that provides
  targets to build the project (both ``.v`` and ``.ml*`` files), to install it
  system-wide in the ``coq-contrib`` directory (i.e. where |Coq| is installed)
  as well as to invoke coqdoc to generate HTML documentation.

CoqMakefile.conf
  contains make variables assignments that reflect
  the contents of the ``_CoqProject`` file as well as the path relevant to
  |Coq|.


An optional file ``CoqMakefile.local`` can be provided by the user in order to
extend ``CoqMakefile``. In particular one can declare custom actions to be
performed before or after the build process. Similarly one can customize the
install target or even provide new targets. Extension points are documented in
paragraph :ref:`coqmakefilelocal`.

The extensions of the files listed in ``_CoqProject`` is used in order to
decide how to build them. In particular:


+ |Coq| files must use the ``.v`` extension
+ |OCaml| files must use the ``.ml`` or ``.mli`` extension
+ |OCaml| files that require pre processing for syntax
  extensions (like ``VERNAC EXTEND``) must use the ``.mlg`` extension
+ In order to generate a plugin one has to list all |OCaml|
  modules (i.e. ``Baz`` for ``baz.ml``) in a ``.mlpack`` file (or ``.mllib``
  file).


The use of ``.mlpack`` files has to be preferred over ``.mllib`` files,
since it results in a “packed” plugin: All auxiliary modules (as
``Baz`` and ``Bazaux``) are hidden inside the plugin’s "namespace"
(``Qux_plugin``). This reduces the chances of begin unable to load two
distinct plugins because of a clash in their auxiliary module names.

.. _coqmakefilelocal:

CoqMakefile.local
+++++++++++++++++

The optional file ``CoqMakefile.local`` is included by the generated
file ``CoqMakefile``. It can contain two kinds of directives.

**Variable assignment**

The variable must belong to the variables listed in the ``Parameters``
section of the generated makefile.
Here we describe only few of them.

:CAMLPKGS:
   can be used to specify third party findlib packages, and is
   passed to the OCaml compiler on building or linking of modules. Eg:
   ``-package yojson``.
:CAMLFLAGS:
   can be used to specify additional flags to the |OCaml|
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
:COQLIBINSTALL, COQDOCINSTALL:
   specify where the Coq libraries and documentation will be installed.
   By default a combination of ``$(DESTDIR)`` (if defined) with
   ``$(COQLIB)/user-contrib`` and ``$(DOCDIR)/user-contrib``.

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

Timing targets and performance testing
++++++++++++++++++++++++++++++++++++++

The generated ``Makefile`` supports the generation of two kinds of timing
data: per-file build-times, and per-line times for an individual file.

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
    passing this variable will cause ``make`` to use ``coqc -time`` to
    write to a ``.v.timing`` file for each ``.v`` file compiled, which contains
    line-by-line timing information.

    .. example::

       For example, running ``make all TIMING=1`` may result in a file like this:

       ::

          Chars 0 - 26 [Require~Coq.ZArith.BinInt.] 0.157 secs (0.128u,0.028s)
          Chars 27 - 68 [Declare~Reduction~comp~:=~vm_c...] 0. secs (0.u,0.s)
          Chars 69 - 162 [Definition~foo0~:=~Eval~comp~i...] 0.153 secs (0.136u,0.019s)
          Chars 163 - 208 [Definition~foo1~:=~Eval~comp~i...] 0.239 secs (0.236u,0.s)

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


Reusing/extending the generated Makefile
++++++++++++++++++++++++++++++++++++++++

Including the generated makefile with an include directive is
discouraged. The contents of this file, including variable names and
status of rules shall change in the future. Users are advised to
include ``Makefile.conf`` or call a target of the generated Makefile as in
``make -f Makefile target`` from another Makefile.

One way to get access to all targets of the generated ``CoqMakefile`` is to
have a generic target for invoking unknown targets.

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



Building a subset of the targets with ``-j``
++++++++++++++++++++++++++++++++++++++++++++

To build, say, two targets foo.vo and bar.vo in parallel one can use
``make only TGTS="foo.vo bar.vo" -j``.

.. note::

  ``make foo.vo bar.vo -j`` has a different meaning for the make
  utility, in particular it may build a shared prerequisite twice.


.. note::

  For users of coq_makefile with version < 8.7

  + Support for "subdirectory" is deprecated. To perform actions before
    or after the build (like invoking ``make`` on a subdirectory) one can hook
    in pre-all and post-all extension points.
  + ``-extra-phony`` and ``-extra`` are deprecated. To provide additional target
    (``.PHONY`` or not) please use ``CoqMakefile.local``.


Precompiling for ``native_compute``
+++++++++++++++++++++++++++++++++++

To compile files for ``native_compute``, one can use the
``-native-compiler yes`` option of |Coq|, for instance by putting the
following in a :ref:`coqmakefilelocal` file:

::

    COQEXTRAFLAGS += -native-compiler yes

The generated ``CoqMakefile`` installation target will then take care
of installing the extra ``.coq-native`` directories.

.. note::

   As an alternative to modifying any file, one can set the
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

Building a |Coq| project with Dune
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. note::

   Dune's Coq support is still experimental; we strongly recommend
   using Dune 2.3 or later.

.. note::

   The canonical documentation for the Coq Dune extension is
   maintained upstream; please refer to the `Dune manual
   <https://dune.readthedocs.io/>`_ for up-to-date information. This
   documentation is up to date for Dune 2.3.

Building a Coq project with Dune requires setting up a Dune project
for your files. This involves adding a ``dune-project`` and
``pkg.opam`` file to the root (``pkg.opam`` can be empty or generated
by Dune itself), and then providing ``dune`` files in the directories
your ``.v`` files are placed. For the experimental version "0.1" of
the Coq Dune language, |Coq| library stanzas look like:

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

to you ``dune`` file.

Once your project is set up, `dune build` will generate the
`pkg.install` files and all the files necessary for the installation
of your project.

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

.. _coqdep:

Computing Module dependencies
-----------------------------

In order to compute module dependencies (to be used by ``make`` or
``dune``), |Coq| provides the ``coqdep`` tool.

``coqdep`` computes inter-module dependencies for |Coq|
programs, and prints the dependencies on the standard output in a
format readable by make. When a directory is given as argument, it is
recursively looked at.

Dependencies of |Coq| modules are computed by looking at ``Require``
commands (``Require``, ``Require Export``, ``Require Import``), but also at the
command ``Declare ML Module``.

See the man page of ``coqdep`` for more details and options.

Both Dune and ``coq_makefile`` use ``coqdep`` to compute the
dependencies among the files part of a Coq project.

Embedded Coq phrases inside |Latex| documents
---------------------------------------------

When writing documentation about a proof development, one may want
to insert |Coq| phrases inside a |Latex| document, possibly together
with the corresponding answers of the system. We provide a mechanical
way to process such |Coq| phrases embedded in |Latex| files: the ``coq-tex``
filter. This filter extracts |Coq| phrases embedded in |Latex| files,
evaluates them, and insert the outcome of the evaluation after each
phrase.

Starting with a file ``file.tex`` containing |Coq| phrases, the ``coq-tex``
filter produces a file named ``file.v.tex`` with the Coq outcome.

There are options to produce the |Coq| parts in smaller font, italic,
between horizontal rules, etc. See the man page of ``coq-tex`` for more
details.


Man pages
---------

There are man pages for the commands ``coqdep`` and ``coq-tex``. Man
pages are installed at installation time (see installation
instructions in file ``INSTALL``, step 6).
