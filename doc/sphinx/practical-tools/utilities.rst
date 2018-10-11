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


Building a |Coq| project with coq_makefile
------------------------------------------

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
    src/baz.ml4
    src/bazaux.ml
    src/qux_plugin.mlpack

where options ``-R``, ``-Q`` and ``-I`` are natively recognized, as well as
file names. The lines of the form ``-arg foo`` are used in order to tell
to literally pass an argument ``foo`` to ``coqc``: in the
example, this allows to pass the two-word option ``-w all`` (see
:ref:`command line options <command-line-options>`).

Currently, both |CoqIDE| and Proof-General (version ≥ ``4.3pre``)
understand ``_CoqProject`` files and invoke |Coq| with the desired options.

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
  extensions (like ``VERNAC EXTEND``) must use the ``.ml4`` extension
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
~~~~~~~~~~~~~~~~~

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
          Slow (user: 0.34 mem: 395448 ko)
          COQC Fast.v
          Fast (user: 0.01 mem: 45184 ko)

+ ``pretty-timed``
    this target stores the output of ``make TIMED=1`` into
    ``time-of-build.log``, and displays a table of the times, sorted from
    slowest to fastest, which is also stored in ``time-of-build-pretty.log``.
    If you want to construct the ``log`` for targets other than the default
    one, you can pass them via the variable ``TGTS``, e.g., ``make pretty-timed
    TGTS="a.vo b.vo"``.

    .. ::
       This target requires ``python`` to build the table.

    .. note::
       This target will *append* to the timing log; if you want a
       fresh start, you must remove the ``filetime-of-build.log`` or
       ``run make cleanall``.

    .. example::

      For example, the output of ``make pretty-timed`` may look like this:

      ::

        COQDEP Fast.v
        COQDEP Slow.v
        COQC Slow.v
        Slow (user: 0.36 mem: 393912 ko)
        COQC Fast.v
        Fast (user: 0.05 mem: 45992 ko)
        Time     | File Name
        --------------------
        0m00.41s | Total
        --------------------
        0m00.36s | Slow
        0m00.05s | Fast


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

    .. example::

        For example, the output table from
        ``make print-pretty-timed-diff`` may look like this:

        ::

          After    | File Name | Before   || Change    | % Change
          --------------------------------------------------------
          0m00.39s | Total     | 0m00.35s || +0m00.03s | +11.42%
          --------------------------------------------------------
          0m00.37s | Slow      | 0m00.01s || +0m00.36s | +3600.00%
          0m00.02s | Fast      | 0m00.34s || -0m00.32s | -94.11%


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

       print-pretty-single-time-diff BEFORE=path/to/file.v.before-timing AFTER=path/to/file.v.after-timing

    this target will make a sorted table of the per-line timing differences
    between the timing logs in the ``BEFORE`` and ``AFTER`` files, display it, and
    save it to the file specified by the ``TIME_OF_PRETTY_BUILD_FILE`` variable,
    which defaults to ``time-of-build-pretty.log``.
    To generate the ``.v.before-timing`` or ``.v.after-timing`` files, you should
    pass  ``TIMING=before`` or ``TIMING=after`` rather than ``TIMING=1``.

    .. note::
       The sorting used here is the same as in the ``print-pretty-timed -diff`` target.

    .. note::
       This target requires python to build the table.

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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



Module dependencies
--------------------

In order to compute module dependencies (so to use ``make``), |Coq| comes
with an appropriate tool, ``coqdep``.

``coqdep`` computes inter-module dependencies for |Coq| and |OCaml|
programs, and prints the dependencies on the standard output in a
format readable by make. When a directory is given as argument, it is
recursively looked at.

Dependencies of |Coq| modules are computed by looking at ``Require``
commands (``Require``, ``Require Export``, ``Require Import``), but also at the
command ``Declare ML Module``.

Dependencies of |OCaml| modules are computed by looking at
`open` commands and the dot notation *module.value*. However, this is
done approximately and you are advised to use ``ocamldep`` instead for the
|OCaml| module dependencies.

See the man page of ``coqdep`` for more details and options.

The build infrastructure generated by ``coq_makefile`` uses ``coqdep`` to
automatically compute the dependencies among the files part of the
project.


.. _coqdoc:

Documenting |Coq| files with coqdoc
-----------------------------------

coqdoc is a documentation tool for the proof assistant |Coq|, similar to
``javadoc`` or ``ocamldoc``. The task of coqdoc is


#. to produce a nice |Latex| and/or HTML document from |Coq| source files,
   readable for a human and not only for the proof assistant;
#. to help the user navigate his own (or third-party) sources.



Principles
~~~~~~~~~~

Documentation is inserted into |Coq| files as *special comments*. Thus
your files will compile as usual, whether you use coqdoc or not. coqdoc
presupposes that the given |Coq| files are well-formed (at least
lexically). Documentation starts with ``(**``, followed by a space, and
ends with ``*)``. The documentation format is inspired by Todd
A. Coram’s *Almost Free Text (AFT)* tool: it is mainly ``ASCII`` text with
some syntax-light controls, described below. coqdoc is robust: it
shouldn’t fail, whatever the input is. But remember: “garbage in,
garbage out”.


|Coq| material inside documentation.
++++++++++++++++++++++++++++++++++++

|Coq| material is quoted between the delimiters ``[`` and ``]``. Square brackets
may be nested, the inner ones being understood as being part of the
quoted code (thus you can quote a term like ``fun x => u`` by writing  ``[fun
x => u]``). Inside quotations, the code is pretty-printed in the same
way as it is in code parts.

Preformatted vernacular is enclosed by ``[[`` and ``]]``. The former must be
followed by a newline and the latter must follow a newline.


Pretty-printing.
++++++++++++++++

coqdoc uses different faces for identifiers and keywords. The pretty-
printing of |Coq| tokens (identifiers or symbols) can be controlled
using one of the following commands:

::


    (** printing  *token* %...LATEX...% #...html...# *)


or

::


    (** printing  *token* $...LATEX math...$ #...html...# *)


It gives the |Latex| and HTML texts to be produced for the given |Coq|
token. Either the |Latex| or the HTML rule may be omitted, causing the
default pretty-printing to be used for this token.

The printing for one token can be removed with

::


    (** remove printing  *token* *)


Initially, the pretty-printing table contains the following mapping:

===== === ==== ===== === ==== ==== ===
`->`   →       `<-`   ←       `*`   ×
`<=`   ≤       `>=`   ≥       `=>`  ⇒
`<>`   ≠       `<->`  ↔       `|-`  ⊢
`\\/`  ∨       `/\\`  ∧       `~`   ¬
===== === ==== ===== === ==== ==== ===

Any of these can be overwritten or suppressed using the printing
commands.

.. note::

   The recognition of tokens is done by a (``ocaml``) lex
   automaton and thus applies the longest-match rule. For instance, `->~`
   is recognized as a single token, where |Coq| sees two tokens. It is the
   responsibility of the user to insert space between tokens *or* to give
   pretty-printing rules for the possible combinations, e.g.

   ::

      (** printing ->~ %\ensuremath{\rightarrow\lnot}% *)



Sections
++++++++

Sections are introduced by 1 to 4 asterisks at the beginning of a line
followed by a space and the title of the section. One asterisk is a section,
two a subsection, etc.

.. example::

   ::

          (** * Well-founded relations

              In this section, we introduce...  *)


Lists.
++++++

List items are introduced by a leading dash. coqdoc uses whitespace to
determine the depth of a new list item and which text belongs in which
list items. A list ends when a line of text starts at or before the
level of indenting of the list’s dash. A list item’s dash must always
be the first non-space character on its line (so, in particular, a
list can not begin on the first line of a comment - start it on the
second line instead).

.. example::

  ::

           We go by induction on [n]:
           - If [n] is 0...
           - If [n] is [S n'] we require...

             two paragraphs of reasoning, and two subcases:

             - In the first case...
             - In the second case...

           So the theorem holds.



Rules.
++++++

More than 4 leading dashes produce a horizontal rule.


Emphasis.
+++++++++

Text can be italicized by enclosing it in underscores. A non-identifier
character must precede the leading underscore and follow the trailing
underscore, so that uses of underscores in names aren’t mistaken for
emphasis. Usually, these are spaces or punctuation.

::

        This sentence contains some _emphasized text_.



Escaping to |Latex| and HTML.
+++++++++++++++++++++++++++++++

Pure |Latex| or HTML material can be inserted using the following
escape sequences:


+ ``$...LATEX stuff...$`` inserts some |Latex| material in math mode.
  Simply discarded in HTML output.
+ ``%...LATEX stuff...%`` inserts some |Latex| material. Simply
  discarded in HTML output.
+ ``#...HTML stuff...#`` inserts some HTML material. Simply discarded in
  |Latex| output.

.. note::
  to simply output the characters ``$``, ``%`` and ``#`` and escaping
  their escaping role, these characters must be doubled.


Verbatim
++++++++

Verbatim material is introduced by a leading ``<<`` and closed by ``>>``
at the beginning of a line.

.. example::

  ::

      Here is the corresponding caml code:
      <<
        let rec fact n =
          if n <= 1 then 1 else n * fact (n-1)
      >>



Hyperlinks
++++++++++

Hyperlinks can be inserted into the HTML output, so that any
identifier is linked to the place of its definition.

``coqc file.v`` automatically dumps localization information in
``file.glob`` or appends it to a file specified using the option ``--dump-glob
file``. Take care of erasing this global file, if any, when starting
the whole compilation process.

Then invoke coqdoc or ``coqdoc --glob-from file`` to tell coqdoc to look
for name resolutions in the file ``file`` (it will look in ``file.glob``
by default).

Identifiers from the |Coq| standard library are linked to the Coq website
`<http://coq.inria.fr/library/>`_. This behavior can be changed
using command line options ``--no-externals`` and ``--coqlib``; see below.


Hiding / Showing parts of the source.
+++++++++++++++++++++++++++++++++++++

Some parts of the source can be hidden using command line options ``-g``
and ``-l`` (see below), or using such comments:

::


    (* begin hide *)
     *some Coq material*
    (* end hide *)


Conversely, some parts of the source which would be hidden can be
shown using such comments:

::


    (* begin show *)
     *some Coq material*
    (* end show *)


The latter cannot be used around some inner parts of a proof, but can
be used around a whole proof.


Usage
~~~~~

coqdoc is invoked on a shell command line as follows:
``coqdoc <options and files>``.
Any command line argument which is not an option is considered to be a
file (even if it starts with a ``-``). |Coq| files are identified by the
suffixes ``.v`` and ``.g`` and |Latex| files by the suffix ``.tex``.


:HTML output: This is the default output format. One HTML file is created for
  each |Coq| file given on the command line, together with a file
  ``index.html`` (unless ``option-no-index is passed``). The HTML pages use a
  style sheet named ``style.css``. Such a file is distributed with coqdoc.
:|Latex| output: A single |Latex| file is created, on standard
  output. It can be redirected to a file using the option ``-o``. The order of
  files on the command line is kept in the final document. |Latex|
  files given on the command line are copied ‘as is’ in the final
  document . DVI and PostScript can be produced directly with the
  options ``-dvi`` and ``-ps`` respectively.
:TEXmacs output: To translate the input files to TEXmacs format,
  to be used by the TEXmacs |Coq| interface.



Command line options
++++++++++++++++++++


**Overall options**


  :--HTML: Select a HTML output.
  :--|Latex|: Select a |Latex| output.
  :--dvi: Select a DVI output.
  :--ps: Select a PostScript output.
  :--texmacs: Select a TEXmacs output.
  :--stdout: Write output to stdout.
  :-o file, --output file: Redirect the output into the file ‘file’
    (meaningless with ``-html``).
  :-d dir, --directory dir: Output files into directory ‘dir’ instead of
    the current directory (option ``-d`` does not change the filename specified
    with the option ``-o``, if any).
  :--body-only: Suppress the header and trailer of the final document.
    Thus, you can insert the resulting document into a larger one.
  :-p string, --preamble string: Insert some material in the |Latex|
    preamble, right before ``\begin{document}`` (meaningless with ``-html``).
  :--vernac-file file,--tex-file file: Considers the file ‘file’
    respectively as a ``.v`` (or ``.g``) file or a ``.tex`` file.
  :--files-from file: Read filenames to be processed from the file ‘file’ as if
    they were given on the command line. Useful for program sources split
    up into several directories.
  :-q, --quiet: Be quiet. Do not print anything except errors.
  :-h, --help: Give a short summary of the options and exit.
  :-v, --version: Print the version and exit.



**Index options**

  The default behavior is to build an index, for the HTML output only,
  into ``index.html``.

  :--no-index: Do not output the index.
  :--multi-index: Generate one page for each category and each letter in
    the index, together with a top page ``index.html``.
  :--index string: Make the filename of the index string instead of
    “index”. Useful since “index.html” is special.



**Table of contents option**

  :-toc, --table-of-contents: Insert a table of contents. For a |Latex|
    output, it inserts a ``\tableofcontents`` at the beginning of the
    document. For a HTML output, it builds a table of contents into
    ``toc.html``.
  :--toc-depth int: Only include headers up to depth ``int`` in the table of
    contents.


**Hyperlink options**

  :--glob-from file: Make references using |Coq| globalizations from file
    file. (Such globalizations are obtained with Coq option ``-dump-glob``).
  :--no-externals: Do not insert links to the |Coq| standard library.
  :--external url coqdir: Use given URL for linking references whose
    name starts with prefix ``coqdir``.
  :--coqlib url: Set base URL for the Coq standard library (default is
    `<http://coq.inria.fr/library/>`_). This is equivalent to ``--external url
    Coq``.
  :-R dir coqdir: Map physical directory dir to |Coq| logical
    directory  ``coqdir`` (similarly to |Coq| option ``-R``).

    .. note::

       option ``-R`` only has
       effect on the files *following* it on the command line, so you will
       probably need to put this option first.


**Title options**

  :-s , --short: Do not insert titles for the files. The default
     behavior is to insert a title like “Library Foo” for each file.
  :--lib-name string: Print “string Foo” instead of “Library Foo” in
     titles. For example “Chapter” and “Module” are reasonable choices.
  :--no-lib-name: Print just “Foo” instead of “Library Foo” in titles.
  :--lib-subtitles: Look for library subtitles. When enabled, the
     beginning of each file is checked for a comment of the form:

     ::

        (** * ModuleName : text *)

     where ``ModuleName`` must be the name of the file. If it is present, the
     text is used as a subtitle for the module in appropriate places.
  :-t string, --title string: Set the document title.


**Contents options**

  :-g, --gallina: Do not print proofs.
  :-l, --light: Light mode. Suppress proofs (as with ``-g``) and the following commands:

      + [Recursive] Tactic Definition
      + Hint / Hints
      + Require
      + Transparent / Opaque
      + Implicit Argument / Implicits
      + Section / Variable / Hypothesis / End



    The behavior of options ``-g`` and ``-l`` can be locally overridden using the
    ``(* begin show *) … (* end show *)`` environment (see above).

    There are a few options that control the parsing of comments:

  :--parse-comments: Parse regular comments delimited by ``(*`` and ``*)`` as
    well. They are typeset inline.
  :--plain-comments: Do not interpret comments, simply copy them as
    plain-text.
  :--interpolate: Use the globalization information to typeset
    identifiers appearing in |Coq| escapings inside comments.

**Language options**


  The default behavior is to assume ASCII 7 bit input files.

  :-latin1, --latin1: Select ISO-8859-1 input files. It is equivalent to
    --inputenc latin1 --charset iso-8859-1.
  :-utf8, --utf8: Set --inputenc utf8x for |Latex| output and--charset
    utf-8 for HTML output. Also use Unicode replacements for a couple of
    standard plain ASCII notations such as → for ``->`` and ∀ for ``forall``. |Latex|
    UTF-8 support can be found
    at `<http://www.ctan.org/pkg/unicode>`_. For the interpretation of Unicode
    characters by |Latex|, extra packages which coqdoc does not provide
    by default might be required, such as textgreek for some Greek letters
    or ``stmaryrd`` for some mathematical symbols. If a Unicode character is
    missing an interpretation in the utf8x input encoding, add
    ``\DeclareUnicodeCharacter{code}{LATEX-interpretation}``. Packages
    and declarations can be added with option ``-p``.
  :--inputenc string: Give a |Latex| input encoding, as an option to |Latex|
    package ``inputenc``.
  :--charset string: Specify the HTML character set, to be inserted in
    the HTML header.



The coqdoc |Latex| style file
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In case you choose to produce a document without the default |Latex|
preamble (by using option ``--no-preamble``), then you must insert into
your own preamble the command

::

  \usepackage{coqdoc}

The package optionally takes the argument ``[color]`` to typeset
identifiers with colors (this requires the ``xcolor`` package).

Then you may alter the rendering of the document by redefining some
macros:

:coqdockw, coqdocid, …: The one-argument macros for typesetting
  keywords and identifiers. Defaults are sans-serif for keywords and
  italic for identifiers.For example, if you would like a slanted font
  for keywords, you may insert

  ::

         \renewcommand{\coqdockw}[1]{\textsl{#1}}


  anywhere between ``\usepackage{coqdoc}`` and ``\begin{document}``.


:coqdocmodule:
  One-argument macro for typesetting the title of a ``.v``
  file. Default is

  ::

      \newcommand{\coqdocmodule}[1]{\section*{Module #1}}

  and you may redefine it using ``\renewcommand``.

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
