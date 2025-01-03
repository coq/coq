.. index:: coqdoc

.. _rocqdoc:

Documenting Rocq files with rocq doc
------------------------------------

`rocq doc` is a documentation tool for the Rocq Prover, similar to
``javadoc`` or ``ocamldoc``. The task of `rocq doc` is


#. to produce a nice |Latex| and/or HTML document from Rocq source files,
   readable for a human and not only for the proof assistant;
#. to help users navigate their own (or third-party) sources.



Principles
~~~~~~~~~~

Documentation is inserted into Rocq files as *special comments*. Thus
your files will compile as usual, whether you use `rocq doc` or not. `rocq doc`
presupposes that the given Rocq files are well-formed (at least
lexically). Documentation starts with ``(**``, followed by a space, and
ends with ``*)``. The documentation format is inspired by Todd
A. Coram’s *Almost Free Text (AFT)* tool: it is mainly ``ASCII`` text with
some syntax-light controls, described below. `rocq doc` is robust: it
shouldn’t fail, whatever the input is. But remember: “garbage in,
garbage out”.


Rocq material inside documentation.
++++++++++++++++++++++++++++++++++++

Rocq material is quoted between the delimiters ``[`` and ``]``. Square brackets
may be nested, the inner ones being understood as being part of the
quoted code (thus you can quote a term like ``let id := fun [T : Type] (x : t) => x in id 0``
by writing  ``[let id := fun [T : Type] (x : t) => x in id 0]``).
Inside quotations, the code is pretty-printed the same way as in code parts.

Preformatted vernacular is enclosed by ``[[`` and ``]]``. The former must be
followed by a newline and the latter must follow a newline.


Pretty-printing.
++++++++++++++++

`rocq doc` uses different faces for identifiers and keywords. The pretty-
printing of Rocq tokens (identifiers or symbols) can be controlled
using one of the following commands:

::


    (** printing  *token* %...LATEX...% #...html...# *)


or

::


    (** printing  *token* $...LATEX math...$ #...html...# *)


It gives the |Latex| and HTML texts to be produced for the given Rocq
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
   is recognized as a single token, where Rocq sees two tokens. It is the
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

List items are introduced by a leading dash. `rocq doc` uses whitespace to
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

Verbatim material on a single line is also possible (assuming that
``>>`` is not part of the text to be presented as verbatim).

.. example::

  ::

      Here is the corresponding caml expression: << fact (n-1) >>


Hyperlinks
++++++++++

Hyperlinks can be inserted into the HTML output, so that any
identifier is linked to the place of its definition.

``rocq c file.v`` automatically dumps localization information in
``file.glob`` or appends it to a file specified using the option ``--dump-glob
file``. Take care of erasing this global file, if any, when starting
the whole compilation process.

Then invoke `rocq doc` or ``rocq doc --glob-from file`` to tell `rocq doc` to look
for name resolutions in the file ``file`` (it will look in ``file.glob``
by default).

Identifiers from the Rocq standard library are linked to the Coq website
`<http://coq.inria.fr/library/>`_. This behavior can be changed
using command line options ``--no-externals`` and ``--coqlib_url``; see below.


.. _rocqdoc-hide-show:

Hiding / Showing parts of the source
++++++++++++++++++++++++++++++++++++

Some parts of the source can be hidden using command line options ``-g``
and ``-l`` (see below), or using such comments:

::


    (* begin hide *)
     *some Rocq material*
    (* end hide *)


Conversely, some parts of the source which would be hidden can be
shown using such comments:

::


    (* begin show *)
     *some Rocq material*
    (* end show *)


The latter cannot be used around some inner parts of a proof, but can
be used around a whole proof.

Lastly, it is possible to adopt a middle-ground approach when the
desired output is HTML, where a given snippet of Rocq material is
hidden by default, but can be made visible with user interaction.

::


    (* begin details *)
     *some Rocq material*
    (* end details *)


There is also an alternative syntax available.

::


    (* begin details : Some summary describing the snippet *)
     *some Rocq material*
    (* end details *)


Usage
~~~~~

`rocq doc` is invoked on a shell command line as follows:
``rocq doc <options and files>``.
Any command line argument which is not an option is considered to be a
file (even if it starts with a ``-``). Rocq files are identified by the
suffixes ``.v`` and ``.g`` and |Latex| files by the suffix ``.tex``.


:HTML output: This is the default output format. One HTML file is created for
  each Rocq file given on the command line, together with a file
  ``index.html`` (unless ``option-no-index is passed``). The HTML pages use a
  style sheet named ``style.css``. Such a file is distributed with `rocq doc`.
:|Latex| output: A single |Latex| file is created, on standard
  output. It can be redirected to a file using the option ``-o``. The order of
  files on the command line is kept in the final document. |Latex|
  files given on the command line are copied ‘as is’ in the final
  document . DVI and PostScript can be produced directly with the
  options ``-dvi`` and ``-ps`` respectively.
:TEXmacs output: To translate the input files to TEXmacs format,
  to be used by the TEXmacs Rocq interface.



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
  :--binder-index: Include variable binders in the index. Not recommended
    with large source files, where binder information may dominate the index.
  :--multi-index: Generate one page for each category and each letter in
    the index, together with a top page ``index.html``.
  :--index string: Make the filename of the index "``string``.html" instead of
    “index.html”. Useful since “index.html” is special.



**Table of contents option**

  :-toc, --table-of-contents: Insert a table of contents. For a |Latex|
    output, it inserts a ``\tableofcontents`` at the beginning of the
    document. For a HTML output, it builds a table of contents into
    ``toc.html``.
  :--toc-depth int: Only include headers up to depth ``int`` in the table of
    contents.


**Hyperlink options**

  :--glob-from file: Make references using Rocq globalizations from file
    file. (Such globalizations are obtained with Rocq option ``-dump-glob``).
  :--no-externals: Do not insert links to the Rocq standard library.
  :--external url coqdir: Use given URL for linking references whose
    name starts with prefix ``coqdir``.
  :--coqlib_url url: Set base URL for the Rocq standard library (default is
    `<http://coq.inria.fr/library/>`_). This is equivalent to ``--external url
    Stdlib``.
  :-R dir coqdir: Recursively map physical directory dir to Rocq logical
    directory  ``coqdir`` (similarly to Rocq option ``-R``).
  :-Q dir coqdir: Map physical directory dir to Rocq logical
    directory  ``coqdir`` (similarly to Rocq option ``-Q``).

    .. note::

       options ``-R`` and ``-Q`` only have
       effect on the files *following* them on the command line, so you will
       probably need to put this option first.


**Title options**

  :-s , --short: Do not insert titles for the files. The default
     behavior is to insert a title like “Library Foo” for each file.
  :--lib-name string: Print “string Foo” instead of “Library Foo” in
     titles. For example “Chapter” and “Module” are reasonable choices.
  :--no-lib-name: Print just “Foo” instead of “Library Foo” in titles.
  :--lib-subtitles: Look for library subtitles. When enabled, the
     first line of each file is checked for a comment of the form:

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
    identifiers appearing in Rocq escapings inside comments.

**Language options**


  The default behavior is to assume ASCII 7 bit input files.

  :-latin1, --latin1: Select ISO-8859-1 input files. It is equivalent to
    --inputenc latin1 --charset iso-8859-1.
  :-utf8, --utf8: Set --inputenc utf8x for |Latex| output and--charset
    utf-8 for HTML output. Also use Unicode replacements for a couple of
    standard plain ASCII notations such as → for ``->`` and ∀ for ``forall``. |Latex|
    UTF-8 support can be found
    at `<http://www.ctan.org/pkg/unicode>`_. For the interpretation of Unicode
    characters by |Latex|, extra packages which `rocq doc` does not provide
    by default might be required, such as textgreek for some Greek letters
    or ``stmaryrd`` for some mathematical symbols. If a Unicode character is
    missing an interpretation in the utf8x input encoding, add
    ``\DeclareUnicodeCharacter{code}{LATEX-interpretation}``. Packages
    and declarations can be added with option ``-p``.
  :--inputenc string: Give a |Latex| input encoding, as an option to |Latex|
    package ``inputenc``.
  :--charset string: Specify the HTML character set, to be inserted in
    the HTML header.



The rocq doc |Latex| style file
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
