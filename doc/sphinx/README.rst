=============================
 Documenting Rocq with Sphinx
=============================

Rocq's reference manual is written in `reStructuredText <http://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (“reST”), and compiled with `Sphinx <http://www.sphinx-doc.org/en/master/>`_.
See `this README <../README.md>`_ for compilation instructions.

In addition to standard reST directives (a directive is similar to a LaTeX environment) and roles (a role is similar to a LaTeX command), the ``rocqrst`` plugin loaded by the documentation uses a custom *Rocq domain* — a set of Rocq-specific directives that define *objects* like tactics, commands (vernacs), warnings, etc. —, some custom *directives*, and a few custom *roles*.  Finally, this manual uses a small DSL to describe tactic invocations and commands.

.. role:: rst(code)
   :language: rst

Rocq objects
============

Our Rocq domain define multiple `objects`_.  Each object has a *signature* (think *type signature*), followed by an optional body (a description of that object).  The following example defines two objects: a variant of the ``simpl`` tactic, and an error that it may raise.

.. example::

   .. code-block:: RST

      .. tacv:: simpl @pattern at {+ @natural}
         :name: simpl_at

         This applies ``simpl`` only to the :n:`{+ @natural}` occurrences of the subterms
         matching :n:`@pattern` in the current goal.

         .. exn:: Too few occurrences
            :undocumented:

Objects are automatically collected into indices, and can be linked to using the role version of the object's directive. For example, you could link to the tactic variant above using :rst:`:tacv:`simpl_at``, and to its exception using :rst:`:exn:`Too few occurrences``.

Names (link targets) are auto-generated for most simple objects, though they can always be overwritten using a :rst:`:name:` option, as shown above.

- Options, errors, warnings have their name set to their signature, with ``...`` replacing all notation bits.  For example, the auto-generated name of

  .. code-block:: RST

     .. exn:: @qualid is not a module

  is ``... is not a module``, and a link to it would take the form

  .. code-block:: RST

     :exn:`... is not a module`

- Vernacs (commands) have their name set to the first word of their signature.  For example, the auto-generated name of

  .. code-block:: RST

     Axiom @ident : @term

  is ``Axiom``, and a link to it would take the form

  .. code-block:: RST

     :cmd:`Axiom`

- Vernac variants, tactic notations, and tactic variants do not have a default name.

Most objects should have a body (i.e. a block of indented text following the signature, called “contents” in Sphinx terms).  Undocumented objects should have the :rst:`:undocumented:` flag instead, as shown above.  When multiple objects have a single description, they can be grouped into a single object, like this (semicolons can be used to separate the names of the objects; names starting with ``_`` will be omitted from the indexes):

.. code-block:: RST

   .. cmdv:: Lemma @ident {* @binder } : @type
             Remark @ident {* @binder } : @type
             Fact @ident {* @binder } : @type
             Corollary @ident {* @binder } : @type
             Proposition @ident {* @binder } : @type
      :name: Lemma; Remark; Fact; Corollary; Proposition

      These commands are all synonyms of :n:`Theorem @ident {* @binder } : type`.

Notations
---------

The signatures of most objects can be written using a succinct DSL for Rocq notations (think regular expressions written with a Lispy syntax).  A typical signature might look like ``Hint Extern @natural {? @pattern} => @tactic``, which means that the ``Hint Extern`` command takes a number (``natural``), followed by an optional pattern, and a mandatory tactic.  The language has the following constructs (the full grammar is in `TacticNotations.g </doc/tools/rocqrst/notations/TacticNotations.g>`_):

``@…``
  A placeholder (``@ident``, ``@natural``, ``@tactic``\ …)

``{? …}``
  an optional block

``{* …}``, ``{+ …}``
  an optional (``*``) or mandatory (``+``) block that can be repeated, with repetitions separated by spaces

``{*, …}``, ``{+, …}``
  an optional or mandatory repeatable block, with repetitions separated by commas

``{| … | … | … }``
  an alternative, indicating than one of multiple constructs can be used

``%{``, ``%}``, ``%|``
  an escaped character (rendered without the leading ``%``).  In most cases,
  escaping is not necessary.  In particular, the following expressions are
  all parsed as plain text, and do not need escaping: ``{ xyz }``, ``x |- y``.
  But the following escapes *are* needed: ``{| a b %| c | d }``, ``all: %{``.
  (We use ``%`` instead of the usual ``\`` because you'd have to type ``\``
  twice in your reStructuredText file.)

  For more details and corner cases, see `Advanced uses of notations`_ below.

..
   FIXME document the new subscript support

As an exercise, what do the following patterns mean?

.. code::

   pattern {+, @term {? at {+ @natural}}}
   generalize {+, @term at {+ @natural} as @ident}
   fix @ident @natural with {+ (@ident {+ @binder} {? {struct @ident'}} : @type)}

Objects
-------

Here is the list of all objects of the Rocq domain (The symbol ✒ indicates an object whose signature can be written using the notations DSL):

.. rst:directive:: attr

   ✒ An attribute.

.. example::

   .. code-block:: RST

      .. attr:: local

.. rst:directive:: cmd

   ✒ A Rocq command.

.. example::

   .. code-block:: RST

      .. cmd:: Infix @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @ident }

         This command is equivalent to :n:`…`.

.. rst:directive:: cmdv

   ✒ A variant of a Rocq command.

.. example::

   .. code-block:: RST

      .. cmd:: Axiom @ident : @term.

         This command links :token:`term` to the name :token:`term` as its specification in
         the global environment. The fact asserted by :token:`term` is thus assumed as a
         postulate.

         .. cmdv:: Parameter @ident : @term.

            This is equivalent to :n:`Axiom @ident : @term`.

.. rst:directive:: exn

   ✒ An error raised by a Rocq command or tactic.
   This commonly appears nested in the :rst:dir:`tacn` that raises the exception.

.. example::

   .. code-block:: RST

      .. tacv:: assert @form by @tactic

         This tactic applies :n:`@tactic` to solve the subgoals generated by
         ``assert``.

         .. exn:: Proof is not complete

            Raised if :n:`@tactic` does not fully solve the goal.

.. rst:directive:: flag

   ✒ A Rocq flag (i.e. a boolean setting).

.. example::

   .. code-block:: RST

      .. flag:: Nonrecursive Elimination Schemes

         Controls whether types declared with the keywords
         :cmd:`Variant` and :cmd:`Record` get an automatic declaration of
         induction principles.

.. rst:directive:: opt

   ✒ A Rocq option (a setting with non-boolean value, e.g. a string or numeric value).

.. example::

   .. code-block:: RST

      .. opt:: Hyps Limit @natural
         :name: Hyps Limit

         Controls the maximum number of hypotheses displayed in goals after
         application of a tactic.

.. rst:directive:: prodn

   A grammar production.

   Use :rst:dir:`prodn` to document grammar productions instead of Sphinx
   `production lists
   <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_.

   prodn displays multiple productions together with alignment similar to :rst:dir:`productionlist`,
   however unlike :rst:dir:`productionlist`\ s, this directive accepts notation syntax.

.. example::

   .. code-block:: RST

       .. prodn:: occ_switch ::= { {? {| + | - } } {* @natural } }
          term += let: @pattern := @term in @term
          | second_production

   The first line defines "occ_switch", which must be unique in the document.  The second
   references and expands the definition of "term", whose main definition is elsewhere
   in the document.  The third form is for continuing the
   definition of a nonterminal when it has multiple productions.  It leaves the first
   column in the output blank.

.. rst:directive:: table

   ✒ A Rocq table, i.e. a setting that is a set of values.

.. example::

   .. code-block:: RST

      .. table:: Search Blacklist @string
         :name: Search Blacklist

         Controls ...

.. rst:directive:: tacn

   A tactic, or a tactic notation.

.. example::

   .. code-block:: RST

      .. tacn:: do @natural @expr

         :token:`expr` is evaluated to ``v`` which must be a tactic value. …

.. rst:directive:: tacv

   ✒ A variant of a tactic.

.. example::

   .. code-block:: RST

      .. tacn:: fail

         This is the always-failing tactic: it does not solve any goal. It is
         useful for defining other tacticals since it can be caught by
         :tacn:`try`, :tacn:`repeat`, :tacn:`match goal`, or the branching
         tacticals. …

         .. tacv:: fail @natural

            The number is the failure level. If no level is specified, it
            defaults to 0. …

.. rst:directive:: thm

   A theorem.

.. example::

   .. code-block:: RST

      .. thm:: Bound on the ceiling function

         Let :math:`p` be an integer and :math:`c` a rational constant. Then
         :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.

.. rst:directive:: warn

   ✒ An warning raised by a Rocq command or tactic.

   Do not mistake this for :rst:dir:`warning`; this directive is for warning
   messages produced by Rocq.

.. example::

   .. code-block:: RST

      .. warn:: Ambiguous path

         When the coercion :token:`qualid` is added to the inheritance graph, non
         valid coercion paths are ignored.

Rocq directives
===============

In addition to the objects above, the ``rocqrst`` Sphinx plugin defines the following directives:

.. rst:directive:: rocqtop

   A reST directive to describe interactions with rocq top.

   Usage:

   .. code-block:: RST

      .. rocqtop:: options…

         Rocq code to send to rocq top

.. example::

   .. code-block:: RST

      .. rocqtop:: in reset

         Print nat.
         Definition a := 1.

The blank line after the directive is required.  If you begin a proof,
use the ``abort`` option to reset rocq top for the next example.

Here is a list of permissible options:

- Display options (choose exactly one)

  - ``all``: Display input and output
  - ``in``: Display only input
  - ``out``: Display only output
  - ``none``: Display neither (useful for setup commands)

- Behavior options

  - ``reset``: Send a ``Reset Initial`` command before running this block
  - ``fail``: Don't die if a command fails, implies ``warn`` (so no need to put both)
  - ``warn``: Don't die if a command emits a warning
  - ``restart``: Send a ``Restart`` command before running this block (only works in proof mode)
  - ``abort``: Send an ``Abort All`` command after running this block (leaves all pending proofs if any)
  - ``extra-foo``: if environment variable 'ROCQRST_EXTRA' is set to `all`
    or to a `,`-separated list containing `foo` this is ignored, otherwise behaves as ``fail``
    This is typically used to showcase examples of things outside coq-core or rocq-core.
    `foo` should be the name of the external requirement, e.g. `stdlib` or `mathcomp`.

``rocq top``\ 's state is preserved across consecutive :rst:dir:`rocqtop` blocks
of the same document (``rocqrst`` creates a single ``rocq top`` process per
reST source file).  Use the ``reset`` option to reset Rocq's state.

.. rst:directive:: rocqdoc

   A reST directive to display Rocqtop-formatted source code.

   Usage:

   .. code-block:: RST

      .. rocqdoc::

         Rocq code to highlight

.. example::

   .. code-block:: RST

      .. rocqdoc::

         Definition test := 1.

.. rst:directive:: example

      A reST directive for examples.
      This behaves like a generic admonition; see
      http://docutils.sourceforge.net/docs/ref/rst/directives.html#generic-admonition
      for more details.

      Optionally, any text immediately following the :rst:dir:`example` header is
      used as the example's title.

.. example::

   .. code-block:: RST

      .. example:: Adding a hint to a database

         The following adds ``plus_comm`` to the ``plu`` database:

         .. rocqdoc::

            Hint Resolve plus_comm : plu.

.. rst:directive:: inference

   A reST directive to format inference rules.
   This also serves as a small illustration of the way to create new Sphinx
   directives.

   Usage:

   .. code-block:: RST

      .. inference:: name

         newline-separated premises
         --------------------------
         conclusion

.. example::


   .. code-block:: RST

      .. inference:: Prod-Pro

         \WTEG{T}{s}
         s \in \Sort
         \WTE{\Gamma::(x:T)}{U}{\Prop}
         -----------------------------
         \WTEG{\forall~x:T,U}{\Prop}

.. rst:directive:: preamble

   A reST directive to include a TeX file.
   Mostly useful to let MathJax know about `\def`\s and `\newcommand`\s.  The
   contents of the TeX file are wrapped in a math environment, as MathJax
   doesn't process LaTeX definitions otherwise.

.. example::


   .. code-block:: RST

      .. preamble:: preamble.tex

Rocq roles
==========

In addition to the objects and directives above, the ``rocqrst`` Sphinx plugin defines the following roles:

.. rst:role:: g

   Rocq code.
   Use this for Gallina and Ltac snippets.

.. example::

   .. code-block:: RST

      :g:`apply plus_comm; reflexivity`
      :g:`Set Printing All.`
      :g:`forall (x: t), P(x)`

.. rst:role:: n

   Any text using the notation syntax (``@id``, ``{+, …}``, etc.).
   Use this to explain tactic equivalences.

.. example::

   .. code-block:: RST

      :n:`generalize @term as @ident` is just like :n:`generalize @term`, but
      it names the introduced hypothesis :token:`ident`.

   Note that this example also uses ``:token:``.  That's because ``ident`` is
   defined in the Rocq manual as a grammar production, and ``:token:``
   creates a link to that.  When referring to a placeholder that happens to be
   a grammar production, ``:token:`…``` is typically preferable to ``:n:`@…```.

.. rst:role:: production

   A grammar production not included in a :rst:dir:`prodn` directive.
   Useful to informally introduce a production, as part of running text.

.. example::

   .. code-block:: RST

      :production:`string` indicates a quoted string.

You're not likely to use this role very commonly; instead, use a :rst:dir:`prodn`
directive and reference its tokens using ``:token:`…```.

.. rst:role:: gdef

   Marks the definition of a glossary term inline in the text.  Matching ``:term:`XXX```
   constructs will link to it.  Use the form :rst:`:gdef:`text <term>`` to display "text"
   for the definition of "term", such as when "term" must be capitalized or plural
   for grammatical reasons.  The term will also appear in the Glossary Index.

.. example::

   .. code-block:: RST

      A :gdef:`prime` number is divisible only by itself and 1.
      :gdef:`Composite <composite>` numbers are the non-prime numbers.

Common mistakes
===============

Improper nesting
----------------

DO
  .. code-block:: RST

     .. cmd:: Foo @bar

        Foo the first instance of :token:`bar`\ s.

        .. cmdv:: Foo All

           Foo all the :token:`bar`\ s in
           the current context

DON'T
  .. code-block:: RST

     .. cmd:: Foo @bar

     Foo the first instance of :token:`bar`\ s.

     .. cmdv:: Foo All

     Foo all the :token:`bar`\ s in
     the current context

You can set the ``report_undocumented_coq_objects`` setting in ``conf.py`` to ``"info"`` or ``"warning"`` to get a list of all Rocq objects without a description.

Overusing ``:token:``
---------------------

DO
  .. code-block:: RST

     This is equivalent to :n:`Axiom @ident : @term`.

DON'T
  .. code-block:: RST

     This is equivalent to ``Axiom`` :token:`ident` : :token:`term`.

..

DO
  .. code-block:: RST

     :n:`power_tac @term [@ltac]`
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize …

DON'T
  .. code-block:: RST

     power_tac :n:`@term` [:n:`@ltac`]
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize …

..

DO
  .. code-block:: RST

     :n:`name={*; attr}`

DON'T
  .. code-block:: RST

     ``name=``:n:`{*; attr}`

Omitting annotations
--------------------

DO
  .. code-block:: RST

     .. tacv:: assert @form as @simple_intropattern

DON'T
  .. code-block:: RST

     .. tacv:: assert form as simple_intropattern

Using the :rst:dir:`rocqtop` directive for syntax highlighting
--------------------------------------------------------------

DO
  .. code-block:: RST

     A tactic of the form:

     .. rocqdoc::

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. rocqdoc::

        first [ t1 | … | tn ].

DON'T
  .. code-block:: RST

     A tactic of the form:

     .. rocqtop:: in

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. rocqtop:: in

        first [ t1 | … | tn ].

Overusing plain quotes
----------------------

DO
  .. code-block:: RST

     The :tacn:`refine` tactic can raise the :exn:`Invalid argument` exception.
     The term :g:`let a = 1 in a a` is ill-typed.

DON'T
  .. code-block:: RST

     The ``refine`` tactic can raise the ``Invalid argument`` exception.
     The term ``let a = 1 in a a`` is ill-typed.

Plain quotes produce plain text, without highlighting or cross-references.

Overusing the ``example`` directive
-----------------------------------

DO
  .. code-block:: RST

     Here is a useful axiom:

     .. rocqdoc::

        Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

DO
  .. code-block:: RST

     .. example:: Using proof-irrelevance

        If you assume the axiom above, …

DON'T
  .. code-block:: RST

     Here is a useful axiom:

     .. example::

        .. rocqdoc::

           Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

Tips and tricks
===============

Nested lemmas
-------------

The :rst:dir:`rocqtop` directive does *not* reset Rocq after running its contents.  That is, the following will create two nested lemmas (which by default results in a failure)::

.. code-block:: RST

   .. rocqtop:: all

      Lemma l1: 1 + 1 = 2.

   .. rocqtop:: all

      Lemma l2: 2 + 2 <> 1.

Add either ``abort`` to the first block or ``reset`` to the second block to avoid nesting lemmas.

Abbreviations and macros
------------------------

Substitutions for specially-formatted names (like ``|Cic|``, ``|Ltac|`` and ``|Latex|``), along with some useful LaTeX macros, are defined in a `separate file </doc/sphinx/refman-preamble.rst>`_.  This file is automatically included in all manual pages.

Emacs
-----

The ``dev/tools/coqdev.el`` folder contains a convenient Emacs function to quickly insert Sphinx roles and quotes.  It takes a single character (one of ``gntm:```), and inserts one of ``:g:``, ``:n:``, ``:t:``, or an arbitrary role, or double quotes.  You can also select a region of text, and wrap it in single or double backticks using that function.

Use the following snippet to bind it to `F12` in ``rst-mode``::

   (with-eval-after-load 'rst
     (define-key rst-mode-map (kbd "<f12>") #'coqdev-sphinx-rst-coq-action))


Advanced uses of notations
--------------------------


  - Use `%` to escape grammar literal strings that are the same as metasyntax,
    such as ``{``, ``|``, ``}`` and ``{|``.  (While this is optional for
    ``|`` and ``{ ... }`` outside of ``{| ... }``, always using the escape
    requires less thought.)

  - Literals such as ``|-`` and ``||`` don't need to be escaped.

  - The literal ``%`` shouldn't be escaped.

  - Don't use the escape for a ``|`` separator in ``{*`` and ``{+``.  These
    should appear as ``{*|`` and ``{+|``.
