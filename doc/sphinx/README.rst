=============================
 Documenting Coq with Sphinx
=============================

..
   README.rst is auto-generated from README.template.rst and the coqrst docs;
   use ``doc/tools/coqrst/regen_readme.py`` to rebuild it.

Coq's reference manual is written in `reStructuredText <http://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (“reST”), and compiled with `Sphinx <http://www.sphinx-doc.org/en/master/>`_.

In addition to standard reST directives (a directive is similar to a LaTeX environment) and roles (a role is similar to a LaTeX command), the ``coqrst`` plugin loaded by the documentation uses a custom *Coq domain* — a set of Coq-specific directives that define *objects* like tactics, commands (vernacs), warnings, etc. —, some custom *directives*, and a few custom *roles*.  Finally, this manual uses a small DSL to describe tactic invocations and commands.

Coq objects
===========

Our Coq domain define multiple `objects`_.  Each object has a *signature* (think *type signature*), followed by an optional body (a description of that object).  The following example defines two objects: a variant of the ``simpl`` tactic, and an error that it may raise::

   .. tacv:: simpl @pattern at {+ @num}
      :name: simpl_at

      This applies ``simpl`` only to the :n:`{+ @num}` occurrences of the subterms
      matching :n:`@pattern` in the current goal.

      .. exn:: Too few occurrences
         :undocumented:

Objects are automatically collected into indices, and can be linked to using the role version of the object's directive. For example, you could link to the tactic variant above using ``:tacv:`simpl_at```, and to its exception using ``:exn:`Too few occurrences```.

Names (link targets) are auto-generated for most simple objects, though they can always be overwritten using a ``:name:`` option, as shown above.

- Options, errors, warnings have their name set to their signature, with ``...`` replacing all notation bits.  For example, the auto-generated name of ``.. exn:: @qualid is not a module`` is ``... is not a module``, and a link to it would take the form ``:exn:`... is not a module```.
- Vernacs (commands) have their name set to the first word of their signature.  For example, the auto-generated name of ``Axiom @ident : @term`` is ``Axiom``, and a link to it would take the form ``:cmd:`Axiom```.
- Vernac variants, tactic notations, and tactic variants do not have a default name.

Most objects should have a body (i.e. a block of indented text following the signature, called “contents” in Sphinx terms).  Undocumented objects should have the ``:undocumented:`` flag instead, as shown above.  When multiple objects have a single description, they can be grouped into a single object, like this (semicolons can be used to separate the names of the objects; names starting with ``_`` will be omitted from the indexes)::

   .. cmdv:: Lemma @ident {? @binders} : @type
             Remark @ident {? @binders} : @type
             Fact @ident {? @binders} : @type
             Corollary @ident {? @binders} : @type
             Proposition @ident {? @binders} : @type
      :name: Lemma; Remark; Fact; Corollary; Proposition

      These commands are all synonyms of :n:`Theorem @ident {? @binders } : type`.

Notations
---------

The signatures of most objects can be written using a succinct DSL for Coq notations (think regular expressions written with a Lispy syntax).  A typical signature might look like ``Hint Extern @num {? @pattern} => @tactic``, which means that the ``Hint Extern`` command takes a number (``num``), followed by an optional pattern, and a mandatory tactic.  The language has the following constructs (the full grammar is in `TacticNotations.g </doc/tools/coqrst/notations/TacticNotations.g>`_):

``@…``
  A placeholder (``@ident``, ``@num``, ``@tactic``\ …)

``{? …}``
  an optional block

``{* …}``, ``{+ …}``
  an optional (``*``) or mandatory (``+``) block that can be repeated, with repetitions separated by spaces

``{*, …}``, ``{+, …}``
  an optional or mandatory repeatable block, with repetitions separated by commas

``%|``, ``%{``, …
  an escaped character (rendered without the leading ``%``)

..
   FIXME document the new subscript support

As an exercise, what do the following patterns mean?

.. code::

   pattern {+, @term {? at {+ @num}}}
   generalize {+, @term at {+ @num} as @ident}
   fix @ident @num with {+ (@ident {+ @binder} {? {struct @ident'}} : @type)}

Objects
-------

Here is the list of all objects of the Coq domain (The symbol :black_nib: indicates an object whose signature can be written using the notations DSL):

``.. cmd::`` :black_nib: A Coq command.
    Example::

       .. cmd:: Infix "@symbol" := @term ({+, @modifier}).

          This command is equivalent to :n:`…`.

``.. cmdv::`` :black_nib: A variant of a Coq command.
    Example::

       .. cmd:: Axiom @ident : @term.

          This command links :token:`term` to the name :token:`term` as its specification in
          the global context. The fact asserted by :token:`term` is thus assumed as a
          postulate.

          .. cmdv:: Parameter @ident : @term.

             This is equivalent to :n:`Axiom @ident : @term`.

``.. exn::`` :black_nib: An error raised by a Coq command or tactic.
    This commonly appears nested in the ``.. tacn::`` that raises the
    exception.

    Example::

       .. tacv:: assert @form by @tactic

          This tactic applies :n:`@tactic` to solve the subgoals generated by
          ``assert``.

          .. exn:: Proof is not complete

             Raised if :n:`@tactic` does not fully solve the goal.

``.. flag::`` :black_nib: A Coq flag (i.e. a boolean setting).
    Example::

       .. flag:: Nonrecursive Elimination Schemes

          Controls whether types declared with the keywords
          :cmd:`Variant` and :cmd:`Record` get an automatic declaration of
          induction principles.

``.. opt::`` :black_nib: A Coq option (a setting with non-boolean value, e.g. a string or numeric value).
    Example::

       .. opt:: Hyps Limit @num
          :name Hyps Limit

          Controls the maximum number of hypotheses displayed in goals after
          application of a tactic.

``.. prodn::`` A grammar production.
    This is useful if you intend to document individual grammar productions.
    Otherwise, use Sphinx's `production lists
    <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_.

    Unlike ``.. productionlist``\ s, this directive accepts notation syntax.


    Usage::

       .. prodn:: token += production
       .. prodn:: token ::= production

    Example::

        .. prodn:: term += let: @pattern := @term in @term
        .. prodn:: occ_switch ::= { {? + %| - } {* @num } }

``.. table::`` :black_nib: A Coq table, i.e. a setting that is a set of values.
    Example::

       .. table:: Search Blacklist @string
          :name: Search Blacklist

          Controls ...

``.. tacn::`` :black_nib: A tactic, or a tactic notation.
    Example::

       .. tacn:: do @num @expr

          :token:`expr` is evaluated to ``v`` which must be a tactic value. …

``.. tacv::`` :black_nib: A variant of a tactic.
    Example::

       .. tacn:: fail

          This is the always-failing tactic: it does not solve any goal. It is
          useful for defining other tacticals since it can be caught by
          :tacn:`try`, :tacn:`repeat`, :tacn:`match goal`, or the branching
          tacticals. …

          .. tacv:: fail @natural

             The number is the failure level. If no level is specified, it
             defaults to 0. …

``.. thm::`` A theorem.
    Example::

       .. thm:: Bound on the ceiling function

          Let :math:`p` be an integer and :math:`c` a rational constant. Then
          :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.

``.. warn::`` :black_nib: An warning raised by a Coq command or tactic..
    Do not mistake this for ``.. warning::``; this directive is for warning
    messages produced by Coq.


    Example::

       .. warn:: Ambiguous path

          When the coercion :token:`qualid` is added to the inheritance graph, non
          valid coercion paths are ignored.

Coq directives
==============

In addition to the objects above, the ``coqrst`` Sphinx plugin defines the following directives:

``.. coqtop::`` A reST directive to describe interactions with Coqtop.
    Usage::

       .. coqtop:: options…

          Coq code to send to coqtop

    Example::

       .. coqtop:: in reset undo

          Print nat.
          Definition a := 1.

    The blank line after the directive is required.  If you begin a proof,
    include an ``Abort`` afterwards to reset coqtop for the next example.

    Here is a list of permissible options:

    - Display options

      - ``all``: Display input and output
      - ``in``: Display only input
      - ``out``: Display only output
      - ``none``: Display neither (useful for setup commands)

    - Behavior options

      - ``reset``: Send a ``Reset Initial`` command before running this block
      - ``undo``: Send an ``Undo n`` (``n`` = number of sentences) command after
        running all the commands in this block

    ``coqtop``\ 's state is preserved across consecutive ``.. coqtop::`` blocks
    of the same document (``coqrst`` creates a single ``coqtop`` process per
    reST source file).  Use the ``reset`` option to reset Coq's state.

``.. coqdoc::`` A reST directive to display Coqtop-formatted source code.
    Usage::

       .. coqdoc::

          Coq code to highlight

    Example::

       .. coqdoc::

          Definition test := 1.

``.. example::`` A reST directive for examples.
    This behaves like a generic admonition; see
    http://docutils.sourceforge.net/docs/ref/rst/directives.html#generic-admonition
    for more details.

    Optionally, any text immediately following the ``.. example::`` header is
    used as the example's title.

    Example::

       .. example:: Adding a hint to a database

          The following adds ``plus_comm`` to the ``plu`` database:

          .. coqdoc::

             Hint Resolve plus_comm : plu.

``.. inference::`` A reST directive to format inference rules.
    This also serves as a small illustration of the way to create new Sphinx
    directives.

    Usage::

       .. inference:: name

          newline-separated premises
          --------------------------
          conclusion

    Example::

       .. inference:: Prod-Pro

          \WTEG{T}{s}
          s \in \Sort
          \WTE{\Gamma::(x:T)}{U}{\Prop}
          -----------------------------
          \WTEG{\forall~x:T,U}{\Prop}

``.. preamble::`` A reST directive to include a TeX file.
    Mostly useful to let MathJax know about `\def`s and `\newcommand`s.  The
    contents of the TeX file are wrapped in a math environment, as MathJax
    doesn't process LaTeX definitions otherwise.

    Usage::

       .. preamble:: preamble.tex

Coq roles
=========

In addition to the objects and directives above, the ``coqrst`` Sphinx plugin defines the following roles:

``:g:`` Coq code.
    Use this for Gallina and Ltac snippets::

       :g:`apply plus_comm; reflexivity`
       :g:`Set Printing All.`
       :g:`forall (x: t), P(x)`

``:n:`` Any text using the notation syntax (``@id``, ``{+, …}``, etc.).
    Use this to explain tactic equivalences.  For example, you might write
    this::

       :n:`generalize @term as @ident` is just like :n:`generalize @term`, but
       it names the introduced hypothesis :token:`ident`.

    Note that this example also uses ``:token:``.  That's because ``ident`` is
    defined in the Coq manual as a grammar production, and ``:token:``
    creates a link to that.  When referring to a placeholder that happens to be
    a grammar production, ``:token:`…``` is typically preferable to ``:n:`@…```.

``:production:`` A grammar production not included in a ``productionlist`` directive.
    Useful to informally introduce a production, as part of running text.

    Example::

       :production:`string` indicates a quoted string.

    You're not likely to use this role very commonly; instead, use a
    `production list
    <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_
    and reference its tokens using ``:token:`…```.

Common mistakes
===============

Improper nesting
----------------

DO
  .. code::

     .. cmd:: Foo @bar

        Foo the first instance of :token:`bar`\ s.

        .. cmdv:: Foo All

           Foo all the :token:`bar`\ s in
           the current context

DON'T
  .. code::

     .. cmd:: Foo @bar

     Foo the first instance of :token:`bar`\ s.

     .. cmdv:: Foo All

     Foo all the :token:`bar`\ s in
     the current context

You can set the ``report_undocumented_coq_objects`` setting in ``conf.py`` to ``"info"`` or ``"warning"`` to get a list of all Coq objects without a description.

Overusing ``:token:``
---------------------

DO
  .. code::

     This is equivalent to :n:`Axiom @ident : @term`.

DON'T
  .. code::

     This is equivalent to ``Axiom`` :token:`ident` : :token:`term`.

..

DO
  .. code::

     :n:`power_tac @term [@ltac]`
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize …

DON'T
  .. code::

     power_tac :n:`@term` [:n:`@ltac`]
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize …

..

DO
  .. code::

     :n:`name={*; attr}`

DON'T
  .. code::

     ``name=``:n:`{*; attr}`

Omitting annotations
--------------------

DO
  .. code::

     .. tacv:: assert @form as @intro_pattern

DON'T
  .. code::

     .. tacv:: assert form as intro_pattern

Using the ``.. coqtop::`` directive for syntax highlighting
-----------------------------------------------------------

DO
  .. code::

     A tactic of the form:

     .. coqdoc::

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. coqdoc::

        first [ t1 | … | tn ].

DON'T
  .. code::

     A tactic of the form:

     .. coqtop:: in

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. coqtop:: in

        first [ t1 | … | tn ].

Overusing plain quotes
----------------------

DO
  .. code::

     The :tacn:`refine` tactic can raise the :exn:`Invalid argument` exception.
     The term :g:`let a = 1 in a a` is ill-typed.

DON'T
  .. code::

     The ``refine`` tactic can raise the ``Invalid argument`` exception.
     The term ``let a = 1 in a a`` is ill-typed.

Plain quotes produce plain text, without highlighting or cross-references.

Overusing the ``example`` directive
-----------------------------------

DO
  .. code::

     Here is a useful axiom:

     .. coqdoc::

        Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

DO
  .. code::

     .. example:: Using proof-irrelevance

        If you assume the axiom above, …

DON'T
  .. code::

     Here is a useful axiom:

     .. example::

        .. coqdoc::

           Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

Tips and tricks
===============

Nested lemmas
-------------

The ``.. coqtop::`` directive does *not* reset Coq after running its contents.  That is, the following will create two nested lemmas::

   .. coqtop:: all

      Lemma l1: 1 + 1 = 2.

   .. coqtop:: all

      Lemma l2: 2 + 2 <> 1.

Add either ``undo`` to the first block or ``reset`` to the second block to avoid nesting lemmas.

Abbreviations and macros
------------------------

Substitutions for specially-formatted names (like ``|Cic|``, ``|Coq|``, ``|CoqIDE|``, ``|Ltac|``, and ``|Gallina|``), along with some useful LaTeX macros, are defined in a `separate file </doc/sphinx/refman-preamble.rst>`_.  This file is automatically included in all manual pages.

Emacs
-----

The ``dev/tools/coqdev.el`` folder contains a convenient Emacs function to quickly insert Sphinx roles and quotes.  It takes a single character (one of ``gntm:```), and inserts one of ``:g:``, ``:n:``, ``:t:``, or an arbitrary role, or double quotes.  You can also select a region of text, and wrap it in single or double backticks using that function.

Use the following snippet to bind it to :kbd:`F12` in ``rst-mode``::

   (with-eval-after-load 'rst
     (define-key rst-mode-map (kbd "<f12>") #'coqdev-sphinx-rst-coq-action))
