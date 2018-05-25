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

Most objects should have a body (i.e. a block of indented text following the signature, called “contents” in Sphinx terms).  Undocumented objects should have the `:undocumented:` flag instead, as shown above.  When multiple objects have a single description, they can be grouped into a single object, like this (semicolons can be used to separate the names of the objects)::

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

[OBJECTS]

Coq directives
==============

In addition to the objects above, the ``coqrst`` Sphinx plugin defines the following directives:

[DIRECTIVES]

Coq roles
=========

In addition to the objects and directives above, the ``coqrst`` Sphinx plugin defines the following roles:

[ROLES]

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

     This is equivalent to ``Axiom`` :token`ident` : :token:`term`.

Omitting annotations
--------------------

DO
  .. code::

     .. tacv:: assert @form as @intro_pattern

DON'T
  .. code::

     .. tacv:: assert form as intro_pattern

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

Abbreviations and placeholders for specially-formatted names (like ``|Cic|``, ``|Coq|``, ``|CoqIDE|``, ``|Ltac|``, and ``|Gallina|``) are defined in a `separate file </doc/sphinx/replaces.rst>`_ included by most chapters of the manual.  Some useful LaTeX macros are defined in `</doc/sphinx/preamble.rst>`_.

Emacs
-----

The ``dev/tools/coqdev.el`` folder contains a convenient Emacs function to quickly insert Sphinx roles and quotes.  It takes a single character (one of ``gntm:```), and inserts one of ``:g:``, ``:n:``, ``:t:``, or an arbitrary role, or double quotes.  You can also select a region of text, and wrap it in single or double backticks using that function.

Use the following snippet to bind it to :kbd:`F12` in ``rst-mode``::

   (with-eval-after-load 'rst
     (define-key rst-mode-map (kbd "<f12>") #'coqdev-sphinx-rst-coq-action))
