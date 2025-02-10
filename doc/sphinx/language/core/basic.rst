=============================
Basic notions and conventions
=============================

This section provides some essential notions and conventions for reading
the manual.

We start by explaining the syntax and lexical conventions used in the
manual.  Then, we present the essential vocabulary necessary to read
the rest of the manual.  Other terms are defined throughout the manual.
The reader may refer to the :ref:`glossary index <glossary_index>`
for a complete list of defined terms.  Finally, we describe the various types of
settings that Rocq provides.

Syntax and lexical conventions
------------------------------

.. _syntax-conventions:

Syntax conventions
~~~~~~~~~~~~~~~~~~

The syntax described in this documentation is equivalent to that
accepted by the Rocq parser, but the grammar has been edited
to improve readability and presentation.

In the grammar presented in this manual, the terminal symbols are
black (e.g. :n:`forall`), whereas the nonterminals are green, italic
and hyperlinked (e.g. :n:`@term`).  Some syntax is represented
graphically using the following kinds of blocks:

:n:`{? item }`
   An optional item.

:n:`{+ item }`
   A list of one or more items.

:n:`{* item }`
   An optional list of items.

:n:`{+s item}`
   A list of one or more items separated by "s" (e.g. :n:`item__1 s item__2 s item__3`).

:n:`{*s item}`
   An optional list of items separated by "s".

:n:`{| item__1 | item__2 | ... }`
   Alternatives (either :n:`item__1` or :n:`item__2` or ...).

`Precedence levels
<https://en.wikipedia.org/wiki/Order_of_operations>`_ that are
implemented in the Rocq parser are shown in the documentation by
appending the level to the nonterminal name (as in :n:`@term100` or
:n:`@ltac_expr3`).

.. note::

   Rocq uses an extensible parser.  Plugins and the :ref:`notation
   system <syntax-extensions-and-notation-scopes>` can extend the
   syntax at run time.  Some notations are defined in the :term:`prelude`,
   which is loaded by default.  The documented grammar doesn't include
   these notations.  Precedence levels not used by the base grammar
   are omitted from the documentation, even though they could still be
   populated by notations or plugins.

   Furthermore, some parsing rules are only activated in certain
   contexts (:ref:`proof mode <proofhandling>`,
   :ref:`custom entries <custom-entries>`...).

.. warning::

   Given the complexity of these parsing rules, it would be extremely
   difficult to create an external program that can properly parse a
   Rocq document.  Therefore, tool writers are advised to delegate
   parsing to Rocq, by communicating with it, for instance through
   `coq-lsp <https://github.com/ejgallego/coq-lsp>`_.

.. seealso:: :cmd:`Print Grammar`

.. _lexical-conventions:

Lexical conventions
~~~~~~~~~~~~~~~~~~~

Blanks
  Space, newline and horizontal tab are considered blanks.
  Blanks are ignored but they separate tokens.

Comments
  Comments are enclosed between ``(*`` and ``*)``.  They can be nested.
  They can contain any character. However, embedded :n:`@string` literals must be
  correctly closed. Comments are treated as blanks.

Identifiers
  Identifiers, written :n:`@ident`, are sequences of letters, digits, ``_`` and
  ``'``, that do not start with a digit or ``'``.  That is, they are
  recognized by the following grammar (except that the string ``_`` is reserved;
  it is not a valid identifier):

  .. insertprodn ident subsequent_letter

  .. prodn::
     ident ::= @first_letter {* @subsequent_letter }
     first_letter ::= {| a .. z | A .. Z | _ | @unicode_letter }
     subsequent_letter ::= {| @first_letter | @digit | ' | @unicode_id_part }

  All characters are meaningful. In particular, identifiers are case-sensitive.
  :production:`unicode_letter` non-exhaustively includes Latin,
  Greek, Gothic, Cyrillic, Arabic, Hebrew, Georgian, Hangul, Hiragana
  and Katakana characters, CJK ideographs, mathematical letter-like
  symbols and non-breaking space. :production:`unicode_id_part`
  non-exhaustively includes symbols for prime letters and subscripts.

Numbers
  Numbers are sequences of digits with an optional fractional part
  and exponent, optionally preceded by a minus sign. Hexadecimal numbers
  start with ``0x`` or ``0X``. :n:`@integer`\s are signed
  numbers without fraction or exponent parts. :n:`@natural`\s are non-negative
  integers.  Underscores embedded in the digits are ignored, for example
  ``1_000_000`` is the same as ``1000000``.

  .. insertprodn number hexdigit

  .. prodn::
     number ::= {? - } @decnat {? . {+ {| @digit | _ } } } {? {| e | E } {? {| + | - } } @decnat }
     | {? - } @hexnat {? . {+ {| @hexdigit | _ } } } {? {| p | P } {? {| + | - } } @decnat }
     integer ::= @bigint
     bigint ::= {? - } @bignat
     natural ::= @bignat
     bignat ::= {| @decnat | @hexnat }
     decnat ::= @digit {* {| @digit | _ } }
     digit ::= 0 .. 9
     hexnat ::= {| 0x | 0X } @hexdigit {* {| @hexdigit | _ } }
     hexdigit ::= {| 0 .. 9 | a .. f | A .. F }

  :n:`number`, :n:`@bigint` and :n:`@bignat`, which are used in :token:`term`\s,
  generally have no range limitation.
  :n:`@integer` and :n:`@natural`, which are used as arguments in tactics
  and commands, are limited to the range that fits
  into an OCaml integer (63-bit integers on most architectures).

  The :ref:`standard library <thecoqlibrary>` provides a few
  :ref:`interpretations <notation-scopes>` for :n:`@number`.
  Some of these interpretations support exponential notation
  for decimal numbers, for example ``5.02e-6`` means 5.02×10\ :sup:`-6`;
  and base 2 exponential notation for hexadecimal numbers denoted by
  ``p`` or ``P``, for example ``0xAp12`` means 10×2\ :sup:`12`.
  The :cmd:`Number Notation` mechanism lets the user
  define custom parsers and printers for :n:`@number`.

  By default, numbers are interpreted as :n:`nat`\s, which is a unary
  representation.  For example, :n:`3` is represented as `S (S (S O))`.  While
  this is a convenient representation for doing proofs, computing with large
  :n:`nat`\s can lead to stack overflows or running out of memory.  You can
  explicitly specify a different interpretation to avoid this problem.  For
  example, the Stdlib library enables to write :n:`1000000%Z` for a more
  efficient binary representation of that number as an integer.
  See :ref:`Scopes` and :n:`@term_scope` for the ``%`` notation.

   .. example:: Stack overflow with :n:`nat`

      .. rocqtop:: all reset

         Fail Eval compute in 100000 + 100000.  (* gives a stack overflow (not shown) *)

      .. rocqtop:: in extra-stdlib

         From Stdlib Require Import ZArith.  (* for definition of Z *)

      .. rocqtop:: all extra-stdlib

         Eval compute in (1000000000000000000000000000000000 + 1)%Z.

Strings
  Strings begin and end with ``"`` (double quote).  Use ``""`` to represent
  a double quote character within a string.  In the grammar, strings are
  identified with :production:`string`.

  The :cmd:`String Notation` mechanism offers the
  user a way to define custom parsers and printers for
  :token:`string`.

.. _keywords:

Keywords
  The following character sequences are keywords defined in the main Rocq grammar
  that cannot be used as identifiers (even when starting Rocq with the `-noinit`
  command-line flag)::

    _ Axiom CoFixpoint Definition Fixpoint Hypothesis Parameter Prop
    SProp Set Theorem Type Variable as at cofix else end
    fix for forall fun if in let match return then where with

  The following are keywords defined in notations or plugins loaded in the :term:`prelude`::

    by exists exists2 using

  Note that loading additional modules or plugins may expand the set of reserved
  keywords.

  :cmd:`Print Keywords` can be used to print the current keywords and tokens.

Other tokens
  The following character sequences are tokens defined in the main Rocq grammar
  (even when starting Rocq with the `-noinit` command-line flag)::

    ! #[ % & ' ( () ) * + , - ->
    . .( .. ... / : ::= := :> ; < <+ <- <:
    <<: <= = => > >-> >= ? @ @{ [ ] _
    `( `{ { {| | }

  The following character sequences are tokens defined in notations or plugins
  loaded in the :term:`prelude`::

    ** |- || ->

  Note that loading additional modules or plugins may expand the set of defined
  tokens.

.. _lexing-unseparated-keywords:

  When multiple tokens match the beginning of a sequence of characters,
  the longest matching token not cutting a subsequence of contiguous letters in the middle is used.
  Occasionally you may need to insert spaces to separate tokens.  For example,
  if ``~`` and ``~~`` are both defined as tokens, the inputs ``~ ~`` and
  ``~~`` generate different tokens, whereas if ``~~`` is not defined, then the
  two inputs are equivalent. Also, if ``~`` and ``~_h`` are both
  defined as tokens, the input ``~_ho`` is interpreted as ``~ _ho``
  rather than ``~_h o`` so as not to cut the identifier-like
  subsequence ``ho``. Contrastingly, if only ``~_h`` is defined as a token,
  then ``~_ho`` is an error because no token can be found that includes
  the whole subsequence ``ho`` without cutting it in the middle. Finally, if
  all of ``~``, ``~_h`` and ``~_ho`` are defined as tokens, the input
  ``~_ho`` is interpreted using the longest match rule, i.e. as the token ``~_ho``.

Essential vocabulary
--------------------

This section presents the most essential notions to understand the
rest of the Rocq Prover manual: :term:`terms <term>` and :term:`types
<type>` on the one hand, :term:`commands <command>` and :term:`tactics
<tactic>` on the other hand.

.. glossary::

   term

     Terms are the basic expressions of Rocq.  Terms can represent
     mathematical expressions, propositions and proofs, but also
     executable programs and program types.

     Here is the top-level syntax of terms.  Each of the listed
     constructs is presented in a dedicated section.  Some of these
     constructs (like :n:`@term_forall_or_fun`) are part of the core
     language that the kernel of Rocq understands and are therefore
     described in :ref:`this chapter <core-language>`, while
     others (like :n:`@term_if`) are language extensions that are
     presented in :ref:`the next chapter <extensions>`.

     .. insertprodn term qualid_annotated

     .. prodn::
        term ::= @term100
        term100 ::= @term_cast
        | @term10
        term10 ::= @term_application
        | @term_forall_or_fun
        | @term_let
        | @term_fix
        | @term_cofix
        | @term_if
        | @one_term
        one_term ::= @term_explicit
        | @term1
        term1 ::= @term_projection
        | @term_scope
        | @term0
        term0 ::= @qualid_annotated
        | @sort
        | @number_or_string
        | @term_evar
        | @term_match
        | @term_record
        | @term_generalizing
        | [| {*; @term } %| @term {? : @type } |] {? @univ_annot }
        | @term_ltac
        | ( @term )
        qualid_annotated ::= @qualid {? @univ_annot }

     .. note::

        Many :term:`commands <command>` and :term:`tactics <tactic>`
        use :n:`@one_term` (in the syntax of their arguments) rather
        than :n:`@term`.  The former need to be enclosed in
        parentheses unless they're very simple, such as a single
        identifier.  This avoids confusing a space-separated list of
        terms or identifiers with a :n:`@term_application`.

   type

     To be valid and accepted by the Rocq kernel, a term needs an
     associated type.  We express this relationship by “:math:`x` *of
     type* :math:`T`”, which we write as “:math:`x:T`”.  Informally,
     “:math:`x:T`” can be thought as “:math:`x` *belongs to*
     :math:`T`”.

     The Rocq kernel is a type checker: it verifies that a term has
     the expected type by applying a set of typing rules (see
     :ref:`Typing-rules`).  If that's indeed the case, we say that the
     term is :gdef:`well-typed`.

     A special feature of the Rocq language is that types can depend
     on terms (we say that the language is `dependently-typed
     <https://en.wikipedia.org/wiki/Dependent_type>`_).  Because of
     this, types and terms share a common syntax.  All types are :term:`terms <term>`,
     but not all terms are types.  The syntactic aliases :n:`@type` and
     :n:`@one_type` are used to make clear when the provided :term:`term`
     must semantically be a type:

     .. insertprodn type one_type

     .. prodn::
        type ::= @term
        one_type ::= @one_term

     Intuitively, types may be viewed as sets containing terms.  We
     say that a type is :gdef:`inhabited` if it contains at least one
     term (i.e. if we can find a term which is associated with this
     type).  We call such terms :gdef:`inhabitants <inhabitant>`.  Note that deciding
     whether a type is inhabited is `undecidable
     <https://en.wikipedia.org/wiki/Undecidable_problem>`_.

     Formally, types can be used to construct logical foundations for
     mathematics alternative to the standard `"set theory"
     <https://en.wikipedia.org/wiki/Set_theory>`_: we call such
     logical foundations `"type theories"
     <https://en.wikipedia.org/wiki/Type_theory>`_.  The Rocq Prover is based on
     the Calculus of Inductive Constructions, which is a particular
     instance of type theory.

   sentence

     Rocq documents are made of a series of sentences that contain
     :term:`commands <command>` or :term:`tactics <tactic>`, generally
     terminated with a period and optionally decorated with
     :term:`attributes <attribute>`.

     .. insertprodn document sentence

     .. prodn::
        document ::= {* @sentence }
        sentence ::= {? @attributes } @command .
        | {? @attributes } {? @natural : } @query_command .
        | {? @attributes } {? @toplevel_selector : } @ltac_expr {| . | ... }
        | @control_command

     :n:`@ltac_expr` syntax supports both simple and compound
     :term:`tactics <tactic>`.  For example: ``split`` is a simple
     tactic while ``split; auto`` combines two simple tactics.

   command

     A :production:`command` can be used to modify the state of a Rocq
     document, for instance by declaring a new object, or to get
     information about the current state.

     By convention, command names begin with uppercase letters.
     Commands appear in the HTML documentation in blue or gray boxes
     after the label "Command".  In the pdf, they appear after the
     boldface label "Command:".  Commands are listed in the
     :ref:`command_index`.  Example:

     .. cmd:: Comments {* {| @one_term | @string | @natural } }

        Prints "Comments ok" and does not change
        the state of the document.

   tactic

     A :production:`tactic` specifies how to transform the current proof state as a
     step in creating a proof.  They are syntactically valid only when
     Rocq is in :term:`proof mode`, such as after a :cmd:`Theorem` command
     and before any subsequent proof-terminating command such as
     :cmd:`Qed`.  See :ref:`proofhandling` for more on proof mode.

     By convention, tactic names begin with lowercase letters.  Tactic
     appear in the HTML documentation in blue or gray boxes after the
     label "Tactic".  In the pdf, they appear after the boldface label
     "Tactic:".  Tactics are listed in the :ref:`tactic_index`.

Settings
--------

There are several mechanisms for changing the behavior of Rocq.  The
:term:`attribute` mechanism is used to modify the default behavior of a
:term:`sentence` or to attach information to Rocq objects.
The :term:`flag`, :term:`option` and :term:`table`
mechanisms are used to modify the behavior of Rocq more globally in a
document or project.

.. _attributes:

Attributes
~~~~~~~~~~

An :gdef:`attribute` is used to modify the default behavior of a
sentence or to attach information to a Rocq object.
Syntactically, most commands and tactics can be decorated with
attributes (cf. :n:`@sentence`), but attributes not supported by the
command or tactic will trigger :warn:`This command does not support
this attribute`. There is also a command :cmd:`Attributes` to
assign attributes to a whole document.

.. insertprodn attributes legacy_attr

.. prodn::
   attributes ::= {* #[ {*, @attribute } ] } {* @legacy_attr }
   attribute ::= @ident {? @attr_value }
   attr_value ::= = @string
   | = @qualid
   | ( {+, @attribute } )
   legacy_attr ::= {| Local | Global }
   | {| Polymorphic | Monomorphic }
   | {| Cumulative | NonCumulative }
   | Private
   | Program

The order of top-level attributes doesn't affect their meaning.  ``#[foo,bar]``, ``#[bar,foo]``,
``#[foo]#[bar]`` and ``#[bar]#[foo]`` are equivalent.

:gdef:`Boolean attributes <boolean attribute>` take the form :n:`@ident__attr{? = {| yes | no } }`.
When the :n:`{| yes | no }` value is omitted, the default is :n:`yes`.

The legacy attributes (:n:`@legacy_attr`) provide an older, alternate syntax
for certain attributes.  They are equivalent to new attributes as follows:

=============================  ================================
Legacy attribute               New attribute
=============================  ================================
`Local`                        :attr:`local`
`Global`                       :attr:`global`
`Polymorphic`, `Monomorphic`   :attr:`universes(polymorphic)`
`Cumulative`, `NonCumulative`  :attr:`universes(cumulative)`
`Private`                      :attr:`private(matching)`
`Program`                      :attr:`program`
=============================  ================================

Attributes appear in the HTML documentation in blue or gray boxes
after the label "Attribute".  In the pdf, they appear after the
boldface label "Attribute:".  Attributes are listed in the
:ref:`attribute_index`.

.. warn:: This command does not support this attribute: @ident.
   :name: This command does not support this attribute

   This warning is configured to behave as an error by default.  You
   may turn it into a normal warning by using the :opt:`Warnings` option:

   .. rocqtop:: none

      Set Silent.

   .. rocqtop:: all warn

      Set Warnings "unsupported-attributes".
      #[ foo ] Comments.

Generic attributes
^^^^^^^^^^^^^^^^^^

The following attribute is supported by every command:

.. attr:: warnings = @string
   :name: warnings

   Sets the given warning string locally for the command. After the
   command finishes the warning state is reset to what it was before
   the command. For instance if the current warning state is
   `some-warnings,-other-warning`,

   .. rocqdoc::

      #[warnings="+other-warning"] Command.

   is equivalent to

   .. rocqdoc::

      Set Warnings "+other-warning".
      Command.
      Set Warnings "some-warnings,-other-warning".

   and `other-warning` is an error while executing the command.

   Consequently, using this attribute around an :cmd:`Import` command
   will prevent it from changing the warning state.

   See also :opt:`Warnings` for the concrete syntax to use inside the
   quoted string.

.. attr:: warning = @string
   :name: warning

   Alias of :attr:`warnings`.

Document-level attributes
^^^^^^^^^^^^^^^^^^^^^^^^^

.. cmd:: Attributes {+, @attribute }
   :name: Attributes

   Associates attributes with the
   document. When compiled with ``rocq compile`` (see Section
   :ref:`therocqcommands`), the attributes are associated with the
   compiled file and may have an effect when the file is loaded with
   :cmd:`Require`. Supported attributes include :attr:`deprecated`
   and :attr:`warn`.

.. _flags-options-tables:

Flags, Options and Tables
~~~~~~~~~~~~~~~~~~~~~~~~~

The following types of settings can be used to change the behavior of Rocq in
subsequent commands and tactics (see :ref:`set_unset_scope_qualifiers` for a
more precise description of the scope of these settings):

* A :gdef:`flag` has a boolean value, such as :flag:`Universe Polymorphism`.
* An :gdef:`option` generally has a numeric or string value, such as :opt:`Firstorder Depth`.
* A :gdef:`table` contains a set of :token:`string`\s or :token:`qualid`\s.
* In addition, some commands provide settings, such as :cmd:`Extraction Language`.

.. FIXME Convert "Extraction Language" to an option.

.. insertprodn setting_name setting_name

.. prodn::
   setting_name ::= {+ @ident }

..

   Flags, options and tables are identified by a series of
   identifiers.  By convention, each of the identifiers start with an
   initial capital letter.

Flags, options and tables appear in the HTML documentation in blue or
gray boxes after the labels "Flag", "Option" and "Table".  In the pdf,
they appear after a boldface label.  They are listed in the
:ref:`options_index`.

.. cmd:: Set @setting_name {? {| @integer | @string } }

   If :n:`@setting_name` is a flag, no value may be provided; the flag
   is set to on.
   If :n:`@setting_name` is an option, a value of the appropriate type
   must be provided; the option is set to the specified value.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   They are described :ref:`here <set_unset_scope_qualifiers>`.

   .. warn:: There is no flag or option with this name: "@setting_name".

      This warning message can be raised by :cmd:`Set` and
      :cmd:`Unset` when :n:`@setting_name` is unknown.  It is a
      warning rather than an error because this helps library authors
      produce Rocq code that is compatible with several Rocq versions.
      To preserve the same behavior, they may need to set some
      compatibility flags or options that did not exist in previous
      Rocq versions.

.. cmd:: Unset @setting_name

   If :n:`@setting_name` is a flag, it is set to off.  If :n:`@setting_name` is an option, it is
   set to its default value.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   They are described :ref:`here <set_unset_scope_qualifiers>`.

.. cmd:: Add @setting_name {+ {| @qualid | @string } }

   Adds the specified values to the table :n:`@setting_name`.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   The default is `export` outside sections and `local` inside sections.
   Depending on the table some values may only allow `local`,
   typically section variables cannot be added with `export` or `global`.

.. cmd:: Remove @setting_name {+ {| @qualid | @string } }

   Removes the specified value from the table :n:`@setting_name`.

   This command supports the same attributes as :cmd:`Add`.

.. cmd:: Test @setting_name {? for {+ {| @qualid | @string } } }

   If :n:`@setting_name` is a flag or option, prints its current value.
   If :n:`@setting_name` is a table: if the `for` clause is specified, reports
   whether the table contains each specified value, otherwise this is equivalent to
   :cmd:`Print Table`.  The `for` clause is not valid for flags and options.

   .. exn:: There is no flag, option or table with this name: "@setting_name".

      This error message is raised when calling the :cmd:`Test`
      command (without the `for` clause), or the :cmd:`Print Table`
      command, for an unknown :n:`@setting_name`.

   .. exn:: There is no qualid-valued table with this name: "@setting_name".
            There is no string-valued table with this name: "@setting_name".

      These error messages are raised when calling the :cmd:`Add` or
      :cmd:`Remove` commands, or the :cmd:`Test` command with the
      `for` clause, if :n:`@setting_name` is unknown or does not have
      the right type.

.. cmd:: Print Options

   Prints the current value of all flags and options, and the names of all tables.

.. cmd:: Print Table @setting_name

   Prints the values in the table :n:`@setting_name`.

.. cmd:: Print Tables

   A synonym for :cmd:`Print Options`.

.. _set_unset_scope_qualifiers:

Locality attributes supported by :cmd:`Set` and :cmd:`Unset`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The :cmd:`Set` and :cmd:`Unset` commands support the mutually
exclusive :attr:`local`, :attr:`export` and :attr:`global` locality
attributes.

* If no attribute is specified, the original value of the flag or option
  is restored at the end of the current module but it is *not* restored
  at the end of the current section.
* The :attr:`local` attribute makes the setting local to the current
  :cmd:`Section` (if applicable) or :cmd:`Module`.
* The :attr:`export` attribute makes the setting local to the current
  :cmd:`Module`, unless :cmd:`Import` (or one of its variants) is used
  on the :cmd:`Module`.
* The :attr:`global` attribute makes the setting persist outside the current
  :cmd:`Module` in the current file, or whenever :cmd:`Require` is used on the
  current file.

.. note::

   We discourage using the :attr:`global` locality attribute with the
   :cmd:`Set` and :cmd:`Unset` commands.  If your goal is to define
   project-wide settings, you should rather use the command-line
   arguments ``-set`` and ``-unset`` for setting flags and options
   (see :ref:`command-line-options`).
