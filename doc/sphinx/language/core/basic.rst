.. _lexical-conventions:

Lexical conventions
===================

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

Numerals
  Numerals are sequences of digits with an optional fractional part
  and exponent, optionally preceded by a minus sign. :n:`@int` is an integer;
  a numeral without fractional or exponent parts. :n:`@num` is a non-negative
  integer.  Underscores embedded in the digits are ignored, for example
  ``1_000_000`` is the same as ``1000000``.

  .. insertprodn numeral digit

  .. prodn::
     numeral ::= {+ @digit } {? . {+ @digit } } {? {| e | E } {? {| + | - } } {+ @digit } }
     int ::= {? - } {+ @digit }
     num ::= {+ @digit }
     digit ::= 0 .. 9

Strings
  Strings begin and end with ``"`` (double quote).  Use ``""`` to represent
  a double quote character within a string.  In the grammar, strings are
  identified with :production:`string`.

Keywords
  The following character sequences are reserved keywords that cannot be
  used as identifiers::

    _ Axiom CoFixpoint Definition Fixpoint Hypothesis IF Parameter Prop
    SProp Set Theorem Type Variable as at by cofix discriminated else
    end exists exists2 fix for forall fun if in lazymatch let match
    multimatch return then using where with

  Note that plugins may define additional keywords when they are loaded.

Other tokens
  The set of
  tokens defined at any given time can vary because the :cmd:`Notation`
  command can define new tokens.  A :cmd:`Require` command may load more notation definitions,
  while the end of a :cmd:`Section` may remove notations.  Some notations
  are defined in the basic library (see :ref:`thecoqlibrary`) and are normally
  loaded automatically at startup time.

  Here are the character sequences that Coq directly defines as tokens
  without using :cmd:`Notation` (omitting 25 specialized tokens that begin with
  ``#int63_``)::

    ! #[ % & ' ( () (bfs) (dfs) ) * ** + , - ->
    . .( .. ... / : ::= := :> :>> ; < <+ <- <:
    <<: <= = => > >-> >= ? @ @{ [ [= ] _
    `( `{ { {| | |- || }

  When multiple tokens match the beginning of a sequence of characters,
  the longest matching token is used.
  Occasionally you may need to insert spaces to separate tokens.  For example,
  if ``~`` and ``~~`` are both defined as tokens, the inputs ``~ ~`` and
  ``~~`` generate different tokens, whereas if `~~` is not defined, then the
  two inputs are equivalent.

.. _gallina-attributes:

Attributes
-----------

.. insertprodn all_attrs legacy_attr

.. prodn::
   all_attrs ::= {* #[ {*, @attr } ] } {* @legacy_attr }
   attr ::= @ident {? @attr_value }
   attr_value ::= = @string
   | ( {*, @attr } )
   legacy_attr ::= {| Local | Global }
   | {| Polymorphic | Monomorphic }
   | {| Cumulative | NonCumulative }
   | Private
   | Program

Attributes modify the behavior of a command or tactic.
Syntactically, most commands and tactics can be decorated with attributes, but
attributes not supported by the command or tactic will be flagged as errors.

The order of top-level attributes doesn't affect their meaning.  ``#[foo,bar]``, ``#[bar,foo]``,
``#[foo]#[bar]`` and ``#[bar]#[foo]`` are equivalent.

The legacy attributes (:n:`@legacy_attr`) provide an older, alternate syntax
for certain attributes.  They are equivalent to new attributes as follows:

================  ================================
Legacy attribute  New attribute
================  ================================
`Local`           :attr:`local`
`Global`          :attr:`global`
`Polymorphic`     :attr:`universes(polymorphic)`
`Monomorphic`     :attr:`universes(monomorphic)`
`Cumulative`      :attr:`universes(cumulative)`
`NonCumulative`   :attr:`universes(noncumulative)`
`Private`         :attr:`private(matching)`
`Program`         :attr:`program`
================  ================================

.. warn:: Unsupported attribute

   This warning is an error by default. It is caused by using a
   command with some attribute it does not understand.

.. _flags-options-tables:

Flags, Options and Tables
-----------------------------

Coq has many settings to control its behavior.  Setting types include flags, options
and tables:

* A *flag* has a boolean value, such as :flag:`Asymmetric Patterns`.
* An *option* generally has a numeric or string value, such as :opt:`Firstorder Depth`.
* A *table* contains a set of strings or qualids.
* In addition, some commands provide settings, such as :cmd:`Extraction Language`.

.. FIXME Convert "Extraction Language" to an option.

Flags, options and tables are identified by a series of identifiers, each with an initial
capital letter.

.. cmd:: Set @setting_name {? {| @int | @string } }
   :name: Set

   .. insertprodn setting_name setting_name

   .. prodn::
      setting_name ::= {+ @ident }

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
      produce Coq code that is compatible with several Coq versions.
      To preserve the same behavior, they may need to set some
      compatibility flags or options that did not exist in previous
      Coq versions.

.. cmd:: Unset @setting_name
   :name: Unset

   If :n:`@setting_name` is a flag, it is set to off.  If :n:`@setting_name` is an option, it is
   set to its default value.

   This command supports the :attr:`local`, :attr:`global` and :attr:`export` attributes.
   They are described :ref:`here <set_unset_scope_qualifiers>`.

.. cmd:: Add @setting_name {+ {| @qualid | @string } }

   Adds the specified values to the table :n:`@setting_name`.

.. cmd:: Remove @setting_name {+ {| @qualid | @string } }

   Removes the specified value from the table :n:`@setting_name`.

.. cmd:: Test @setting_name {? for {+ {| @qualid | @string } } }

   If :n:`@setting_name` is a flag or option, prints its current value.
   If :n:`@setting_name` is a table: if the `for` clause is specified, reports
   whether the table contains each specified value, otherise this is equivalent to
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
````````````````````````````````````````````````````````````

The :cmd:`Set` and :cmd:`Unset` commands support the :attr:`local`,
:attr:`global` and :attr:`export` locality attributes:

* no attribute: the original setting is *not* restored at the end of
  the current module or section.
* :attr:`local` (an alternative syntax is to use the ``Local``
  prefix): the setting is applied within the current module or
  section.  The original value of the setting is restored at the end
  of the current module or section.
* :attr:`export` (an alternative syntax is to use the ``Export``
  prefix): similar to :attr:`local`, the original value of the setting
  is restored at the end of the current module or section.  In
  addition, if the value is set in a module, then :cmd:`Import`\-ing
  the module sets the option or flag.
* :attr:`global` (an alternative syntax is to use the ``Global``
  prefix): the original setting is *not* restored at the end of the
  current module or section.  In addition, if the value is set in a
  file, then :cmd:`Require`\-ing the file sets the option.

Newly opened modules and sections inherit the current settings.

.. note::

   The use of the :attr:`global` attribute with the :cmd:`Set` and
   :cmd:`Unset` commands is discouraged.  If your goal is to define
   project-wide settings, you should rather use the command-line
   arguments ``-set`` and ``-unset`` for setting flags and options
   (cf. :ref:`command-line-options`).
