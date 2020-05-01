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
