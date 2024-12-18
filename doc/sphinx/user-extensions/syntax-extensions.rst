.. _syntax-extensions-and-notation-scopes:

Syntax extensions and notation scopes
=====================================

In this chapter, we introduce advanced commands to modify the way Rocq
parses and prints objects, i.e. the translations between the concrete
and internal representations of terms and commands.

The main commands to provide custom symbolic notations for terms are
:cmd:`Notation` and :cmd:`Infix`; they will be described in the
:ref:`next section <Notations>`. There is also a
variant of :cmd:`Notation` which does not modify the parser; this provides a
form of :ref:`abbreviation <Abbreviations>`. It is
sometimes expected that the same symbolic notation has different meanings in
different contexts; to achieve this form of overloading, Rocq offers a notion
of :ref:`notation scopes <Scopes>`.
The main command to provide custom notations for tactics is :cmd:`Tactic Notation`.

.. rocqtop:: none

   Set Printing Depth 50.

.. _Notations:

Notations
---------

.. _BasicNotations:

Basic notations
~~~~~~~~~~~~~~~

.. cmd:: Notation @notation_declaration

   .. insertprodn notation_declaration notation_declaration

   .. prodn::
      notation_declaration ::= @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @scope_name }

   Defines a *notation*, an alternate syntax for entering or displaying
   a specific term or term pattern.

   This command supports the :attr:`local` attribute, which limits its effect to the
   current module.
   If the command is inside a section, its effect is limited to the section.

   Specifying :token:`scope_name` associates the notation with that scope.  Otherwise
   it is a :gdef:`lonely notation`, that is, not associated with a scope.

   .. todo indentation of this chapter is not consistent with other chapters.  Do we have a standard?

For example, the following definition permits using the infix expression :g:`A /\ B`
to represent :g:`(and A B)`:

.. rocqtop:: in

   Notation "A /\ B" := (and A B).

:g:`"A /\ B"` is a *notation*, which tells how to represent the abbreviated term
:g:`(and A B)`.

Notations must be in double quotes, except when the
abbreviation has the form of an ordinary applicative expression;
see :ref:`Abbreviations`. The notation consists of *tokens* separated by
spaces. Tokens which are identifiers (such as ``A``, ``x0'``, etc.) are the *parameters*
of the notation. Each of them must occur at least once in the abbreviated term. The
other elements of the string (such as ``/\``) are the *symbols*, which must appear
literally when the notation is used.

Identifiers enclosed in single quotes are treated as symbols and thus
lose their role as parameters. For example:

.. rocqtop:: in

   Notation "'IF' c1 'then' c2 'else' c3" := (c1 /\ c2 \/ ~ c1 /\ c3) (at level 200, right associativity).

Symbols that start with a single quote followed by at least 2
characters must be single quoted.  For example, the symbol `'ab` is
represented by `''ab'` in the notation string. Quoted strings can be used in
notations: they must begin and end with two double quotes.
Embedded spaces in these strings are
part of the string and do not contribute to the separation
between notation tokens. To embed double quotes in these strings, use four
double quotes (e.g. the notation :g:`"A ""I'm an """"infix"""" string symbol"" B"`
defines an infix notation whose infix symbol is the string
:g:`"I'm an ""infix"" string symbol"`). Symbols may contain
double quotes without being strings themselves (as e.g. in symbol :g:`|"|`) but notations with such symbols can be
used only for printing (see :ref:`Use of notations for printing <UseOfNotationsForPrinting>`).
In this case, no spaces are allowed in the symbol.  Also, if the
symbol starts with a double quote, it must be surrounded with single
quotes to prevent confusion with the beginning of a string symbol.

A notation binds a syntactic expression to a term, called its :gdef:`interpretation`. Unless the parser
and pretty-printer of Rocq already know how to deal with the syntactic
expression (such as through :cmd:`Reserved Notation` or for notations
that contain only literals), explicit precedences and
associativity rules have to be given.

.. note::

   The right-hand side of a notation is interpreted at the time the notation is
   given. Disambiguation of constants, :ref:`implicit arguments
   <ImplicitArguments>` and other notations are resolved at the
   time of the declaration of the notation. The right-hand side is
   currently typed only at use time but this may change in the future.

.. exn:: Unterminated string in notation

   Occurs when the notation string contains an unterminated quoted
   string, as e.g. in :g:`Reserved Notation "A ""an unended string B"`, for which the
   user may instead mean :g:`Reserved Notation "A ""an ended string"" B`.

.. exn:: End of quoted string not followed by a space in notation.

   Occurs when the notation string contains a quoted string which
   contains a double quote not ending the quoted string, as e.g. in
   :g:`Reserved Notation "A ""string""! B"` or `Reserved Notation "A ""string""!"" B"`, for which
   the user may instead mean :g:`Reserved Notation "A ""string"""" ! B`,
   :g:`Reserved Notation "A ""string""""!"" B`, or :g:`Reserved Notation "A '""string""!' B`.

Precedences and associativity
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Mixing different symbolic notations in the same text may cause serious
parsing ambiguity. To deal with the ambiguity of notations, Rocq uses
precedence levels ranging from 0 to 100 (plus one extra level numbered
200) and associativity rules.

Consider for example the new notation

.. rocqtop:: in

   Notation "A \/ B" := (or A B).

Clearly, an expression such as :g:`forall A:Prop, True /\ A \/ A \/ False`
is ambiguous. To tell the Rocq parser how to interpret the
expression, a priority between the symbols ``/\`` and ``\/`` has to be
given. Assume for instance that we want conjunction to bind more than
disjunction. This is expressed by assigning a precedence level to each
notation, knowing that a lower level binds more than a higher level.
Hence the level for disjunction must be higher than the level for
conjunction.

Since connectives are not tight articulation points of a text, it
is reasonable to choose levels not so far from the highest level which
is 100, for example 85 for disjunction and 80 for conjunction [#and_or_levels]_.

Similarly, an associativity is needed to decide whether :g:`True /\ False /\ False`
defaults to :g:`True /\ (False /\ False)` (right associativity) or to
:g:`(True /\ False) /\ False` (left associativity). We may even consider that the
expression is not well-formed and that parentheses are mandatory (this is a “no
associativity”) [#no_associativity]_. We do not know of a special convention for
the associativity of disjunction and conjunction, so let us apply
right associativity (which is the choice of Rocq).

Precedence levels and associativity rules of notations are specified with a list of
parenthesized :n:`@syntax_modifier`\s.  Here is how the previous examples refine:

.. rocqtop:: in

   Notation "A /\ B" := (and A B) (at level 80, right associativity).
   Notation "A \/ B" := (or A B) (at level 85, right associativity).

By default, a notation is considered nonassociative, but the
precedence level is mandatory (except for special cases whose level is
canonical). The level is either a number or the phrase ``next level``
whose meaning is obvious.
Some :ref:`associativities are predefined <init-notations>` in the
``Notations`` module.

.. TODO I don't find it obvious -- CPC

Complex notations
~~~~~~~~~~~~~~~~~

Notations can be made from arbitrarily complex symbols. One can for
instance define prefix notations.

.. rocqtop:: in

   Notation "~ x" := (not x) (at level 75, right associativity).

One can also define notations for incomplete terms, with the hole
expected to be inferred during type checking.

.. rocqtop:: in

   Notation "x = y" := (@eq _ x y) (at level 70, no associativity).

One can define *closed* notations whose both sides are symbols. In this case,
the default precedence level for the inner sub-expression is 200, and the default
level for the notation itself is 0.

.. rocqtop:: in

   Notation "( x , y )" := (@pair _ _ x y).

One can also define notations for binders.

.. rocqtop:: in

   Notation "{ x : A | P }" := (sig A (fun x => P)).

In the last case though, there is a conflict with the notation for
type casts. The notation for type casts, as shown by the command :cmd:`Print
Grammar` `constr` is at level 100. To avoid ``x : A`` being parsed as a type cast,
it is necessary to put ``x`` at a level below 100, typically 99. Hence, a correct
definition is the following:

.. rocqtop:: reset all

   Notation "{ x : A | P }" := (sig A (fun x => P)) (x at level 99).

More generally, it is required that notations are explicitly factorized on the
left. See the next section for more about factorization.

.. _NotationFactorization:

Simple factorization rules
~~~~~~~~~~~~~~~~~~~~~~~~~~

Rocq extensible parsing is performed by *Camlp5* which is essentially a LL1
parser: it decides which notation to parse by looking at tokens from left to right.
Hence, some care has to be taken not to hide already existing rules by new
rules. Indeed notations with a common prefix but different levels can
interfere with one another, making some of them unusable. For instance, a notation ``x << y`` with ``x``
and ``y`` at level 69 would be broken by another rule that puts
``y`` at another level, like ``x << y << z`` with ``x`` at level 69 and ``y``
at level 200. To avoid such issues, you should left factorize rules, that is ensure
that common prefixes use the samel levels.

.. rocqtop:: all

   Reserved Notation "x << y" (at level 70).
   Fail Reserved Notation "x << y << z" (at level 70, y at level 200).

In order to factorize the left part of the rules, the subexpression
referred to by ``y`` has to be at the same level in both rules. However the
default behavior puts ``y`` at the next level below 70 in the first rule
(``no associativity`` is the default). To fix this, we
need to force the parsing level of ``y``, as follows.

.. rocqtop:: reset all

   Reserved Notation "x << y" (at level 70).
   Reserved Notation "x << y << z" (at level 70, y at next level).

Or better yet, simply let the defaults ensure the best factorization.

.. rocqtop:: reset all

   Reserved Notation "x << y" (at level 70).
   Reserved Notation "x << y << z".
   Print Notation "_ << _ << _".

For the sake of factorization with Rocq predefined rules, simple rules
have to be observed for notations starting with a symbol, e.g., rules
starting with “\ ``{``\ ” or “\ ``(``\ ” should be put at level 0. The list
of Rocq predefined notations can be found in the chapter on :ref:`thecoqlibrary`.

.. warn:: Closed notations (i.e. starting and ending with a terminal symbol) should usually be at level 0 (default).
   :name: closed-notation-not-level-0

   It is usually better to put closed notations, that is the ones starting and ending with a terminal symbol, at level 0.

.. warn:: Postfix notations (i.e. starting with a nonterminal symbol and ending with a terminal symbol) should usually be at level 1 (default).")
   :name: postfix-notation-not-level-1

   It is usually better to put postfix notations, that is the ones ending with a terminal symbol, at level 1.

.. _UseOfNotationsForPrinting:

Use of notations for printing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The command :cmd:`Notation` has an effect both on the Rocq parser and on the
Rocq printer. For example:

.. rocqtop:: all

   Check (and True True).

However, printing, especially pretty-printing, also requires some
care. We may want specific indentations, line breaks, alignment if on
several lines, etc. For pretty-printing, Rocq relies on OCaml
formatting library, which provides indentation and automatic line
breaks depending on page width by means of *formatting boxes*.

The default printing of notations is rudimentary. For printing a
notation, a formatting box is opened in such a way that if the
notation and its arguments cannot fit on a single line, a line break
is inserted before the symbols of the notation and the arguments on
the next lines are aligned with the argument on the first line.

A first, simple control that a user can have on the printing of a
notation is the insertion of spaces at some places of the notation.
This is performed by adding extra spaces between the symbols and
parameters: each extra space (other than the single space needed to
separate the components) is interpreted as a space to be inserted by
the printer. Here is an example showing how to add spaces next to the
curly braces.

.. rocqtop:: in

   Notation "{{  x : A | P  }}" := (sig (fun x : A => P)) (at level 0, x at level 99).

.. rocqtop:: all

   Check (sig (fun x : nat => x=x)).

The second, more powerful control on printing is by using :n:`@syntax_modifier`\s. Here is an example

.. rocqtop:: in

   Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

.. rocqtop:: all

   Notation "'If' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
   (at level 200, right associativity, format
   "'[v   ' 'If'  c1 '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'").

.. rocqtop:: all

   Check
     (IF_then_else (IF_then_else True False True)
       (IF_then_else True False True)
       (IF_then_else True False True)).

A *format* tells how to control the indentation and line breaks when printing
a notation. It is a string extending the notation with
the possible following elements delimited by single quotes:

- tokens of the form ``'/ '`` are translated into breaking points.  If
  there is a line break, indents the number of spaces appearing after the
  “``/``” (no indentation in the example)

- tokens of the form ``'//'`` force writing on a new line

- well-bracketed pairs of tokens of the form ``'[ '`` and ``']'`` are
  translated into printing boxes; if there is a line break, an extra
  indentation of the number of spaces after the “``[``” is applied

- well-bracketed pairs of tokens of the form ``'[hv '`` and ``']'`` are
  translated into horizontal-or-else-vertical printing boxes; if the
  content of the box does not fit on a single line, then every breaking
  point forces a new line and an extra indentation of the number of
  spaces after the “``[hv``” is applied at the beginning of each new line

- well-bracketed pairs of tokens of the form ``'[v '`` and ``']'`` are
  translated into vertical printing boxes; every breaking point forces a
  new line, even if the line is large enough to display the whole content
  of the box, and an extra indentation of the number of spaces
  after the “``[v``” is applied at the beginning of each new line (3 spaces
  in the example)

- extra spaces in other tokens are preserved in the output

Notations disappear when a section is closed. No typing of the denoted
expression is performed at definition time. Type checking is done only
at the time of use of the notation.

.. note::

   The default for a notation is to be used both for parsing and
   printing. It is possible to declare a notation only for parsing by
   adding the option ``only parsing`` to the list of
   :n:`@syntax_modifier`\s of :cmd:`Notation`. Symmetrically, the
   ``only printing`` :n:`@syntax_modifier` can be used to declare that
   a notation should only be used for printing.

   If a notation to be used both for parsing and printing is
   overridden, both the parsing and printing are invalided, even if the
   overriding rule is only parsing.

   If a given notation string occurs only in ``only printing`` rules,
   the parser is not modified at all.

   Notations used for parsing, that is notations not restricted with
   the ``only printing`` modifier, can have only a single
   interpretation per scope. On the other side, notations marked with
   ``only printing`` can have multiple associated interpretations,
   even in the same scope.

.. note::

   When several notations can be used to print a given term, the
   notations which capture the largest subterm of the term are used
   preferentially. Here is an example:

   .. rocqtop:: in

     Notation "x < y" := (lt x y) (at level 70).
     Notation "x < y < z" := (lt x y /\ lt y z) (at level 70, y at next level).

     Check (0 < 1 /\ 1 < 2).

   When several notations match the same subterm, or incomparable
   subterms of the term to print, the notation declared most recently
   is selected. Moreover, reimporting a library or module declares the
   notations of this library or module again. If the notation is in a
   scope (see :ref:`Scopes`), either the scope has to be opened or a
   delimiter has to exist in the scope for the notation to be usable.

The Infix command
~~~~~~~~~~~~~~~~~~

The :cmd:`Infix` command is a shortcut for declaring notations for infix
symbols.

.. cmd:: Infix @notation_declaration

   The command

       :n:`Infix @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @scope_name }`

   is equivalent to

       :n:`Notation "x @string y" := (@one_term x y) {? ( {+, @syntax_modifier } ) } {? : @scope_name }`

   where ``x`` and ``y`` are fresh names and omitting the quotes around :n:`@string`.
   Here is an example:

   .. rocqtop:: in

      Infix "/\" := and (at level 80, right associativity).

.. _ReservingNotations:

Reserving notations
~~~~~~~~~~~~~~~~~~~

.. cmd:: Reserved Notation @string {? ( {+, @syntax_modifier } ) }

   A given notation may be used in different contexts. Rocq expects all
   uses of the notation to be defined at the same precedence and with the
   same associativity. To avoid giving the precedence and associativity
   every time, this command declares a parsing rule (:token:`string`) in advance
   without giving its interpretation. Here is an example from the initial
   state of Rocq.

   .. rocqtop:: in

      Reserved Notation "x = y" (at level 70, no associativity).

   Reserving a notation is also useful for simultaneously defining an
   inductive type or a recursive constant and a notation for it.

   .. note:: The notations mentioned in the module :ref:`init-notations` are reserved. Hence
             their precedence and associativity cannot be changed.

   .. cmd:: Reserved Infix @string {? ( {+, @syntax_modifier } ) }

      This command declares an infix parsing rule without giving its
      interpretation.

   When a format is attached to a reserved notation (with the `format`
   :token:`syntax_modifier`), it is used by
   default by all subsequent interpretations of the corresponding
   notation. Individual interpretations can override the format.

   .. warn:: Notations "a b" defined at level x and "a c" defined at level y have incompatible prefixes. One of them will likely not work.
      :name: notation-incompatible-prefix

      The two notations have a common prefix but different levels.
      The levels of one of the notations should be adjusted to match
      the other. See :ref:`factorization <NotationFactorization>` for
      details.

Simultaneous definition of terms and notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thanks to reserved notations, inductive and coinductive type declarations, recursive and
corecursive definitions can use customized notations. To do this, insert
a :token:`decl_notations` clause after the definition of the (co)inductive type or
(co)recursive term (or after the definition of each of them in case of mutual
definitions). Note that only syntax modifiers that do not require adding or
changing a parsing rule are accepted.

   .. insertprodn decl_notations decl_notations

   .. prodn::
      decl_notations ::= where @notation_declaration {* and @notation_declaration }

Here are examples:

.. rocqtop:: in

   Reserved Notation "A & B" (at level 80).

.. rocqtop:: in

   Inductive and' (A B : Prop) : Prop := conj' : A -> B -> A & B
   where "A & B" := (and' A B).

.. without this we get "not a truly recursive fixpoint"
.. rocqtop:: none

   Arguments S _ : clear scopes.

.. rocqtop:: in

   Fixpoint plus (n m : nat) {struct n} : nat :=
   match n with
       | O => m
       | S p => S (p + m)
   end
   where "n + m" := (plus n m).

Enabling and disabling notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: {| Enable | Disable } Notation {? {| @string | @qualid {* @ident__parm } } } {? := @one_term } {? ( {+, @enable_notation_flag } ) } {? {| : @scope_name | : no scope } }
   :name: Enable Notation; Disable Notation

   .. insertprodn enable_notation_flag enable_notation_flag

   .. prodn::
      enable_notation_flag ::= all
      | only parsing
      | only printing
      | in custom @ident
      | in constr

   Enables or disables notations previously defined with
   :cmd:`Notation` or :cmd:`Notation (abbreviation)`.
   Disabling a notation doesn't remove parsing rules or tokens defined by the notation.
   The command has no effect on notations reserved with :cmd:`Reserved Notation`.
   At least one of
   :token:`string`, :token:`qualid`, :token:`one_term` or :token:`scope_name` must be
   provided.
   When multiple clauses are provided, the notations enabled or
   disabled must satisfy all of their constraints.

   This command supports the :attr:`local` and :attr:`global`
   attributes.

   :n:`@string`
      Notations to enable or disable. :n:`@string` can be a single
      token in the notation such as "`->`" or a pattern that matches
      the notation. See :ref:`locating-notations`. If no
      :n:`{? := @one_term }` is given, the variables of the notation can be
      replaced by :n:`_`.

   :n:`@qualid {* @ident__parm }`
      Enable or disable :ref:`abbreviations <Abbreviations>` whose
      absolute name has :n:`@qualid` as a suffix. The :n:`{* @ident__parm }`
      are the parameters of the abbreviation.

   :n:`{? := @one_term }`
      Enable or disable notations matching :token:`one_term`.
      :token:`one_term` can be written using notations or not, as well
      as :n:`_`, just like in the :cmd:`Notation` command. If no
      :n:`@string` nor :n:`@qualid {* @ident__parm }` is given, the
      variables of the notation can be replaced by :n:`_`.

   :n:`all`
      Enable or disable all notations meeting the given constraints,
      even if there are multiple ones. Otherwise, there must be a single
      notation meeting the constraints.

   :n:`only parsing`
      The notation is enabled or disabled only for parsing.

   :n:`only printing`
      The notation is enabled or disabled only for printing.

   :n:`in custom @ident`
      Enable or disable notations in the given :ref:`custom entry
      <custom-entries>`.

   :n:`in constr`
      Enable or disable notations in the custom entry for :n:`constr`.
      See :ref:`custom entries <custom-entries>`.

   :n:`{| : @scope_name | : no scope }`
      If given, only notations in scope :token:`scope_name` are affected (or
      :term:`lonely notations <lonely notation>` for :n:`no scope`).

   .. exn:: Unexpected only printing for an only parsing notation.

      Cannot enable or disable for printing a notation that was
      originally defined as only parsing.

   .. exn:: Unexpected only parsing for an only printing notation.

      Cannot enable or disable for parsing a notation that was
      originally defined as only printing.

   .. warn:: Found no matching notation to enable or disable.
      :name: Found no matching notation to enable or disable

      No previously defined notation satisfies the given constraints.

   .. exn:: More than one interpretation bound to this notation, confirm with the "all" modifier.

      Use :n:`all` to allow enabling or disabling multiple
      notations in a single command.

   .. exn:: Unknown custom entry.

      In :n:`in custom @ident`, :token:`ident` is not a valid custom entry name.

   .. exn:: No notation provided.

      At least one of :token:`string`, :token:`qualid`,
      :token:`one_term` or :token:`scope_name` must be provided.

   .. warn:: Activation of abbreviations does not expect mentioning a grammar entry.

      ``in custom`` and ``in constr`` are not compatible with
      :ref:`abbreviations <Abbreviations>`.

   .. warn:: Activation of abbreviations does not expect mentioning a scope.

      Scopes are not compatible with :ref:`abbreviations <Abbreviations>`.

   .. example:: Enabling and disabling notations

      .. rocqtop:: all

         Disable Notation "+" (all).
         Enable Notation "_ + _" (all) : type_scope.
         Disable Notation "x + y" := (sum x y).

Displaying information about notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Notations

   This :term:`flag` controls whether to use notations for printing terms wherever possible.
   Default is on.

.. flag:: Printing Raw Literals

   This :term:`flag` controls whether to use string and number notations for printing terms
   wherever possible (see :ref:`string-notations`).
   Default is off.

.. flag:: Printing Parentheses

   When this :term:`flag` is on, parentheses are printed even if
   implied by associativity and precedence. Default is off.

.. seealso::

   :flag:`Printing All` to disable other elements in addition to notations.

.. cmd:: Print Notation @string {? in custom @ident }

   Displays information about the previously reserved notation string
   :token:`string`. :token:`ident`, if specified, is the name of the associated
   custom entry. See :cmd:`Declare Custom Entry`.

   .. rocqtop:: all

      Reserved Notation "x # y" (at level 123, right associativity).
      Print Notation "_ # _".

   Variables can be indicated with either `"_"` or names, as long as these can
   not be confused with notation symbols. When confusion may arise, for example
   with notation symbols that are entirely made up of letters, use single quotes
   to delimit those symbols. Using `"_"` is preferred, as it avoids this
   confusion. Note that there must always be (at least) a space between notation
   symbols and arguments, even when the notation format does not include those
   spaces.

   .. example:: :cmd:`Print Notation`

      .. rocqtop:: all

         Reserved Notation "x 'mod' y" (at level 40, no associativity).
         Print Notation "_ mod _".
         Print Notation "x 'mod' y".

         Reserved Notation "# x #" (at level 0, format "# x #").
         Fail Print Notation "#x#".
         Print Notation "# x #".

         Reserved Notation "( x , y , .. , z )" (at level 0).
         Print Notation "( _ , _ , .. , _ )".


         Reserved Notation "x $ y" (at level 50, left associativity).

         Declare Custom Entry expr.
         Reserved Notation "x $ y"
           (in custom expr at level 30, x custom expr, y at level 80, no associativity).

         Print Notation "_ $ _".
         Print Notation "_ $ _" in custom expr.

   .. exn:: @string cannot be interpreted as a known notation. Make sure that symbols are surrounded by spaces and that holes are explicitly denoted by "_".

      Occurs when :cmd:`Print Notation` can't find a notation associated with
      :token:`string`. This can happen, for example, when the notation does not
      exist in the current context, :token:`string` is not specific enough,
      there are missing spaces between symbols, or some symbols need to be
      quoted with `"'"`.

   .. exn:: @string cannot be interpreted as a known notation in @ident entry. Make sure that symbols are surrounded by spaces and that holes are explicitly denoted by "_".
      :undocumented:

.. seealso::

    :cmd:`Locate` for information on the definitions and scopes associated with
    a notation.

.. cmd:: Print Keywords

   Prints the current reserved :ref:`keywords <keywords>` and parser tokens, one
   per line. Keywords cannot be used as identifiers.

.. cmd:: Print Grammar {* @ident }

   When no :token:`ident` is provided, shows the whole grammar.
   Otherwise shows the grammar for the nonterminal :token:`ident`\s, except for
   the following, which will include some related nonterminals:

   - `constr` - for :token:`term`\s
   - `tactic` - for currently-defined tactic notations, :token:`tactic`\s and tacticals
     (corresponding to :token:`ltac_expr` in the documentation).
   - `vernac` - for :token:`command`\s
   - `ltac2` - for Ltac2 notations (corresponding to :token:`ltac2_expr`)

   This command can display any nonterminal in the grammar reachable from `vernac_control`.

   Most of the grammar in the documentation was updated in 8.12 to make it accurate and
   readable.  This was done using a new developer tool that extracts the grammar from the
   source code, edits it and inserts it into the documentation files.  While the
   edited grammar is equivalent to the original, for readability some nonterminals
   have been renamed and others have been eliminated by substituting the nonterminal
   definition where the nonterminal was referenced.  This command shows the original grammar,
   so it won't exactly match the documentation.

   The Rocq parser is based on Camlp5.  The documentation for
   `Extensible grammars <http://camlp5.github.io/doc/htmlc/grammars.html>`_ is the
   most relevant but it assumes considerable knowledge.  Here are the essentials:

   Productions can contain the following elements:

   - nonterminal names - identifiers in the form `[a-zA-Z0-9_]*`
   - `"…"` - a literal string that becomes a keyword and cannot be used as an :token:`ident`.
     The string doesn't have to be a valid identifier; frequently the string will contain only
     punctuation characters.
   - `IDENT "…"` - a literal string that has the form of an :token:`ident`
   - `OPT element` - optionally include `element` (e.g. a nonterminal, IDENT "…" or "…")
   - `LIST1 element` - a list of one or more `element`\s
   - `LIST0 element` - an optional list of `element`\s
   - `LIST1 element SEP sep` - a list of `element`\s separated by `sep`
   - `LIST0 element SEP sep` - an optional list of `element`\s separated by `sep`
   - `[ elements1 | elements2 | … ]` - alternatives (either `elements1` or `elements2` or …)

   Nonterminals can have multiple **levels** to specify precedence and associativity
   of its productions.  This feature of grammars makes it simple to parse input
   such as `1+2*3` in the usual way as `1+(2*3)`.  However, most nonterminals have a single level.

   For example, this output from `Print Grammar tactic` shows the first 3 levels for
   `ltac_expr`, designated as "5", "4" and "3".  Level 3 is right-associative,
   which applies to the productions within it, such as the `try` construct::

     Entry ltac_expr is
     [ "5" RIGHTA
       [ ]
     | "4" LEFTA
       [ SELF; ";"; SELF
       | SELF; ";"; tactic_then_locality; for_each_goal; "]" ]
     | "3" RIGHTA
       [ IDENT "try"; SELF
       :

   The interpretation of `SELF` depends on its position in the production and the
   associativity of the level:

   - At the beginning of a production, `SELF` means the next level.  In the
     fragment shown above, the next level for `try` is "2".  (This is defined by the order
     of appearance in the grammar or output; the levels could just as well be
     named "foo" and "bar".)
   - In the middle of a production, `SELF` means the top level ("5" in the fragment)
   - At the end of a production, `SELF` means the next level within
     `LEFTA` levels and the current level within `RIGHTA` levels.

   `NEXT` always means the next level. `nonterminal LEVEL "…"` is a reference to the specified level
   for `nonterminal`.

   `Associativity <http://camlp5.github.io/doc/htmlc/grammars.html#b:Associativity>`_
   explains `SELF` and `NEXT` in somewhat more detail.

   The output for `Print Grammar constr` includes :cmd:`Notation` definitions,
   which are dynamically added to the grammar at run time.
   For example, in the definition for `term`, the production on the second line shown
   here is defined by a :cmd:`Reserved Notation` command in `Notations.v`::

     | "50" LEFTA
       [ SELF; "||"; NEXT

   Similarly, `Print Grammar tactic` includes :cmd:`Tactic Notation`\s, such as :tacn:`dintuition`.

   The file
   `doc/tools/docgram/fullGrammar <http://github.com/coq/coq/blob/master/doc/tools/docgram/fullGrammar>`_
   in the source tree extracts the full grammar for
   Rocq (not including notations and tactic notations defined in `*.v` files nor some optionally-loaded plugins)
   in a single file with minor changes to handle nonterminals using multiple levels (described in
   `doc/tools/docgram/README.md <http://github.com/coq/coq/blob/master/doc/tools/docgram/README.md>`_).
   This is complete and much easier to read than the grammar source files.
   `doc/tools/docgram/orderedGrammar <http://github.com/coq/coq/blob/master/doc/tools/docgram/orderedGrammar>`_
   has the edited grammar that's used in the documentation.

   Developer documentation for parsing is in
   `dev/doc/parsing.md <http://github.com/coq/coq/blob/master/dev/doc/parsing.md>`_.

.. _locating-notations:

Locating notations
~~~~~~~~~~~~~~~~~~

To know to which notations a given symbol belongs to, use the :cmd:`Locate`
command. You can call it on any (composite) symbol surrounded by double quotes.
To locate a particular notation, use a string where the variables of the
notation are replaced by “``_``” and where possible single quotes inserted around
identifiers or tokens starting with a single quote are dropped.

.. rocqtop:: all

   Locate "exists".
   Locate "exists _ .. _ , _".

Inheritance of the properties of arguments of constants bound to a notation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If the right-hand side of a notation is a partially applied constant,
the notation inherits the implicit arguments (see
:ref:`ImplicitArguments`) and notation scopes (see
:ref:`Scopes`) of the constant. For instance:

.. rocqtop:: in reset

   Record R := {dom : Type; op : forall {A}, A -> dom}.
   Notation "# x" := (@op x) (at level 8).

.. rocqtop:: all

   Check fun x:R => # x 3.

As an exception, if the right-hand side is just of the form
:n:`@@qualid`, this conventionally stops the inheritance of implicit
arguments (but not of notation scopes).

.. _notations-and-binders:

Notations and binders
~~~~~~~~~~~~~~~~~~~~~

Notations can include binders. This section lists
different ways to deal with binders. For further examples, see also
:ref:`RecursiveNotationsWithBinders`.

Binders bound in the notation and parsed as identifiers
+++++++++++++++++++++++++++++++++++++++++++++++++++++++

Here is the basic example of a notation using a binder:

.. rocqtop:: in

   Notation "'sigma' x : A , B" := (sigT (fun x : A => B))
     (at level 200, x name, A at level 200, right associativity).

The binding variables in the right-hand side that occur as a parameter
of the notation (here :g:`x`) dynamically bind all the occurrences
in their respective binding scope after instantiation of the
parameters of the notation. This means that the term bound to :g:`B` can
refer to the variable name bound to :g:`x` as shown in the following
application of the notation:

.. rocqtop:: all

   Check sigma z : nat, z = 0.

Note the :n:`@syntax_modifier x name` in the declaration of the
notation. It tells to parse :g:`x` as a single identifier (or as the
unnamed variable :g:`_`).

Binders bound in the notation and parsed as patterns
++++++++++++++++++++++++++++++++++++++++++++++++++++

In the same way as patterns can be used as binders, as in
:g:`fun '(x,y) => x+y` or :g:`fun '(existT _ x _) => x`, notations can be
defined so that any :n:`@pattern` can be used in place of the
binder. Here is an example:

.. rocqtop:: in reset

   Notation "'subset' ' p , P " := (sig (fun p => P))
     (at level 200, p pattern, format "'subset'  ' p ,  P").

.. rocqtop:: all

   Check subset '(x,y), x+y=0.

The :n:`@syntax_modifier p pattern` in the declaration of the notation tells to parse
:g:`p` as a pattern. Note that a single variable is both an identifier and a
pattern, so, e.g., the following also works:

.. rocqtop:: all

   Check subset 'x, x=0.

If one wants to prevent such a notation to be used for printing when the
pattern is reduced to a single identifier, one has to use instead
the :n:`@syntax_modifier p strict pattern`. For parsing, however, a
``strict pattern`` will continue to include the case of a
variable. Here is an example showing the difference:

.. rocqtop:: in

   Notation "'subset_bis' ' p , P" := (sig (fun p => P))
     (at level 200, p strict pattern).
   Notation "'subset_bis' p , P " := (sig (fun p => P))
     (at level 200, p name).

.. rocqtop:: all

   Check subset_bis 'x, x=0.

The default level for a ``pattern`` is 0. One can use a different level by
using ``pattern at level`` :math:`n` where the scale is the same as the one for
terms (see :ref:`init-notations`).

Binders bound in the notation and parsed as terms
+++++++++++++++++++++++++++++++++++++++++++++++++

Sometimes, for the sake of factorization of rules, a binder has to be
parsed as a term. This is typically the case for a notation such as
the following:

.. rocqdoc::

   Notation "{ x : A | P }" := (sig (fun x : A => P))
       (at level 0, x at level 99 as name).

This is so because the grammar also contains rules starting with :g:`{}` and
followed by a term, such as the rule for the notation :g:`{ A } + { B }` for the
constant :g:`sumbool` (see :ref:`specification`).

Then, in the rule, ``x name`` is replaced by ``x at level 99 as name`` meaning
that ``x`` is parsed as a term at level 99 (as done in the notation for
:g:`sumbool`), but that this term has actually to be a name, i.e. an
identifier or :g:`_`.

The notation :g:`{ x | P }` is already defined in the standard
library with the ``as name`` :n:`@syntax_modifier`. We cannot redefine it but
one can define an alternative notation, say :g:`{ p such that P }`,
using instead ``as pattern``.

.. rocqtop:: in

   Notation "{ p 'such' 'that' P }" := (sig (fun p => P))
     (at level 0, p at level 99 as pattern).

Then, the following works:

.. rocqtop:: all

   Check {(x,y) such that x+y=0}.

To enforce that the pattern should not be used for printing when it
is just a name, one could have said
``p at level 99 as strict pattern``.

Note also that in the absence of a ``as name``, ``as strict pattern`` or
``as pattern`` :n:`@syntax_modifier`\s, the default is to consider sub-expressions occurring
in binding position and parsed as terms to be ``as name``.

Binders bound in the notation and parsed as general binders
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

It is also possible to rely on Rocq's syntax of binders using the
`binder` modifier as follows:

.. rocqtop:: in

   Notation "'myforall' p , [ P , Q ] " := (forall p, P -> Q)
     (at level 200, p binder).

In this case, all of :n:`@ident`, :n:`{@ident}`, :n:`[@ident]`, :n:`@ident:@type`,
:n:`{@ident:@type}`, :n:`[@ident:@type]`, :n:`'@pattern` can be used in place of
the corresponding notation variable. In particular, the binder can
declare implicit arguments:

.. rocqtop:: all

   Check fun (f : myforall {a}, [a=0, Prop]) => f eq_refl.
   Check myforall '((x,y):nat*nat), [ x = y, True ].

By using instead `closed binder`, the same list of binders is allowed
except that :n:`@ident:@type` requires parentheses around.

.. _NotationsWithBinders:

Binders not bound in the notation
+++++++++++++++++++++++++++++++++

We can also have binders in the right-hand side of a notation which
are not themselves bound in the notation. In this case, the binders
are considered up to renaming of the internal binder. E.g., for the
notation

.. rocqtop:: in

   Notation "'exists_different' n" := (exists p:nat, p<>n) (at level 200).

the next command fails because p does not bind in the instance of n.

.. rocqtop:: all

   Fail Check (exists_different p).

.. rocqtop:: in

   Notation "[> a , .. , b <]" :=
     (cons a .. (cons b nil) .., cons b .. (cons a nil) ..).

Notations with expressions used both as binder and term
+++++++++++++++++++++++++++++++++++++++++++++++++++++++

It is possible to use parameters of the notation both in term and
binding position. Here is an example:

.. rocqtop:: in

   Definition force n (P:nat -> Prop) := forall n', n' >= n -> P n'.
   Notation "▢_ n P" := (force n (fun n => P))
     (at level 0, n name, P at level 9, format "▢_ n  P").

.. rocqtop:: all

   Check exists p, ▢_p (p >= 1).

More generally, the parameter can be a pattern, as in the following
variant:

.. rocqtop:: in reset

   Definition force2 q (P:nat*nat -> Prop) :=
     (forall n', n' >= fst q -> forall p', p' >= snd q -> P q).

   Notation "▢_ p P" := (force2 p (fun p => P))
     (at level 0, p pattern at level 0, P at level 9, format "▢_ p  P").

.. rocqtop:: all

   Check exists x y, ▢_(x,y) (x >= 1 /\ y >= 2).

This support is experimental. For instance, the notation is used for
printing only if the occurrence of the parameter in term position
comes in the right-hand side before the occurrence in binding position.

.. _RecursiveNotations:

Notations with recursive patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A mechanism is provided for declaring elementary notations with
recursive patterns. The basic example is:

.. rocqtop:: all

   Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

On the right-hand side, an extra construction of the form ``.. t ..`` can
be used. Notice that ``..`` is part of the Rocq syntax and it must not be
confused with the three-dots notation “``…``” used in this manual to denote
a sequence of arbitrary size.

On the left-hand side, the part “``x s .. s y``” of the notation parses
any number of times (but at least once) a sequence of expressions
separated by the sequence of tokens ``s`` (in the example, ``s`` is just “``;``”).

The right-hand side must contain a subterm of the form either
``φ(x, .. φ(y,t) ..)`` or ``φ(y, .. φ(x,t) ..)`` where :math:`φ([~]_E , [~]_I)`,
called the *iterator* of the recursive notation is an arbitrary expression with
distinguished placeholders and where :math:`t` is called the *terminating
expression* of the recursive notation. In the example, we choose the names
:math:`x` and :math:`y` but in practice they can of course be chosen
arbitrarily. Note that the placeholder :math:`[~]_I` has to occur only once but
:math:`[~]_E` can occur several times.

Parsing the notation produces a list of expressions which are used to
fill the first placeholder of the iterating pattern which itself is
repeatedly nested as many times as the length of the list, the second
placeholder being the nesting point. In the innermost occurrence of the
nested iterating pattern, the second placeholder is finally filled with the
terminating expression.

In the example above, the iterator :math:`φ([~]_E , [~]_I)` is :math:`cons [~]_E\, [~]_I`
and the terminating expression is ``nil``.

Here is another example with the pattern associating on the left:

.. rocqtop:: in

   Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).

Here is an example with more involved recursive patterns:

.. rocqtop:: in

   Notation "[| t * ( x , y , .. , z ) ; ( a , b , .. , c )  * u |]" :=
     (pair (pair .. (pair (pair t x) (pair t y)) .. (pair t z))
           (pair .. (pair (pair a u) (pair b u)) .. (pair c u)))
     (t at level 39).

To give a flavor of the extent and limits of the mechanism, here is an
example showing a notation for a chain of equalities. It relies on an
artificial expansion of the intended denotation so as to expose a
``φ(x, .. φ(y,t) ..)`` structure, with the drawback that if ever the
beta-redexes are contracted, the notations stops to be used for
printing. Support for notations defined in this way should be considered
experimental.

.. rocqtop:: in

   Notation "x  ⪯ y  ⪯ ..  ⪯ z  ⪯ t" :=
     ((fun b A a => a <= b /\ A b) y .. ((fun b A a => a <= b /\ A b) z (fun b => b <= t)) .. x)
     (at level 70, y at next level, z at next level, t at next level).

Note finally that notations with recursive patterns can be reserved like
standard notations, they can also be declared within :ref:`notation
scopes <Scopes>`.

.. _RecursiveNotationsWithBinders:

Notations with recursive patterns involving binders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recursive notations can also be used with binders. The basic example
is:

.. rocqtop:: in

   Notation "'exists' x .. y , p" :=
     (ex (fun x => .. (ex (fun y => p)) ..))
     (at level 200, x binder, y binder, right associativity).

The principle is the same as in :ref:`RecursiveNotations`
except that in the iterator
:math:`φ([~]_E , [~]_I)`, the placeholder :math:`[~]_E` can also occur in
position of the binding variable of a ``fun`` or a ``forall``.

To specify that the part “``x .. y``” of the notation parses a sequence of
binders, ``x`` and ``y`` must be marked as ``binder`` in the list of :n:`@syntax_modifier`\s
of the notation. The binders of the parsed sequence are used to fill the
occurrences of the first placeholder of the iterating pattern which is
repeatedly nested as many times as the number of binders generated. If ever the
generalization operator ``'`` (see :ref:`implicit-generalization`) is
used in the binding list, the added binders are taken into account too.

There are two flavors of binder parsing. If ``x`` and ``y`` are marked as binder,
then a sequence such as :g:`a b c : T` will be accepted and interpreted as
the sequence of binders :g:`(a:T) (b:T) (c:T)`. For instance, in the
notation above, the syntax :g:`exists a b : nat, a = b` is valid.

The variables ``x`` and ``y`` can also be marked as closed binder in which
case only well-bracketed binders of the form :g:`(a b c:T)` or :g:`{a b c:T}`
etc. are accepted.

With closed binders, the recursive sequence in the left-hand side can
be of the more general form ``x s .. s y`` where ``s`` is an arbitrary sequence of
tokens. With open binders though, ``s`` has to be empty. Here is an
example of recursive notation with closed binders:

.. rocqtop:: in

   Notation "'mylet' f x .. y :=  t 'in' u":=
     (let f := fun x => .. (fun y => t) .. in u)
     (at level 200, x closed binder, y closed binder, right associativity).

A recursive pattern for binders can be used in position of a recursive
pattern for terms. Here is an example:

.. rocqtop:: in

   Notation "'FUNAPP' x .. y , f" :=
     (fun x => .. (fun y => (.. (f x) ..) y ) ..)
     (at level 200, x binder, y binder, right associativity).

If an occurrence of the :math:`[~]_E` is not in position of a binding
variable but of a term, it is the name used in the binding which is
used. Here is an example:

.. rocqtop:: in

   Notation "'exists_non_null' x .. y  , P" :=
     (ex (fun x => x <> 0 /\ .. (ex (fun y => y <> 0 /\ P)) ..))
     (at level 200, x binder).

Predefined entries
~~~~~~~~~~~~~~~~~~

By default, sub-expressions are parsed as terms and the corresponding
grammar entry is called ``constr``. However, one may sometimes want
to restrict the syntax of terms in a notation. For instance, the
following notation will accept to parse only global reference in
position of :g:`x`:

.. rocqtop:: in

   Notation "'apply' f a1 .. an" := (.. (f a1) .. an)
     (at level 10, f global, a1, an at level 9).

In addition to ``global``, one can restrict the syntax of a
sub-expression by using the entry names ``ident``, ``name`` or ``pattern``
already seen in :ref:`NotationsWithBinders`, even when the
corresponding expression is not used as a binder in the right-hand
side. E.g.:

.. rocqtop:: in

   Notation "'apply_id' f a1 .. an" := (.. (f a1) .. an)
     (at level 10, f ident, a1, an at level 9).

.. _custom-entries:

Custom entries
~~~~~~~~~~~~~~

.. cmd:: Declare Custom Entry @ident

   Defines new grammar entries, called *custom
   entries*, that can later be referred to using the entry name
   :n:`custom @ident`.

   This command supports the :attr:`local` attribute, which limits the entry to the
   current module.

   Non-local custom entries survive module closing and are
   declared when a file is Required.

.. example::

   For instance, we may want to define an ad hoc
   parser for arithmetical operations and proceed as follows:

   .. rocqtop:: reset all

      Inductive Expr :=
      | One : Expr
      | Mul : Expr -> Expr -> Expr
      | Add : Expr -> Expr -> Expr.

      Declare Custom Entry expr.
      Notation "[ e ]" := e (e custom expr at level 2).
      Notation "1" := One (in custom expr at level 0).
      Notation "x y" := (Mul x y) (in custom expr at level 1, left associativity).
      Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).
      Notation "( x )" := x (in custom expr, x at level 2).
      Notation "{ x }" := x (in custom expr, x constr).
      Notation "x" := x (in custom expr at level 0, x ident).

      Axiom f : nat -> Expr.
      Check fun x y z => [1 + y z + {f x}].
      Unset Printing Notations.
      Check fun x y z => [1 + y z + {f x}].
      Set Printing Notations.
      Check fun e => match e with
      | [1 + 1] => [1]
      | [x y + z] => [x + y z]
      | y => [y + e]
      end.

Custom entries have levels, like the main grammar of terms and grammar
of patterns have. The lower level is 0 and this is the level used by
default to put rules delimited with tokens on both ends. The level is
left to be inferred by Rocq when using :n:`in custom @ident`. The
level is otherwise given explicitly by using the syntax
:n:`in custom @ident at level @natural`, where :n:`@natural` refers to the level.

Levels are cumulative: a notation at level ``n`` of which the left end
is a term shall use rules at level less than ``n`` to parse this
subterm. More precisely, it shall use rules at level strictly less
than ``n`` if the rule is declared with ``right associativity`` and
rules at level less or equal than ``n`` if the rule is declared with
``left associativity``. Similarly, a notation at level ``n`` of which
the right end is a term shall use by default rules at level strictly
less than ``n`` to parse this subterm if the rule is declared left
associative and rules at level less or equal than ``n`` if the rule is
declared right associative. This is what happens for instance in the
rule

.. rocqtop:: in

   Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).

where ``x`` is any expression parsed in entry
``expr`` at level less or equal than ``2`` (including, recursively,
the given rule) and ``y`` is any expression parsed in entry ``expr``
at level strictly less than ``2``.

Rules associated with an entry can refer different sub-entries. The
grammar entry name ``constr`` can be used to refer to the main grammar
of term as in the rule

.. rocqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

which indicates that the subterm ``x`` should be
parsed using the main grammar. If not indicated, the level is computed
as for notations in ``constr``, e.g. using 200 as default level for
inner sub-expressions. The level can otherwise be indicated explicitly
by using ``constr at level n`` for some ``n``, or ``constr at next
level``.

Conversely, custom entries can be used to parse sub-expressions of the
main grammar, or from another custom entry as is the case in

.. rocqtop:: in

   Notation "[ e ]" := e (e custom expr at level 2).

to indicate that ``e`` has to be parsed at level ``2`` of the grammar
associated with the custom entry ``expr``. The level can be omitted, as in

.. rocqdoc::

   Notation "[ e ]" := e (e custom expr).

in which case Rocq infer it. If the sub-expression is at a border of
the notation (as e.g. ``x`` and ``y`` in ``x + y``), the level is
determined by the associativity. If the sub-expression is not at the
border of the notation (as e.g. ``e`` in ``"[ e ]``), the level is
inferred to be the highest level used for the entry. In particular,
this level depends on the highest level existing in the entry at the
time of use of the notation.

In the absence of an explicit entry for parsing or printing a
sub-expression of a notation in a custom entry, the default is to
consider that this sub-expression is parsed or printed in the same
custom entry where the notation is defined. In particular, if ``x at
level n`` is used for a sub-expression of a notation defined in custom
entry ``foo``, it shall be understood the same as ``x custom foo at
level n``.

In general, rules are required to be *productive* on the right-hand
side, i.e. that they are bound to an expression which is not
reduced to a single variable. If the rule is not productive on the
right-hand side, as it is the case above for

.. rocqtop:: in

   Notation "( x )" := x (in custom expr at level 0, x at level 2).

and

.. rocqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

it is used as a *grammar coercion* which means that it is used to parse or
print an expression which is not available in the current grammar at the
current level of parsing or printing for this grammar but which is available
in another grammar or in another level of the current grammar. For instance,

.. rocqtop:: in

   Notation "( x )" := x (in custom expr at level 0, x at level 2).

tells that parentheses can be inserted to parse or print an expression
declared at level ``2`` of ``expr`` whenever this expression is
expected to be used as a subterm at level 0 or 1.  This allows for
instance to parse and print :g:`Add x y` as a subterm of :g:`Mul (Add
x y) z` using the syntax ``(x + y) z``. Similarly,

.. rocqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

gives a way to let any arbitrary expression which is not handled by the
custom entry ``expr`` be parsed or printed by the main grammar of term
up to the insertion of a pair of curly brackets.

Another special situation is when parsing global references or
identifiers. To indicate that a custom entry should parse identifiers,
use the following form:

.. rocqtop:: reset none

   Declare Custom Entry expr.

.. rocqtop:: in

   Notation "x" := x (in custom expr at level 0, x ident).

Similarly, to indicate that a custom entry should parse global references
(i.e. qualified or unqualified identifiers), use the following form:

.. rocqtop:: reset none

   Declare Custom Entry expr.

.. rocqtop:: in

   Notation "x" := x (in custom expr at level 0, x global).

.. cmd:: Print Custom Grammar @ident

   This displays the state of the grammar for terms associated with
   the custom entry :token:`ident`.

.. _NotationSyntax:

Syntax
~~~~~~~

Here are the syntax elements used by the various notation commands.

   .. insertprodn syntax_modifier level

   .. prodn::
      syntax_modifier ::= at level @natural
      | in custom @ident {? at level @natural }
      | {+, @ident } {| at @level | in scope @ident }
      | @ident at @level {? @binder_interp }
      | @ident @explicit_subentry
      | @ident @binder_interp
      | left associativity
      | right associativity
      | no associativity
      | only parsing
      | format @string
      | only printing
      explicit_subentry ::= ident
      | name
      | global
      | bigint
      | strict pattern {? at level @natural }
      | binder
      | closed binder
      | constr {? at @level } {? @binder_interp }
      | custom @ident {? at @level } {? @binder_interp }
      | pattern {? at level @natural }
      binder_interp ::= as ident
      | as name
      | as pattern
      | as strict pattern
      level ::= level @natural
      | next level

Note that `_` by itself is a valid :n:`@name` but is not a valid :n:`@ident`.

.. note:: No typing of the denoted expression is performed at definition
          time. Type checking is done only at the time of use of the notation.

.. note:: Some examples of Notation may be found in the files composing
          the initial state of Rocq (see directory :file:`$ROCQLIB/theories/Init`).

.. note:: The notation ``"{ x }"`` has a special status in the main grammars of
          terms and patterns so that
          complex notations of the form ``"x + { y }"`` or ``"x * { y }"`` can be
          nested with correct precedences. Especially, every notation involving
          a pattern of the form ``"{ x }"`` is parsed as a notation where the
          pattern ``"{ x }"`` has been simply replaced by ``"x"`` and the curly
          braces are parsed separately. E.g. ``"y + { z }"`` is not parsed as a
          term of the given form but as a term of the form ``"y + z"`` where ``z``
          has been parsed using the rule parsing ``"{ x }"``. Especially, level
          and precedences for a rule including patterns of the form ``"{ x }"``
          are relative not to the textual notation but to the notation where the
          curly braces have been removed (e.g. the level and the associativity
          given to some notation, say ``"{ y } & { z }"`` in fact applies to the
          underlying ``"{ x }"``\-free rule which is ``"y & z"``).

.. note:: Notations such as ``"( p | q )"`` (or starting with ``"( x | "``,
          more generally) are deprecated as they conflict with the syntax for
          nested disjunctive patterns (see :ref:`extendedpatternmatching`),
          and are not honored in pattern expressions.

          .. warn:: Use of @string Notation is deprecated as it is inconsistent with pattern syntax.

             This warning is disabled by default to avoid spurious diagnostics
             due to legacy notation in the Rocq standard library.
             It can be turned on with the ``-w disj-pattern-notation`` flag.

.. exn:: Unknown custom entry: @ident.

   Occurs when :cmd:`Notation` or :cmd:`Print Notation` can't find the custom entry given by the user.

.. _Scopes:

Notation scopes
---------------

A :gdef:`notation scope` is a set of notations for terms with their
interpretations. Notation scopes provide a weak, purely
syntactic form of notation overloading: a symbol may
refer to different definitions depending on which notation scopes
are currently open.  For instance, the infix symbol ``+`` can be
used to refer to distinct definitions of the addition operator,
such as for natural numbers, integers or reals.
Notation scopes can include an interpretation for numbers and
strings with the :cmd:`Number Notation` and :cmd:`String Notation` commands.

   .. insertprodn scope scope_key

   .. prodn::
      scope ::= @scope_name
      | @scope_key
      scope_name ::= @ident
      scope_key ::= @ident

Each notation scope has a single :token:`scope_name`, which by convention
ends with the suffix "_scope", as in "nat_scope".  One or more :token:`scope_key`\s
(delimiting keys) may be associated with a notation scope with the :cmd:`Delimit Scope` command.
Most commands use :token:`scope_name`; :token:`scope_key`\s are used within :token:`term`\s.

.. cmd:: Declare Scope @scope_name

   Declares a new notation scope. Note that the initial
   state of Rocq declares the following notation scopes:

   ``bool_scope``, ``byte_scope``, ``core_scope``, ``dec_int_scope``,
   ``dec_uint_scope``, ``function_scope``, ``hex_int_scope``, ``hex_nat_scope``,
   ``hex_uint_scope``, ``list_scope``, ``nat_scope``, ``type_scope``.

   Use commands such as :cmd:`Notation` to add notations to the scope.

.. exn:: Scope names should not start with an underscore.

   Scope names starting with an underscore would make the :g:`%_` syntax ambiguous.

Global interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At any time, the interpretation of a notation for a term is done within
a *stack* of notation scopes and :term:`lonely notations <lonely notation>`. If a
notation is defined in multiple scopes, Rocq uses the interpretation from
the most recently opened notation scope or declared lonely notation.

Note that "stack" is a misleading name.  Each scope or lonely notation can only appear in
the stack once.  New items are pushed onto the top of the stack, except that
adding a item that's already in the stack moves it to the top of the stack instead.
Scopes are removed by name (e.g. by :cmd:`Close Scope`) wherever they are in the
stack, rather than through "pop" operations.

Use the :cmd:`Print Visibility` command to display the current notation scope stack.

The initial state of Rocq has the following scopes opened: ``core_scope``,
``function_scope``, ``type_scope`` and ``nat_scope``, ``nat_scope`` being the
top of the scopes stack.

.. cmd:: Open Scope @scope

   Adds a scope to the notation scope stack.  If the scope is already present,
   the command moves it to the top of the stack.

   If the command appears in a section: By default, the scope is only added within the
   section.  Specifying :attr:`global` marks the scope for export as part of the current
   module.  Specifying :attr:`local` behaves like the default.

   If the command does not appear in a section: By default, the scope marks the scope for
   export as part of the current module.  Specifying :attr:`local` prevents exporting the scope.
   Specifying :attr:`global` behaves like the default.

.. cmd:: Close Scope @scope

   Removes a scope from the notation scope stack.

   If the command appears in a section: By default, the scope is only removed within the
   section.  Specifying :attr:`global` marks the scope removal for export as part of the current
   module.  Specifying :attr:`local` behaves like the default.

   If the command does not appear in a section: By default, the scope marks the scope removal for
   export as part of the current module.  Specifying :attr:`local` prevents exporting the removal.
   Specifying :attr:`global` behaves like the default.

   .. todo: Strange notion, exporting something that _removes_ a scope.
      See https://github.com/coq/coq/pull/11718#discussion_r413667817

.. _LocalInterpretationRulesForNotations:

Local interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In addition to the global rules of interpretation of notations, some
ways to change the interpretation of subterms are available.

Opening a notation scope locally
++++++++++++++++++++++++++++++++

.. insertprodn term_scope term_scope

.. prodn::
   term_scope ::= @term0 % @scope_key
   | @term0 %_ @scope_key

The notation scope stack can be locally extended within
a :token:`term` with the syntax
:n:`(@term)%@scope_key` (or simply :n:`@term0%@scope_key` for atomic terms).

In this case, :n:`@term` is
interpreted in the scope stack extended with the scope bound to :n:`@scope_key`.

The term :n:`@term0%_@scope_key` is interpreted similarly to :n:`@term0%@scope_key`
except that the scope stack is only temporarily extended for the head of :n:`@term0`,
rather than all its subterms.

.. cmd:: Delimit Scope @scope_name with @scope_key

   Binds the delimiting key :token:`scope_key` to a scope.

.. cmd:: Undelimit Scope @scope_name

   Removes the delimiting keys associated with a scope.

.. exn:: Scope delimiters should not start with an underscore.

   Scope delimiters starting with an underscore would make the :g:`%_` syntax ambiguous.

The arguments of an :ref:`abbreviation <Abbreviations>` can be interpreted
in a scope stack locally extended with a given scope by using the modifier
:n:`{+, @ident } in scope @scope_name`.s

Binding types or coercion classes to notation scopes
++++++++++++++++++++++++++++++++++++++++++++++++++++

.. cmd:: Bind Scope @scope_name with {+ @coercion_class }

   Binds the notation scope :token:`scope_name` to the type or coercion class
   :token:`coercion_class`.
   When bound, arguments of that type for any function will be interpreted in
   that scope by default.  This default can be overridden for individual functions
   with the :cmd:`Arguments` command. See :ref:`binding_to_scope` for details.
   The association may be convenient
   when a notation scope is naturally associated with a :token:`type` (e.g.
   `nat` and the natural numbers).

   Whether the argument of a function has some type ``type`` is determined
   statically. For instance, if ``f`` is a polymorphic function of type
   :g:`forall X:Type, X -> X` and type :g:`t` is bound to a scope ``scope``,
   then :g:`a` of type :g:`t` in :g:`f t a` is not recognized as an argument to
   be interpreted in scope ``scope``.

   In explicit :ref:`casts <type-cast>` :n:`@term : @coercion_class`, the :n:`term`
   is interpreted in the :token:`scope_name` associated with :n:`@coercion_class`.

   This command supports the :attr:`local`, :attr:`global`,
   :attr:`add_top` and :attr:`add_bottom` attributes.

   .. attr:: add_top
             add_bottom

      These :ref:`attributes <attribute>` allow adding additional
      bindings at the top or bottom of the stack of already declared
      bindings. In absence of such attributes, any new binding clears
      the previous ones. This makes it possible to bind multiple scopes
      to the same :token:`coercion_class`.

   .. example:: Binding scopes to a type

      Let's declare two scopes with a notation in each and an arbitrary
      function on type ``bool``.

      .. rocqtop:: in reset

         Declare Scope T_scope.
         Declare Scope F_scope.
         Notation "#" := true (only parsing) : T_scope.
         Notation "#" := false (only parsing) : F_scope.

         Parameter f : bool -> bool.

      By default, the argument of ``f`` is interpreted in the
      currently opened scopes.

      .. rocqtop:: all

         Open Scope T_scope.
         Check f #.
         Open Scope F_scope.
         Check f #.

      This can be changed by binding scopes to the type ``bool``.

      .. rocqtop:: all

         Bind Scope T_scope with bool.
         Check f #.

      When multiple scopes are attached to a type, notations are
      interpreted in the first scope containing them, from the top of
      the stack.

      .. rocqtop:: all

         #[add_top] Bind Scope F_scope with bool.
         Check f #.

         Notation "##" := (negb false) (only parsing) : T_scope.
         Check f ##.

      Bindings for functions can be displayed with the
      :cmd:`About` command.

      .. rocqtop:: all

         About f.

      Bindings are also used in casts.

      .. rocqtop:: all

         Close Scope F_scope.
         Check #.
         Check # : bool.

      .. note:: Such stacks of scopes can be handy to share notations
         between multiple types. For instance, the scope ``T_scope``
         above could contain many generic notations used for both the
         ``bool`` and ``nat`` types, while the scope ``F_scope`` could
         override some of these notations specifically for
         ``bool`` and another ``F'_scope`` could override them
         specifically for ``nat``, which could then be bound to
         ``%F'_scope%T_scope``.

   .. note:: When active, a bound scope has effect on all defined functions
             (even if they are defined after the :cmd:`Bind Scope` directive), except
             if argument scopes were assigned explicitly using the
             :cmd:`Arguments` command.

   .. note:: The scopes ``type_scope`` and ``function_scope`` also have a local
             effect on interpretation. See the next section.

The ``type_scope`` notation scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index:: type_scope

The scope ``type_scope`` has a special status. It is a primitive interpretation
scope which is temporarily activated each time a subterm of an expression is
expected to be a type. It is delimited by the key ``type``, and bound to the
coercion class ``Sortclass``. It is also used in certain situations where an
expression is statically known to be a type, including the conclusion and the
type of hypotheses within an Ltac goal match (see
:ref:`ltac-match-goal`), the statement of a theorem, the type of a definition,
the type of a binder, the domain and codomain of implication, the codomain of
products, and more generally any type argument of a declared or defined
constant.

The ``function_scope`` notation scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index:: function_scope

The scope ``function_scope`` also has a special status.
It is temporarily activated each time the argument of a global reference is
recognized to be a ``Funclass`` instance, i.e., of type :g:`forall x:A, B` or
:g:`A -> B`.


.. _notation-scopes:

Notation scopes used in the standard library of Rocq
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We give an overview of the scopes used in the standard library of Rocq.
For a complete list of notations in each scope, use the commands :cmd:`Print
Scopes` or :cmd:`Print Scope`.

``type_scope``
  This scope includes infix * for product types and infix + for sum types. It
  is delimited by the key ``type``, and bound to the coercion class
  ``Sortclass``, as described above.

``function_scope``
  This scope is delimited by the key ``function``, and bound to the coercion class
  ``Funclass``, as described above.

``nat_scope``
  This scope includes the standard arithmetical operators and relations on type
  nat. Positive integer numbers in this scope are mapped to their canonical
  representent built from :g:`O` and :g:`S`. The scope is delimited by the key
  ``nat``, and bound to the type :g:`nat` (see above).

``N_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`N` (binary natural numbers). It is delimited by the key ``N`` and comes
  with an interpretation for numbers as closed terms of type :g:`N`.

``Z_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`Z` (binary integer numbers). It is delimited by the key ``Z`` and comes
  with an interpretation for numbers as closed terms of type :g:`Z`.

``positive_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`positive` (binary strictly positive numbers). It is delimited by
  key ``positive`` and comes with an interpretation for numbers as closed
  terms of type :g:`positive`.

``Q_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`Q` (rational numbers defined as fractions of an integer and a
  strictly positive integer modulo the equality of the numerator-
  denominator cross-product) and comes with an interpretation for numbers
  as closed terms of type :g:`Q`.

``Qc_scope``
  This scope includes the standard arithmetical operators and relations on the
  type :g:`Qc` of rational numbers defined as the type of irreducible
  fractions of an integer and a strictly positive integer.

``R_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`R` (axiomatic real numbers). It is delimited by the key ``R`` and comes
  with an interpretation for numbers using the :g:`IZR` morphism from binary
  integer numbers to :g:`R` and :g:`Z.pow_pos` for potential exponent parts.

``bool_scope``
  This scope includes notations for the boolean operators. It is delimited by the
  key ``bool``, and bound to the type :g:`bool` (see above).

``list_scope``
  This scope includes notations for the list operators. It is delimited by the key
  ``list``, and bound to the type :g:`list` (see above).

``core_scope``
  This scope includes the notation for pairs. It is delimited by the key ``core``.

``string_scope``
  This scope includes notation for strings as elements of the type string.
  Special characters and escaping follow Rocq conventions on strings (see
  :ref:`lexical-conventions`). Especially, there is no convention to visualize non
  printable characters of a string. The file :file:`String.v` shows an example
  that contains quotes, a newline and a beep (i.e. the ASCII character
  of code 7).

``char_scope``
  This scope includes interpretation for all strings of the form ``"c"``
  where :g:`c` is an ASCII character, or of the form ``"nnn"`` where nnn is
  a three-digit number (possibly with leading 0s), or of the form
  ``""""``. Their respective denotations are the ASCII code of :g:`c`, the
  decimal ASCII code ``nnn``, or the ascii code of the character ``"`` (i.e.
  the ASCII code 34), all of them being represented in the type :g:`ascii`.


Displaying information about scopes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Visibility {? @scope_name }

   Displays the current notation scope stack. The top of the stack
   is displayed last. Notations in scopes whose interpretation is hidden
   by the same notation in a more recently opened scope are not displayed.
   Hence each notation is displayed only once.

   If :n:`@scope_name` is specified,
   displays the current notation scope stack
   as if the scope :n:`@scope_name` is pushed on top of the stack. This is
   useful to see how a subterm occurring locally in the scope is
   interpreted.

.. cmd:: Print Scopes

   Displays, for each existing notation scope, all accessible notations
   (whether or not currently in the notation scope stack),
   the most-recently defined delimiting key and the class the notation scope is bound to.
   The display also includes :term:`lonely notations <lonely notation>`.

   .. todo should the command report all delimiting keys?

   Use the :cmd:`Print Visibility` command to display the current notation scope stack.

.. cmd:: Print Scope @scope_name

   Displays all notations defined in the notation scope :n:`@scope_name`.
   It also displays the delimiting key and the class to which the
   scope is bound, if any.

.. _Abbreviations:

Abbreviations
--------------

.. cmd:: Notation @ident {* @ident__parm } := @one_term {? ( {+, @syntax_modifier } ) }
   :name: Notation (abbreviation)

   .. todo: for some reason, Sphinx doesn't complain about a duplicate name if
      :name: is omitted

   Defines an abbreviation :token:`ident` with the parameters :n:`@ident__parm`.

   This command supports the :attr:`local` attribute, which limits the notation to the
   current module.

   Unlike a :cmd:`Notation`, an abbreviation defined with the default locality
   is available (with a fully qualified name) outside the current module even
   when :cmd:`Import` (or one of its variants) has not been used on the current
   :cmd:`Module`.

   An *abbreviation* is a name, possibly applied to arguments, that
   denotes a (presumably) more complex expression. Here are examples:

   .. rocqtop:: none

      Require Import ListDef.
      Set Printing Notations.

   .. rocqtop:: in

      Notation Nlist := (list nat).

   .. rocqtop:: all

      Check 1 :: 2 :: 3 :: nil.

   .. rocqtop:: in

      Notation reflexive R := (forall x, R x x).

   .. rocqtop:: all

      Check forall A:Prop, A <-> A.
      Check reflexive iff.

   .. rocqtop:: in

      Notation Plus1 B := (Nat.add B 1).

   .. rocqtop:: all

      Compute (Plus1 3).

   An abbreviation expects no precedence nor associativity, since it
   is parsed as an usual application. Abbreviations are used as
   much as possible by the Rocq printers unless the modifier ``(only
   parsing)`` is given.

   An abbreviation is bound to an absolute name as an ordinary definition is
   and it also can be referred to by a qualified name.

   Abbreviations are syntactic in the sense that they are bound to
   expressions which are not typed at the time of the definition of the
   abbreviation but at the time they are used. Especially, abbreviations
   can be bound to terms with holes (i.e. with “``_``”). For example:

   .. rocqtop:: none reset

      Set Strict Implicit.
      Set Printing Depth 50.

   .. rocqtop:: in

      Definition explicit_id (A:Set) (a:A) := a.

   .. rocqtop:: in

      Notation id := (explicit_id _).

   .. rocqtop:: all

      Check (id 0).

   Abbreviations disappear when a section is closed. No typing of the
   denoted expression is performed at definition time. Type checking is
   done only at the time of use of the abbreviation.

   Like for notations, if the right-hand side of an abbreviation is a
   partially applied constant, the abbreviation inherits the implicit
   arguments and notation scopes of the constant. As an
   exception, if the right-hand side is just of the form :n:`@@qualid`,
   this conventionally stops the inheritance of implicit arguments.

   Like for notations, it is possible to bind binders in
   abbreviations. Here is an example:

   .. rocqtop:: in reset

      Definition force2 q (P:nat*nat -> Prop) :=
        (forall n', n' >= fst q -> forall p', p' >= snd q -> P q).

      Notation F p P := (force2 p (fun p => P)).
      Check exists x y, F (x,y) (x >= 1 /\ y >= 2).

.. extracted from Gallina chapter

Numbers and strings
-------------------

.. insertprodn number_or_string number_or_string

.. prodn::
   number_or_string ::= @number
   | @string

Numbers and strings have no predefined semantics in the calculus. They are
merely notations that can be bound to objects through the notation mechanism.
Initially, numbers are bound to :n:`nat`, Peano’s representation of natural
numbers (see :ref:`datatypes`).

.. note::

   Negative integers are not at the same level as :n:`@natural`, for this
   would make precedence unnatural.

.. _number-notations:

Number notations
~~~~~~~~~~~~~~~~

.. cmd:: Number Notation @qualid__type @qualid__parse @qualid__print {? ( {+, @number_modifier } ) } : @scope_name

   .. insertprodn number_modifier number_string_via

   .. prodn::
      number_modifier ::= warning after @bignat
      | abstract after @bignat
      | @number_string_via
      number_string_via ::= via @qualid mapping [ {+, {| @qualid => @qualid | [ @qualid ] => @qualid } } ]

   Customizes the way number literals are parsed and printed within the current
   :term:`notation scope`.

      :n:`@qualid__type`
         the name of an inductive type,
         while :n:`@qualid__parse` and :n:`@qualid__print` should be the names of the
         parsing and printing functions, respectively.  The parsing function
         :n:`@qualid__parse` should have one of the following types:

            * :n:`Number.int -> @qualid__type`
            * :n:`Number.int -> option @qualid__type`
            * :n:`Number.uint -> @qualid__type`
            * :n:`Number.uint -> option @qualid__type`
            * :n:`Z -> @qualid__type`
            * :n:`Z -> option @qualid__type`
            * :n:`PrimInt63.pos_neg_int63 -> @qualid__type`
            * :n:`PrimInt63.pos_neg_int63 -> option @qualid__type`
            * :n:`PrimFloat.float -> @qualid__type`
            * :n:`PrimFloat.float -> option @qualid__type`
            * :n:`Number.number -> @qualid__type`
            * :n:`Number.number -> option @qualid__type`

         And the printing function :n:`@qualid__print` should have one of the
         following types:

            * :n:`@qualid__type -> Number.int`
            * :n:`@qualid__type -> option Number.int`
            * :n:`@qualid__type -> Number.uint`
            * :n:`@qualid__type -> option Number.uint`
            * :n:`@qualid__type -> Z`
            * :n:`@qualid__type -> option Z`
            * :n:`@qualid__type -> PrimInt63.pos_neg_int63`
            * :n:`@qualid__type -> option PrimInt63.pos_neg_int63`
            * :n:`@qualid__type -> PrimFloat.float`
            * :n:`@qualid__type -> option PrimFloat.float`
            * :n:`@qualid__type -> Number.number`
            * :n:`@qualid__type -> option Number.number`

         When parsing, the application of the parsing function
         :n:`@qualid__parse` to the number will be fully reduced, and universes
         of the resulting term will be refreshed.

         Note that only fully-reduced ground terms (terms containing only
         function application, constructors, inductive type families,
         sorts, primitive integers, primitive floats, primitive arrays and type
         constants for primitive types) will be considered for printing.

         .. note::
            Instead of an inductive type, :n:`@qualid__type` can be :n:`PrimInt63.int`
            or :n:`PrimFloat.float`,
            in which case :n:`@qualid__print` takes :n:`PrimInt63.int_wrapper`
            or :n:`PrimFloat.float_wrapper` as input
            instead of :n:`PrimInt63.int` or :n:`PrimFloat.float`. See below for an
            :ref:`example <example-number-notation-primitive-int>`.

         .. note::
            When :n:`PrimFloat.float` is used as input type of
            :n:`@qualid__parse`, only numerical values will be parsed
            this way, (no infinities nor NaN). Similarly, printers
            :n:`@qualid__print` with output type :n:`PrimFloat.float`
            or :n:`option PrimFloat.float` are ignored when they return
            non numerical values.

      .. _number-string-via:

      :n:`via @qualid__ind mapping [ {+, @qualid__constant => @qualid__constructor } ]`
         When using this option, :n:`@qualid__type` no
         longer needs to be an inductive type and is instead mapped to the
         inductive type :n:`@qualid__ind` according to the provided
         list of pairs, whose first component :n:`@qualid__constant` is a
         constant of type :n:`@qualid__type`
         (or a function of type :n:`{* _ -> } @qualid__type`) and the second a
         constructor of type :n:`@qualid__ind`. The type
         :n:`@qualid__type` is then replaced by :n:`@qualid__ind` in the
         above parser and printer types.

         When :n:`@qualid__constant` is surrounded by square brackets,
         all the implicit arguments of :n:`@qualid__constant` (whether maximally inserted or not) are ignored
         when translating to :n:`@qualid__constructor` (i.e., before
         applying :n:`@qualid__print`) and replaced with implicit
         argument holes :g:`_` when translating from
         :n:`@qualid__constructor` to :n:`@qualid__constant` (after
         :n:`@qualid__parse`). See below for an :ref:`example <example-number-notation-implicit-args>`.

         .. note::
            The implicit status of the arguments is considered
            only at notation declaration time, any further
            modification of this status has no impact
            on the previously declared notations.

         .. note::
            In case of multiple implicit options (for instance
            :g:`Arguments eq_refl {A}%_type_scope {x}, [_] _`), an
            argument is considered implicit when it is implicit in any of the
            options.

         .. note::
            To use a :token:`sort` as the target type :n:`@qualid__type`, use an :ref:`abbreviation <Abbreviations>`
            as in the :ref:`example below <example-number-notation-non-inductive>`.

      :n:`warning after @bignat`
         displays a warning message about a possible stack
         overflow when calling :n:`@qualid__parse` to parse a literal larger than :n:`@bignat`.

         .. warn:: Stack overflow or segmentation fault happens when working with large numbers in @type (threshold may vary depending on your system limits and on the command executed).

            When a :cmd:`Number Notation` is registered in the current scope
            with :n:`(warning after @bignat)`, this warning is emitted when
            parsing a number greater than or equal to :token:`bignat`.

      :n:`abstract after @bignat`
         returns :n:`(@qualid__parse m)` when parsing a literal
         :n:`m` that's greater than :n:`@bignat` rather than reducing
         it to a normal form.  Here :g:`m` will be a
         :g:`Number.int`, :g:`Number.uint`, :g:`Z` or :g:`Number.number`, depending on the
         type of the parsing function :n:`@qualid__parse`. This allows for a
         more compact representation of literals in types such as :g:`nat`,
         and limits parse failures due to stack overflow.  Note that a
         warning will be emitted when an integer larger than :token:`bignat`
         is parsed.  Note that :n:`(abstract after @bignat)` has no effect
         when :n:`@qualid__parse` lands in an :g:`option` type.

         .. warn:: To avoid stack overflow, large numbers in @type are interpreted as applications of @qualid__parse.

            When a :cmd:`Number Notation` is registered in the current scope
            with :n:`(abstract after @bignat)`, this warning is emitted when
            parsing a number greater than or equal to :token:`bignat`.
            Typically, this indicates that the fully computed representation
            of numbers can be so large that non-tail-recursive OCaml
            functions run out of stack space when trying to walk them.

         .. warn:: The 'abstract after' directive has no effect when the parsing function (@qualid__parse) targets an option type.

            As noted above, the :n:`(abstract after @natural)` directive has no
            effect when :n:`@qualid__parse` lands in an :g:`option` type.

         .. exn:: 'via' and 'abstract' cannot be used together.

            With the :n:`abstract after` option, the parser function
            :n:`@qualid__parse` does not reduce large numbers to a normal form,
            which prevents doing the translation given in the :n:`mapping` list.

   .. exn:: Cannot interpret this number as a value of type @type

     The number notation registered for :token:`type` does not support
     the given number.  This error is given when the interpretation
     function returns :g:`None`, or if the interpretation is registered
     only for integers or non-negative integers, and the given number
     has a fractional or exponent part or is negative.

   .. exn:: overflow in int63 literal @bigint

      The constant's absolute value is too big to fit into a 63-bit integer :n:`PrimInt63.int`.

   .. exn:: @qualid__parse should go from Number.int to @type or (option @type). Instead of Number.int, the types Number.uint or Z or PrimInt63.pos_neg_int63 or PrimFloat.float or Number.number could be used (you may need to require BinNums or Number or PrimInt63 or PrimFloat first).

     The parsing function given to the :cmd:`Number Notation`
     command is not of the right type.

   .. exn:: @qualid__print should go from @type to Number.int or (option Number.int). Instead of Number.int, the types Number.uint or Z or PrimInt63.pos_neg_int63 or Number.number could be used (you may need to require BinNums or Number or PrimInt63 first).


     The printing function given to the :cmd:`Number Notation`
     command is not of the right type.

   .. exn:: Unexpected term @term while parsing a number notation.

     Parsing functions must always return ground terms, made up of
     function application, constructors, inductive type families, sorts and primitive
     integers.  Parsing functions may not return terms containing
     axioms, bare (co)fixpoints, lambdas, etc.

   .. exn:: Unexpected non-option term @term while parsing a number notation.

     Parsing functions expected to return an :g:`option` must always
     return a concrete :g:`Some` or :g:`None` when applied to a
     concrete number expressed as a (hexa)decimal.  They may not return
     opaque constants.

   .. exn:: Multiple 'via' options.

     At most one :g:`via` option can be given.

   .. exn:: Multiple 'warning after' or 'abstract after' options.

     At most one :g:`warning after` or :g:`abstract after` option can be given.

.. _string-notations:

String notations
~~~~~~~~~~~~~~~~

.. cmd:: String Notation @qualid__type @qualid__parse @qualid__print {? ( @number_string_via ) } : @scope_name

   Allows the user to customize how strings are parsed and printed.

      :n:`@qualid__type`
         the name of an inductive type,
         while :n:`@qualid__parse` and :n:`@qualid__print` should be the names of the
         parsing and printing functions, respectively.  The parsing function
         :n:`@qualid__parse` should have one of the following types:

            * :n:`Byte.byte -> @qualid__type`
            * :n:`Byte.byte -> option @qualid__type`
            * :n:`list Byte.byte -> @qualid__type`
            * :n:`list Byte.byte -> option @qualid__type`
            * :n:`PrimString.string -> @qualid__type`
            * :n:`PrimString.string -> option @qualid__type`

         The printing function :n:`@qualid__print` should have one of the
         following types:

            * :n:`@qualid__type -> Byte.byte`
            * :n:`@qualid__type -> option Byte.byte`
            * :n:`@qualid__type -> list Byte.byte`
            * :n:`@qualid__type -> option (list Byte.byte)`
            * :n:`@qualid__type -> PrimString.string`
            * :n:`@qualid__type -> option PrimString.string`

         When parsing, the application of the parsing function
         :n:`@qualid__parse` to the string will be fully reduced, and universes
         of the resulting term will be refreshed.

         Note that only fully-reduced ground terms (terms containing only
         function application, constructors, inductive type families,
         sorts, primitive integers, primitive floats, primitive strings, primitive arrays and type
         constants for primitive types) will be considered for printing.

      :n:`via @qualid__ind mapping [ {+, @qualid__constant => @qualid__constructor } ]`
         works as for :ref:`number notations above <number-string-via>`.

  .. exn:: Cannot interpret this string as a value of type @type

     The string notation registered for :token:`type` does not support
     the given string.  This error is given when the interpretation
     function returns :g:`None`.

   .. exn:: @qualid__parse should go from Byte.byte, (list Byte.byte), or PrimString.string to @type or (option @type).

     The parsing function given to the :cmd:`String Notation`
     command is not of the right type.

   .. exn:: @qualid__print should go from @type to T or (option T), where T is either Byte.byte, (list Byte.byte), or PrimString.string.

     The printing function given to the :cmd:`String Notation`
     command is not of the right type.

   .. exn:: Unexpected term @term while parsing a string notation.

     Parsing functions must always return ground terms, made up of
     function application, constructors, inductive type families, sorts, primitive
     integers and primitive strings.  Parsing functions may not return terms containing
     axioms, bare (co)fixpoints, lambdas, etc.

   .. exn:: Unexpected non-option term @term while parsing a string notation.

     Parsing functions expected to return an :g:`option` must always
     return a concrete :g:`Some` or :g:`None` when applied to a
     concrete string expressed as a decimal.  They may not return
     opaque constants.

.. note::
   Number or string notations for parameterized inductive types can be
   added by declaring an :ref:`abbreviation <Abbreviations>` for the
   inductive which instantiates all parameters. See :ref:`example below <example-string-notation-parameterized-inductive>`.

The following errors apply to both string and number notations:

   .. exn:: @type is not an inductive type.

     String and number notations can only be declared for inductive types.
     Declare string or numeral notations for non-inductive types using :n:`@number_string_via`.

   .. exn:: @qualid was already mapped to @qualid and cannot be remapped to @qualid

      Duplicates are not allowed in the :n:`mapping` list.

   .. exn:: Missing mapping for constructor @qualid

      A mapping should be provided for :n:`@qualid` in the :n:`mapping` list.

   .. warn:: @type was already mapped to @type, mapping it also to @type might yield ill typed terms when using the notation.

      Two pairs in the :n:`mapping` list associate types that might be incompatible.

   .. warn:: Type of @qualid seems incompatible with the type of @qualid. Expected type is: @type instead of @type. This might yield ill typed terms when using the notation.

      A mapping given in the :n:`mapping` list associates a constant with a seemingly incompatible constructor.

   .. exn:: Cannot interpret in @scope_name because @qualid could not be found in the current environment.

     The inductive type used to register the string or number notation is no
     longer available in the environment.  Most likely, this is because
     the notation was declared inside a functor for an
     inductive type inside the functor.  This use case is not currently
     supported.

     Alternatively, you might be trying to use a primitive token
     notation from a plugin which forgot to specify which module you
     must :g:`Require` for access to that notation.

   .. exn:: Syntax error: [prim:reference] expected after 'Notation' (in [vernac:command]).

     The type passed to :cmd:`String Notation` or :cmd:`Number Notation` must be a single qualified
     identifier.

   .. exn:: Syntax error: [prim:reference] expected after [prim:reference] (in [vernac:command]).

     Both functions passed to :cmd:`String Notation` or :cmd:`Number Notation` must be single qualified
     identifiers.

     .. todo: generally we don't document syntax errors.  Is this a good execption?

   .. exn:: @qualid is bound to a notation that does not denote a reference.

     Identifiers passed to :cmd:`String Notation` or :cmd:`Number Notation` must be global
     references, or notations which evaluate to single qualified identifiers.

     .. todo note on "single qualified identifiers" https://github.com/coq/coq/pull/11718#discussion_r415076703

.. example:: Number Notation for radix 3

   The following example parses and prints natural numbers
   whose digits are :g:`0`, :g:`1` or :g:`2` as terms of the following
   inductive type encoding radix 3 numbers.

   .. rocqtop:: in reset

      Inductive radix3 : Set :=
        | x0 : radix3
        | x3 : radix3 -> radix3
        | x3p1 : radix3 -> radix3
        | x3p2 : radix3 -> radix3.

   We first define a parsing function

   .. rocqtop:: in

      Definition of_uint_dec (u : Decimal.uint) : option radix3 :=
        let fix f u := match u with
          | Decimal.Nil => Some x0
          | Decimal.D0 u => match f u with Some u => Some (x3 u) | None => None end
          | Decimal.D1 u => match f u with Some u => Some (x3p1 u) | None => None end
          | Decimal.D2 u => match f u with Some u => Some (x3p2 u) | None => None end
          | _ => None end in
        f (Decimal.rev u).
      Definition of_uint (u : Number.uint) : option radix3 :=
        match u with Number.UIntDecimal u => of_uint_dec u | Number.UIntHexadecimal _ => None end.

   and a printing function

   .. rocqtop:: in

      Definition to_uint_dec (x : radix3) : Decimal.uint :=
        let fix f x := match x with
          | x0 => Decimal.Nil
          | x3 x => Decimal.D0 (f x)
          | x3p1 x => Decimal.D1 (f x)
          | x3p2 x => Decimal.D2 (f x) end in
        Decimal.rev (f x).
      Definition to_uint (x : radix3) : Number.uint := Number.UIntDecimal (to_uint_dec x).

   before declaring the notation

   .. rocqtop:: in

      Declare Scope radix3_scope.
      Open Scope radix3_scope.
      Number Notation radix3 of_uint to_uint : radix3_scope.

   We can check the printer

   .. rocqtop:: all

      Check x3p2 (x3p1 x0).

   and the parser

   .. rocqtop:: all

      Set Printing All.
      Check 120.

   Digits other than :g:`0`, :g:`1` and :g:`2` are rejected.

   .. rocqtop:: all fail

      Check 3.

.. _example-number-notation-primitive-int:

.. example:: Number Notation for primitive integers

   This shows the use of the primitive
   integers :n:`PrimInt63.int` as :n:`@qualid__type`. It is the way
   parsing and printing of primitive integers are actually implemented
   in `PrimInt63.v`.

   .. rocqtop:: in reset

      Require Import PrimInt63.
      Definition parser (x : pos_neg_int63) : option int :=
        match x with Pos p => Some p | Neg _ => None end.
      Definition printer (x : int_wrapper) : pos_neg_int63 := Pos (int_wrap x).
      Number Notation int parser printer : uint63_scope.

.. _example-number-notation-non-inductive:

.. example:: Number Notation for a non-inductive type

   The following example encodes the terms in the form :g:`sum unit ( ... (sum unit unit) ... )`
   as the number of units in the term. For instance :g:`sum unit (sum unit unit)`
   is encoded as :g:`3` while :g:`unit` is :g:`1` and :g:`0` stands for :g:`Empty_set`.
   The inductive :g:`I` will be used as :n:`@qualid__ind`.

   .. rocqtop:: in reset

      Inductive I := Iempty : I | Iunit : I | Isum : I -> I -> I.

   We then define :n:`@qualid__parse` and :n:`@qualid__print`

   .. rocqtop:: in

      Definition of_uint (x : Number.uint) : I :=
        let fix f n := match n with
          | O => Iempty | S O => Iunit
          | S n => Isum Iunit (f n) end in
        f (Nat.of_num_uint x).

      Definition to_uint (x : I) : Number.uint :=
        let fix f i := match i with
          | Iempty => O | Iunit => 1
          | Isum i1 i2 => f i1 + f i2 end in
        Nat.to_num_uint (f x).

      Inductive sum (A : Set) (B : Set) : Set := pair : A -> B -> sum A B.

   the number notation itself

   .. rocqtop:: in

      Notation nSet := Set (only parsing).
      Number Notation nSet of_uint to_uint (via I
        mapping [Empty_set => Iempty, unit => Iunit, sum => Isum]) : type_scope.

   and check the printer

   .. rocqtop:: all

      Local Open Scope type_scope.
      Check sum unit (sum unit unit).

   and the parser

   .. rocqtop:: all

      Set Printing All.
      Check 3.

.. _example-number-notation-implicit-args:

.. example:: Number Notation with implicit arguments

   The following example parses and prints natural numbers between
   :g:`0` and :g:`n-1` as terms of type :g:`Fin.t n`.

   .. rocqtop:: all reset warn

      Module Fin.
      Inductive t : nat -> Set :=  F1 : forall n, t (S n) | FS : forall n, t n -> t (S n).
      End Fin.
      Arguments Fin.F1 {_}.
      Arguments Fin.FS {_}.

   Note the implicit arguments of :g:`Fin.F1` and :g:`Fin.FS`,
   which won't appear in the corresponding inductive type.

   .. rocqtop:: in

      Inductive I := I1 : I | IS : I -> I.

      Definition of_uint (x : Number.uint) : I :=
        let fix f n := match n with O => I1 | S n => IS (f n) end in
        f (Nat.of_num_uint x).

      Definition to_uint (x : I) : Number.uint :=
        let fix f i := match i with I1 => O | IS n => S (f n) end in
        Nat.to_num_uint (f x).

      Declare Scope fin_scope.
      Delimit Scope fin_scope with fin.
      Local Open Scope fin_scope.
      Number Notation Fin.t of_uint to_uint (via I
        mapping [[Fin.F1] => I1, [Fin.FS] => IS]) : fin_scope.

   Now :g:`2` is parsed as :g:`Fin.FS (Fin.FS Fin.F1)`, that is
   :g:`@Fin.FS _ (@Fin.FS _ (@Fin.F1 _))`.

   .. rocqtop:: all

      Check 2.

   which can be of type :g:`Fin.t 3` (numbers :g:`0`, :g:`1` and :g:`2`)

   .. rocqtop:: all

      Check 2 : Fin.t 3.

   but cannot be of type :g:`Fin.t 2` (only :g:`0` and :g:`1`)

   .. rocqtop:: all fail

      Check 2 : Fin.t 2.

.. _example-string-notation-parameterized-inductive:

.. example:: String Notation with a parameterized inductive type

   The parameter :g:`Byte.byte` for the parameterized inductive type
   :g:`list` is given through an :ref:`abbreviation <Abbreviations>`.

   .. rocqtop:: in reset

      Notation string := (list Byte.byte) (only parsing).
      Definition id_string := @id string.

      String Notation string id_string id_string : list_scope.

   .. rocqtop:: all

      Check "abc"%list.

.. _TacticNotation:

Tactic Notations
-----------------

Tactic notations allow customizing the syntax of tactics.

.. todo move to the Ltac chapter

.. todo to discuss after moving to the ltac chapter:
   any words of wisdom on when to use tactic notation vs ltac?
   can you run into problems if you shadow another tactic or tactic notation?
   If so, how to avoid ambiguity?

.. cmd:: Tactic Notation {? ( at level @natural ) } {+ @ltac_production_item } := @ltac_expr

   .. insertprodn ltac_production_item ltac_production_item

   .. prodn::
      ltac_production_item ::= @string
      | @ident {? ( @ident {? , @string } ) }

   Defines a *tactic notation*, which extends the parsing and pretty-printing of tactics.

   This command supports the :attr:`local` attribute, which limits the notation to the
   current module.

      :token:`natural`
         The parsing precedence to assign to the notation.  This information is particularly
         relevant for notations for tacticals.  Levels can be in the range 0 .. 5 (default is 5).

      :n:`{+ @ltac_production_item }`
         The notation syntax.  Notations for simple tactics should begin with a :token:`string`.
         Note that `Tactic Notation foo := idtac` is not valid; it should be `Tactic Notation "foo" := idtac`.

         .. todo: "Tactic Notation constr := idtac" gives a nice message, would be good to show
            that message for the "foo" example above.

      :token:`string`
         represents a literal value in the notation

      :n:`@ident`
         is the name of a grammar nonterminal listed in the table below.  In a few cases,
         to maintain backward compatibility, the name differs from the nonterminal name
         used elsewhere in the documentation.

      :n:`( @ident__parm {? , @string__s } )`
         :n:`@ident__parm` is the parameter name associated with :n:`@ident`.   The :n:`@string__s`
         is the separator string to use when :n:`@ident` specifies a list with separators
         (i.e. :n:`@ident` ends with `_list_sep`).

      :n:`@ltac_expr`
         The tactic expression to substitute for the notation.  :n:`@ident__parm`
         tokens appearing in :n:`@ltac_expr` are substituted with the associated
         nonterminal value.

   For example, the following command defines a notation with a single parameter `x`.

   .. rocqtop:: in

      Tactic Notation "destruct_with_eqn" constr(x) := destruct x eqn:?.

   For a complex example, examine the 16 `Tactic Notation "setoid_replace"`\s
   defined in :file:`$ROCQLIB/theories/Classes/SetoidTactics.v`, which are designed
   to accept any subset of 4 optional parameters.

   The nonterminals that can specified in the tactic notation are:

     .. Some missing entries: "ref", "string", "preident", "int" and "ssrpatternarg".
        (from reading .v files).
        Looks like any string passed to "make0" in the code is valid.  But do
        we want to support all these?
        @JasonGross's opinion here: https://github.com/coq/coq/pull/11718#discussion_r415387421

   .. list-table::
      :header-rows: 1

      * -  Specified :token:`ident`
        - Parsed as
        - Interpreted as
        - as in tactic

      * - ``ident``
        - :token:`ident`
        - a user-given name
        - :tacn:`intro`

      * - ``simple_intropattern``
        - :token:`simple_intropattern`
        - an introduction pattern
        - :tacn:`assert` `as`

      * - ``hyp``
        - :token:`ident`
        - a hypothesis defined in context
        - :tacn:`clear`

      * - ``reference``
        - :token:`qualid`
        - a qualified identifier
        - name of an |Ltac|-defined tactic

      * - ``smart_global``
        - :token:`reference`
        - a global reference of term
        - :tacn:`unfold`, :tacn:`with_strategy`

      * - ``constr``
        - :token:`one_term`
        - a term
        - :tacn:`exact`

      * - ``open_constr``
        - :token:`one_term`
        - a term where all `_` which are not resolved by unification become evars; typeclass resolution is not triggered
        - tacn:`epose`, tacn:`eapply`

      * - ``uconstr``
        - :token:`one_term`
        - an untyped term
        - :tacn:`refine`

      * - ``integer``
        - :token:`integer`
        - an integer
        -

      * - ``int_or_var``
        - :token:`int_or_var`
        - an integer
        - :tacn:`do`

      * - ``strategy_level``
        - :token:`strategy_level`
        - a strategy level
        -

      * - ``strategy_level_or_var``
        - :token:`strategy_level_or_var`
        - a strategy level
        - :tacn:`with_strategy`

      * - ``tactic``
        - :token:`ltac_expr`
        - a tactic
        -

      * - ``tactic``\ *n* (*n* in 0..5)
        - :token:`ltac_expr`\ *n*
        - a tactic at level *n*
        -

      * - *entry*\ ``_list``
        - :n:`{* entry }`
        - a list of how *entry* is interpreted
        -

      * - ``ne_``\ *entry*\ ``_list``
        - :n:`{+ entry }`
        - a list of how *entry* is interpreted
        -

      * - *entry*\ ``_list_sep``
        - :n:`{*s entry }`
        - a list of how *entry* is interpreted
        -

      * - ``ne_``\ *entry*\ ``_list_sep``
        - :n:`{+s entry }`
        - a list of how *entry* is interpreted
        -

   .. todo: notation doesn't support italics

   .. note:: In order to be bound in tactic definitions, each
             syntactic entry for argument type must include the case
             of a simple |Ltac| identifier as part of what it
             parses. This is naturally the case for ``ident``,
             ``simple_intropattern``, ``reference``, ``constr``, ...
             but not for ``integer`` nor for ``strategy_level``.  This
             is the reason for introducing special entries
             ``int_or_var`` and ``strategy_level_or_var`` which
             evaluate to integers or strategy levels only,
             respectively, but which syntactically includes
             identifiers in order to be usable in tactic definitions.

   .. note:: The *entry*\ ``_list*`` and ``ne_``\ *entry*\ ``_list*``
             entries can be used in primitive tactics or in other
             notations at places where a list of the underlying entry
             can be used: entry is either ``constr``, ``hyp``,
             ``integer``, ``reference``, ``strategy_level``,
             ``strategy_level_or_var``, or ``int_or_var``.

.. rubric:: Footnotes

.. [#and_or_levels] which are the levels effectively chosen in the current
   implementation of Rocq

.. [#no_associativity] Rocq accepts notations declared as nonassociative but the parser on
   which Rocq is built, namely Camlp5, currently does not implement ``no associativity`` and
   replaces it with ``left associativity``; hence it is the same for Rocq: ``no associativity``
   is in fact ``left associativity`` for the purposes of parsing
