.. include:: ../replaces.rst

.. _syntaxextensionsandinterpretationscopes:

Syntax extensions and interpretation scopes
========================================================

In this chapter, we introduce advanced commands to modify the way Coq
parses and prints objects, i.e. the translations between the concrete
and internal representations of terms and commands.

The main commands to provide custom symbolic notations for terms are
``Notation`` and ``Infix``. They are described in section 12.1. There is also a
variant of ``Notation`` which does not modify the parser. This provides with a
form of abbreviation and it is described in Section :ref:`Abbreviations`. It is
sometimes expected that the same symbolic notation has different meanings in
different contexts. To achieve this form of overloading, |Coq| offers a notion
of interpretation scope. This is described in Section :ref:`scopes`.

The main command to provide custom notations for tactics is ``Tactic Notation``.
It is described in Section :ref:`TacticNotation`.

.. coqtop:: none

   Set Printing Depth 50.

Notations
---------

Basic notations
~~~~~~~~~~~~~~~

A *notation* is a symbolic expression denoting some term or term
pattern.

A typical notation is the use of the infix symbol ``/\`` to denote the
logical conjunction (and). Such a notation is declared by

.. coqtop:: in

   Notation "A /\ B" := (and A B).

The expression :g:`(and A B)` is the abbreviated term and the string ``"A /\ B"``
(called a *notation*) tells how it is symbolically written.

A notation is always surrounded by double quotes (except when the
abbreviation has the form of an ordinary applicative expression;
see :ref:`Abbreviations`). The notation is composed of *tokens* separated by
spaces. Identifiers in the string (such as ``A`` and ``B``) are the *parameters*
of the notation. They must occur at least once each in the denoted term. The
other elements of the string (such as ``/\``) are the *symbols*.

An identifier can be used as a symbol but it must be surrounded by
simple quotes to avoid the confusion with a parameter. Similarly,
every symbol of at least 3 characters and starting with a simple quote
must be quoted (then it starts by two single quotes). Here is an
example.

.. coqtop:: in

   Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3).

A notation binds a syntactic expression to a term. Unless the parser
and pretty-printer of Coq already know how to deal with the syntactic
expression (see 12.1.7), explicit precedences and associativity rules
have to be given.

.. note::

   The right-hand side of a notation is interpreted at the time the notation is
   given. In particular, disambiguiation of constants, implicit arguments (see
   Section :ref:`ImplicitArguments`), coercions (see Section :ref:`Coercions`),
   etc. are resolved at the time of the declaration of the notation.

Precedences and associativity
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Mixing different symbolic notations in the same text may cause serious
parsing ambiguity. To deal with the ambiguity of notations, Coq uses
precedence levels ranging from 0 to 100 (plus one extra level numbered
200) and associativity rules.

Consider for example the new notation

.. coqtop:: in

   Notation "A \/ B" := (or A B).

Clearly, an expression such as :g:`forall A:Prop, True /\ A \/ A \/ False`
is ambiguous. To tell the Coq parser how to interpret the
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
expression is not well- formed and that parentheses are mandatory (this is a “no
associativity”) [#no_associativity]_. We do not know of a special convention of
the associativity of disjunction and conjunction, so let us apply for instance a
right associativity (which is the choice of Coq).

Precedence levels and associativity rules of notations have to be
given between parentheses in a list of modifiers that the ``Notation``
command understands. Here is how the previous examples refine.

.. coqtop:: in

   Notation "A /\ B" := (and A B) (at level 80, right associativity).
   Notation "A \/ B" := (or A B) (at level 85, right associativity).

By default, a notation is considered non associative, but the
precedence level is mandatory (except for special cases whose level is
canonical). The level is either a number or the phrase `next level`
whose meaning is obvious. The list of levels already assigned is on
Figure 3.1.

.. TODO I don't find it obvious -- CPC

Complex notations
~~~~~~~~~~~~~~~~~

Notations can be made from arbitrarily complex symbols. One can for
instance define prefix notations.

.. coqtop:: in

   Notation "~ x" := (not x) (at level 75, right associativity).

One can also define notations for incomplete terms, with the hole
expected to be inferred at typing time.

.. coqtop:: in

   Notation "x = y" := (@eq _ x y) (at level 70, no associativity).

One can define *closed* notations whose both sides are symbols. In this case,
the default precedence level for the inner subexpression is 200, and the default
level for the notation itself is 0.

.. coqtop:: in

   Notation "( x , y )" := (@pair _ _ x y).

One can also define notations for binders.

.. coqtop:: in

   Notation "{ x : A | P }" := (sig A (fun x => P)).

In the last case though, there is a conflict with the notation for
type casts. The notation for types casts, as shown by the command :cmd:`Print
Grammar constr` is at level 100. To avoid ``x : A`` being parsed as a type cast,
it is necessary to put x at a level below 100, typically 99. Hence, a correct
definition is the following:

.. coqtop:: all

   Notation "{ x : A | P }" := (sig A (fun x => P)) (x at level 99).

More generally, it is required that notations are explicitly factorized on the
left. See the next section for more about factorization.

Simple factorization rules
~~~~~~~~~~~~~~~~~~~~~~~~~~

Coq extensible parsing is performed by *Camlp5* which is essentially a LL1
parser: it decides which notation to parse by looking tokens from left to right.
Hence, some care has to be taken not to hide already existing rules by new
rules. Some simple left factorization work has to be done. Here is an example.

.. coqtop:: all

   Notation "x < y" := (lt x y) (at level 70).
   Notation "x < y < z" := (x < y /\ y < z) (at level 70).

In order to factorize the left part of the rules, the subexpression
referred by y has to be at the same level in both rules. However the
default behavior puts y at the next level below 70 in the first rule
(no associativity is the default), and at the level 200 in the second
rule (level 200 is the default for inner expressions). To fix this, we
need to force the parsing level of y, as follows.

.. coqtop:: all

   Notation "x < y" := (lt x y) (at level 70).
   Notation "x < y < z" := (x < y /\ y < z) (at level 70, y at next level).

For the sake of factorization with Coq predefined rules, simple rules
have to be observed for notations starting with a symbol: e.g. rules
starting with “{” or “(” should be put at level 0. The list of Coq
predefined notations can be found in Chapter 3.

.. cmd:: Print Grammar constr.

   This command displays the current state of the Coq term parser.

.. cmd:: Print Grammar pattern.

   This displays the state of the subparser of patterns (the parser used in the
   grammar of the match with constructions).


Displaying symbolic notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The command ``Notation`` has an effect both on the Coq parser and on the
Coq printer. For example:

.. coqtop:: all

   Check (and True True).

However, printing, especially pretty-printing, also requires some
care. We may want specific indentations, line breaks, alignment if on
several lines, etc. For pretty-printing, |Coq| relies on |ocaml|
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
the printer. Here is an example showing how to add spaces around the
bar of the notation.

.. coqtop:: in

   Notation "{{ x : A | P }}" := (sig (fun x : A => P)) (at level 0, x at level 99).

.. coqtop:: all

   Check (sig (fun x : nat => x=x)).

The second, more powerful control on printing is by using the format
modifier. Here is an example

.. coqtop:: all

   Notation "'If' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
   (at level 200, right associativity, format
   "'[v   ' 'If'  c1 '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'").

.. coqtop:: all

   Check
     (IF_then_else (IF_then_else True False True)
       (IF_then_else True False True)
       (IF_then_else True False True)).

A *format* is an extension of the string denoting the notation with
the possible following elements delimited by single quotes:

- extra spaces are translated into simple spaces

- tokens of the form ``'/ '`` are translated into breaking point, in
  case a line break occurs, an indentation of the number of spaces after
  the “ ``/``” is applied (2 spaces in the given example)

- token of the form ``'//'`` force writing on a new line

- well-bracketed pairs of tokens of the form ``'[ '`` and ``']'`` are
  translated into printing boxes; in case a line break occurs, an extra
  indentation of the number of spaces given after the “ ``[``” is applied
  (4 spaces in the example)

- well-bracketed pairs of tokens of the form ``'[hv '`` and ``']'`` are
  translated into horizontal-orelse-vertical printing boxes; if the
  content of the box does not fit on a single line, then every breaking
  point forces a newline and an extra indentation of the number of
  spaces given after the “ ``[``” is applied at the beginning of each
  newline (3 spaces in the example)

- well-bracketed pairs of tokens of the form ``'[v '`` and ``']'`` are
  translated into vertical printing boxes; every breaking point forces a
  newline, even if the line is large enough to display the whole content
  of the box, and an extra indentation of the number of spaces given
  after the “``[``” is applied at the beginning of each newline

Notations do not survive the end of sections. No typing of the denoted
expression is performed at definition time. Type-checking is done only
at the time of use of the notation.

.. note:: Sometimes, a notation is expected only for the parser. To do
          so, the option ``only parsing`` is allowed in the list of modifiers
          of ``Notation``. Conversely, the ``only printing`` modifier can be
          used to declare that a notation should only be used for printing and
          should not declare a parsing rule. In particular, such notations do
          not modify the parser.

The Infix command
~~~~~~~~~~~~~~~~~~

The ``Infix`` command is a shortening for declaring notations of infix
symbols.

.. cmd:: Infix "@symbol" := @term ({+, @modifier}).

   This command is equivalent to

       :n:`Notation "x @symbol y" := (@term x y) ({+, @modifier}).`

   where ``x`` and ``y`` are fresh names. Here is an example.

   .. coqtop:: in

      Infix "/\" := and (at level 80, right associativity).

Reserving notations
~~~~~~~~~~~~~~~~~~~

A given notation may be used in different contexts. Coq expects all
uses of the notation to be defined at the same precedence and with the
same associativity. To avoid giving the precedence and associativity
every time, it is possible to declare a parsing rule in advance
without giving its interpretation. Here is an example from the initial
state of Coq.

.. coqtop:: in

   Reserved Notation "x = y" (at level 70, no associativity).

Reserving a notation is also useful for simultaneously defining an
inductive type or a recursive constant and a notation for it.

.. note:: The notations mentioned on Figure 3.1 are reserved. Hence
          their precedence and associativity cannot be changed.

Simultaneous definition of terms and notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thanks to reserved notations, the inductive, co-inductive, record, recursive
and corecursive definitions can benefit of customized notations. To do
this, insert a ``where`` notation clause after the definition of the
(co)inductive type or (co)recursive term (or after the definition of
each of them in case of mutual definitions). The exact syntax is given
on Figure 12.1 for inductive, co-inductive, recursive and corecursive
definitions and on Figure :ref:`record-syntax` for records. Here are examples:

.. coqtop:: in

   Inductive and (A B:Prop) : Prop := conj : A -> B -> A /\ B
   where "A /\ B" := (and A B).

   Fixpoint plus (n m:nat) {struct n} : nat :=
     match n with
     | O => m
     | S p => S (p+m)
     end
   where "n + m" := (plus n m).

Displaying informations about notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. opt:: Printing Notations

   To deactivate the printing of all notations, use the command
   ``Unset Printing Notations``. To reactivate it, use the command
   ``Set Printing Notations``.

   The default is to use notations for printing terms wherever possible.

.. seealso::

   :opt:`Printing All`
      To disable other elements in addition to notations.

Locating notations
~~~~~~~~~~~~~~~~~~

.. cmd:: Locate @symbol

   To know to which notations a given symbol belongs to, use the command
   ``Locate symbol``, where symbol is any (composite) symbol surrounded by double
   quotes. To locate a particular notation, use a string where the variables of the
   notation are replaced by “_” and where possible single quotes inserted around
   identifiers or tokens starting with a single quote are dropped.

   .. coqtop:: all

      Locate "exists".
      Locate "exists _ .. _ , _".

   .. todo:: See also: Section 6.3.10.

Notations and binders
~~~~~~~~~~~~~~~~~~~~~

Notations can include binders. This section lists
different ways to deal with binders. For further examples, see also
Section :ref:`RecursiveNotationsWithBinders`.

Binders bound in the notation and parsed as identifiers
+++++++++++++++++++++++++++++++++++++++++++++++++++++++

Here is the basic example of a notation using a binder:

.. coqtop:: in

   Notation "'sigma' x : A , B" := (sigT (fun x : A => B))
     (at level 200, x ident, A at level 200, right associativity).

The binding variables in the right-hand side that occur as a parameter
of the notation (here :g:`x`) dynamically bind all the occurrences
in their respective binding scope after instantiation of the
parameters of the notation. This means that the term bound to :g:`B` can
refer to the variable name bound to :g:`x` as shown in the following
application of the notation:

.. coqtop:: all

   Check sigma z : nat, z = 0.

Notice the modifier ``x ident`` in the declaration of the
notation. It tells to parse :g:`x` as a single identifier.

Binders bound in the notation and parsed as patterns
++++++++++++++++++++++++++++++++++++++++++++++++++++

In the same way as patterns can be used as binders, as in
:g:`fun '(x,y) => x+y` or :g:`fun '(existT _ x _) => x`, notations can be
defined so that any pattern (in the sense of the entry :n:`@pattern` of
Figure :ref:`term-syntax-aux`) can be used in place of the
binder. Here is an example:

.. coqtop:: in reset

   Notation "'subset' ' p , P " := (sig (fun p => P))
     (at level 200, p pattern, format "'subset'  ' p ,  P").

.. coqtop:: all

   Check subset '(x,y), x+y=0.

The modifier ``p pattern`` in the declaration of the notation tells to parse
:g:`p` as a pattern. Note that a single variable is both an identifier and a
pattern, so, e.g., the following also works:

.. coqtop:: all

   Check subset 'x, x=0.

If one wants to prevent such a notation to be used for printing when the
pattern is reduced to a single identifier, one has to use instead
the modifier ``p strict pattern``. For parsing, however, a
``strict pattern`` will continue to include the case of a
variable. Here is an example showing the difference:

.. coqtop:: in

   Notation "'subset_bis' ' p , P" := (sig (fun p => P))
     (at level 200, p strict pattern).
   Notation "'subset_bis' p , P " := (sig (fun p => P))
     (at level 200, p ident).

.. coqtop:: all

   Check subset_bis 'x, x=0.

The default level for a ``pattern`` is 0. One can use a different level by
using ``pattern at level`` :math:`n` where the scale is the same as the one for
terms (Figure :ref:`init-notations`).

Binders bound in the notation and parsed as terms
+++++++++++++++++++++++++++++++++++++++++++++++++

Sometimes, for the sake of factorization of rules, a binder has to be
parsed as a term. This is typically the case for a notation such as
the following:

.. coqtop:: in

   Notation "{ x : A | P }" := (sig (fun x : A => P))
       (at level 0, x at level 99 as ident).

This is so because the grammar also contains rules starting with :g:`{}` and
followed by a term, such as the rule for the notation :g:`{ A } + { B }` for the
constant :g:`sumbool` (see Section :ref:`sumbool`).

Then, in the rule, ``x ident`` is replaced by ``x at level 99 as ident`` meaning
that ``x`` is parsed as a term at level 99 (as done in the notation for
:g:`sumbool`), but that this term has actually to be an identifier.

The notation :g:`{ x | P }` is already defined in the standard
library with the ``as ident`` modifier. We cannot redefine it but
one can define an alternative notation, say :g:`{ p such that P }`,
using instead ``as pattern``.

.. coqtop:: in

   Notation "{ p 'such' 'that' P }" := (sig (fun p => P))
     (at level 0, p at level 99 as pattern).

Then, the following works:

.. coqtop:: all

   Check {(x,y) such that x+y=0}.

To enforce that the pattern should not be used for printing when it
is just an identifier, one could have said
``p at level 99 as strict pattern``.

Note also that in the absence of a ``as ident``, ``as strict pattern`` or
``as pattern`` modifiers, the default is to consider subexpressions occurring
in binding position and parsed as terms to be ``as ident``.

.. _NotationsWithBinders:

Binders not bound in the notation
+++++++++++++++++++++++++++++++++

We can also have binders in the right-hand side of a notation which
are not themselves bound in the notation. In this case, the binders
are considered up to renaming of the internal binder. E.g., for the
notation

.. coqtop:: in

   Notation "'exists_different' n" := (exists p:nat, p<>n) (at level 200).

the next command fails because p does not bind in the instance of n.

.. coqtop:: all

   Fail Check (exists_different p).

.. coqtop:: in

   Notation "[> a , .. , b <]" :=
     (cons a .. (cons b nil) .., cons b .. (cons a nil) ..).

.. _RecursiveNotationsWithBinders:

Notations with recursive patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A mechanism is provided for declaring elementary notations with
recursive patterns. The basic example is:

.. coqtop:: all

   Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

On the right-hand side, an extra construction of the form ``.. t ..`` can
be used. Notice that ``..`` is part of the Coq syntax and it must not be
confused with the three-dots notation “``…``” used in this manual to denote
a sequence of arbitrary size.

On the left-hand side, the part “``x s .. s y``” of the notation parses
any number of time (but at least one time) a sequence of expressions
separated by the sequence of tokens ``s`` (in the example, ``s`` is just “``;``”).

The right-hand side must contain a subterm of the form either
``φ(x, .. φ(y,t) ..)`` or ``φ(y, .. φ(x,t) ..)`` where :math:`φ([~]_E , [~]_I)`,
called the *iterator* of the recursive notation is an arbitrary expression with
distinguished placeholders and where :math:`t` is called the *terminating
expression* of the recursive notation. In the example, we choose the names
:math:`x` and :math:`y` but in practice they can of course be chosen
arbitrarily. Not atht the placeholder :math:`[~]_I` has to occur only once but
:math:`[~]_E` can occur several times.

Parsing the notation produces a list of expressions which are used to
fill the first placeholder of the iterating pattern which itself is
repeatedly nested as many times as the length of the list, the second
placeholder being the nesting point. In the innermost occurrence of the
nested iterating pattern, the second placeholder is finally filled with the
terminating expression.

In the example above, the iterator :math:`φ([~]_E , [~]_I)` is :math:`cons [~]_E [~]_I`
and the terminating expression is ``nil``. Here are other examples:

.. coqtop:: in

   Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).

   Notation "[| t * ( x , y , .. , z ) ; ( a , b , .. , c )  * u |]" :=
     (pair (pair .. (pair (pair t x) (pair t y)) .. (pair t z))
           (pair .. (pair (pair a u) (pair b u)) .. (pair c u)))
     (t at level 39).

Notations with recursive patterns can be reserved like standard
notations, they can also be declared within interpretation scopes (see
section 12.2).


Notations with recursive patterns involving binders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recursive notations can also be used with binders. The basic example
is:

.. coqtop:: all

   Notation "'exists' x .. y , p" :=
     (ex (fun x => .. (ex (fun y => p)) ..))
     (at level 200, x binder, y binder, right associativity).

The principle is the same as in Section 12.1.12 except that in the iterator
:math:`φ([~]_E , [~]_I)`, the placeholder :math:`[~]_E` can also occur in
position of the binding variable of a ``fun`` or a ``forall``.

To specify that the part “``x .. y``” of the notation parses a sequence of
binders, ``x`` and ``y`` must be marked as ``binder`` in the list of modifiers
of the notation. The binders of the parsed sequence are used to fill the
occurrences of the first placeholder of the iterating pattern which is
repeatedly nested as many times as the number of binders generated. If ever the
generalization operator ``'`` (see Section 2.7.19) is used in the binding list,
the added binders are taken into account too.

Binders parsing exist in two flavors. If ``x`` and ``y`` are marked as binder,
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

.. coqtop:: in

   Notation "'mylet' f x .. y :=  t 'in' u":=
     (let f := fun x => .. (fun y => t) .. in u)
     (at level 200, x closed binder, y closed binder, right associativity).

A recursive pattern for binders can be used in position of a recursive
pattern for terms. Here is an example:

.. coqtop:: in 

   Notation "'FUNAPP' x .. y , f" :=
     (fun x => .. (fun y => (.. (f x) ..) y ) ..)
     (at level 200, x binder, y binder, right associativity).

If an occurrence of the :math:`[~]_E` is not in position of a binding
variable but of a term, it is the name used in the binding which is
used. Here is an example:

.. coqtop:: in

   Notation "'exists_non_null' x .. y  , P" :=
     (ex (fun x => x <> 0 /\ .. (ex (fun y => y <> 0 /\ P)) ..))
     (at level 200, x binder).

Predefined entries
~~~~~~~~~~~~~~~~~~

By default, sub-expressions are parsed as terms and the corresponding
grammar entry is called :n:`@constr`. However, one may sometimes want
to restrict the syntax of terms in a notation. For instance, the
following notation will accept to parse only global reference in
position of :g:`x`:

.. coqtop:: in

   Notation "'apply' f a1 .. an" := (.. (f a1) .. an)
     (at level 10, f global, a1, an at level 9).

In addition to ``global``, one can restrict the syntax of a
sub-expression by using the entry names ``ident`` or ``pattern``
already seen in Section :ref:`NotationsWithBinders`, even when the
corresponding expression is not used as a binder in the right-hand
side. E.g.:

.. coqtop:: in

   Notation "'apply_id' f a1 .. an" := (.. (f a1) .. an)
     (at level 10, f ident, a1, an at level 9).

Summary
~~~~~~~

Syntax of notations
~~~~~~~~~~~~~~~~~~~

The different syntactic variants of the command Notation are given on the
following figure. The optional :token:`scope` is described in the Section 12.2.

.. productionlist:: coq
   notation      : [Local] Notation `string` := `term` [`modifiers`] [: `scope`].
                 : | [Local] Infix `string` := `qualid` [`modifiers`] [: `scope`].
                 : | [Local] Reserved Notation `string` [`modifiers`] .
                 : | Inductive `ind_body` [`decl_notation`] with … with `ind_body` [`decl_notation`].
                 : | CoInductive `ind_body` [`decl_notation`] with … with `ind_body` [`decl_notation`].
                 : | Fixpoint `fix_body` [`decl_notation`] with … with `fix_body` [`decl_notation`].
                 : | CoFixpoint `cofix_body` [`decl_notation`] with … with `cofix_body` [`decl_notation`].
   decl_notation : [where `string` := `term` [: `scope`] and … and `string` := `term` [: `scope`]].
   modifiers     : at level `natural`
                 : | `ident` , … , `ident` at level `natural` [`binderinterp`]
                 : | `ident` , … , `ident` at next level [`binderinterp`]
                 : | `ident` ident
                 : | `ident` global
                 : | `ident` bigint
                 : | `ident` [strict] pattern [at level `natural`]
                 : | `ident` binder
                 : | `ident` closed binder
                 : | left associativity
                 : | right associativity
                 : | no associativity
                 : | only parsing
                 : | only printing
                 : | format `string`
   binderinterp  : as ident
                 : | as pattern
                 : | as strict pattern

.. note:: No typing of the denoted expression is performed at definition
          time. Type-checking is done only at the time of use of the notation.

.. note:: Many examples of Notation may be found in the files composing
          the initial state of Coq (see directory :file:`$COQLIB/theories/Init`).

.. note:: The notation ``"{ x }"`` has a special status in such a way that
          complex notations of the form ``"x + { y }"`` or ``"x * { y }"`` can be
          nested with correct precedences. Especially, every notation involving
          a pattern of the form ``"{ x }"`` is parsed as a notation where the
          pattern ``"{ x }"`` has been simply replaced by ``"x"`` and the curly
          brackets are parsed separately. E.g. ``"y + { z }"`` is not parsed as a
          term of the given form but as a term of the form ``"y + z"`` where ``z``
          has been parsed using the rule parsing ``"{ x }"``. Especially, level
          and precedences for a rule including patterns of the form ``"{ x }"``
          are relative not to the textual notation but to the notation where the
          curly brackets have been removed (e.g. the level and the associativity
          given to some notation, say ``"{ y } & { z }"`` in fact applies to the
          underlying ``"{ x }"``\-free rule which is ``"y & z"``).

Persistence of notations
~~~~~~~~~~~~~~~~~~~~~~~~

Notations do not survive the end of sections.

.. cmd:: Local Notation @notation

   Notations survive modules unless the command ``Local Notation`` is used instead
   of ``Notation``.

Interpretation scopes
----------------------

An *interpretation scope* is a set of notations for terms with their
interpretation. Interpretation scopes provide a weak, purely
syntactical form of notations overloading: the same notation, for
instance the infix symbol ``+`` can be used to denote distinct
definitions of the additive operator. Depending on which interpretation
scopes is currently open, the interpretation is different.
Interpretation scopes can include an interpretation for numerals and
strings. However, this is only made possible at the Objective Caml
level.

See Figure 12.1 for the syntax of notations including the possibility
to declare them in a given scope. Here is a typical example which
declares the notation for conjunction in the scope ``type_scope``.

.. coqdoc::

   Notation "A /\ B" := (and A B) : type_scope.

.. note:: A notation not defined in a scope is called a *lonely*
          notation.

Global interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At any time, the interpretation of a notation for term is done within
a *stack* of interpretation scopes and lonely notations. In case a
notation has several interpretations, the actual interpretation is the
one defined by (or in) the more recently declared (or open) lonely
notation (or interpretation scope) which defines this notation.
Typically if a given notation is defined in some scope ``scope`` but has
also an interpretation not assigned to a scope, then, if ``scope`` is open
before the lonely interpretation is declared, then the lonely
interpretation is used (and this is the case even if the
interpretation of the notation in scope is given after the lonely
interpretation: otherwise said, only the order of lonely
interpretations and opening of scopes matters, and not the declaration
of interpretations within a scope).

The initial state of Coq declares three interpretation scopes and no
lonely notations. These scopes, in opening order, are ``core_scope``,
``type_scope`` and ``nat_scope``.

.. cmd:: Open Scope @scope

   The command to add a scope to the interpretation scope stack is
   :n:`Open Scope @scope`.

.. cmd:: Close Scope @scope

   It is also possible to remove a scope from the interpretation scope
   stack by using the command :n:`Close Scope @scope`.

   Notice that this command does not only cancel the last :n:`Open Scope @scope`
   but all the invocations of it.

.. note:: ``Open Scope`` and ``Close Scope`` do not survive the end of sections
          where they occur. When defined outside of a section, they are exported
          to the modules that import the module where they occur.

.. cmd:: Local Open Scope @scope.
         Local Close Scope @scope.

   These variants are not exported to the modules that import the module where
   they occur, even if outside a section.

.. cmd:: Global Open Scope @scope.
         Global Close Scope @scope.

   These variants survive sections. They behave as if Global were absent when
   not inside a section.

Local interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In addition to the global rules of interpretation of notations, some
ways to change the interpretation of subterms are available.

Local opening of an interpretation scope
+++++++++++++++++++++++++++++++++++++++++

It is possible to locally extend the interpretation scope stack using the syntax
:g:`(term)%key` (or simply :g:`term%key` for atomic terms), where key is a
special identifier called *delimiting key* and bound to a given scope.

In such a situation, the term term, and all its subterms, are
interpreted in the scope stack extended with the scope bound tokey.

.. cmd:: Delimit Scope @scope with @ident

   To bind a delimiting key to a scope, use the command
   :n:`Delimit Scope @scope with @ident`

.. cmd:: Undelimit Scope @scope

   To remove a delimiting key of a scope, use the command
   :n:`Undelimit Scope @scope`

Binding arguments of a constant to an interpretation scope
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. cmd:: Arguments @qualid {+ @name%@scope}

   It is possible to set in advance that some arguments of a given constant have
   to be interpreted in a given scope. The command is
   :n:`Arguments @qualid {+ @name%@scope}` where the list is a prefix of the
   arguments of ``qualid`` eventually annotated with their ``scope``. Grouping
   round parentheses can be used to decorate multiple arguments with the same
   scope. ``scope`` can be either a scope name or its delimiting key. For
   example the following command puts the first two arguments of :g:`plus_fct`
   in the scope delimited by the key ``F`` (``Rfun_scope``) and the last
   argument in the scope delimited by the key ``R`` (``R_scope``).

   .. coqtop:: in

      Arguments plus_fct (f1 f2)%F x%R.

   The ``Arguments`` command accepts scopes decoration to all grouping
   parentheses. In the following example arguments A and B are marked as
   maximally inserted implicit arguments and are put into the type_scope scope.

   .. coqtop:: in

      Arguments respectful {A B}%type (R R')%signature _ _.

   When interpreting a term, if some of the arguments of qualid are built
   from a notation, then this notation is interpreted in the scope stack
   extended by the scope bound (if any) to this argument. The effect of
   the scope is limited to the argument itself. It does not propagate to
   subterms but the subterms that, after interpretation of the notation,
   turn to be themselves arguments of a reference are interpreted
   accordingly to the arguments scopes bound to this reference.

.. cmdv:: Arguments @qualid : clear scopes

   Arguments scopes can be cleared with :n:`Arguments @qualid : clear scopes`.

.. cmdv:: Arguments @qualid {+ @name%scope} : extra scopes

   Defines extra argument scopes, to be used in case of coercion to Funclass
   (see Chapter :ref:`Coercions-full`) or with a computed type.

.. cmdv:: Global Arguments @qualid {+ @name%@scope}

   This behaves like :n:`Arguments qualid {+ @name%@scope}` but survives when a
   section is closed instead of stopping working at section closing. Without the
   ``Global`` modifier, the effect of the command stops when the section it belongs
   to ends.

.. cmdv:: Local Arguments @qualid {+ @name%@scope}

   This behaves like :n:`Arguments @qualid {+ @name%@scope}` but does not
   survive modules and files. Without the ``Local`` modifier, the effect of the
   command is visible from within other modules or files.

.. seealso::

   :cmd:`About @qualid`
     The command to show the scopes bound to the arguments of a
     function is described in Section 2.

.. note::

   In notations, the subterms matching the identifiers of the
   notations are interpreted in the scope in which the identifiers
   occurred at the time of the declaration of the notation. Here is an
   example:

   .. coqtop:: all

      Parameter g : bool -> bool.
      Notation "@@" := true (only parsing) : bool_scope.
      Notation "@@" := false (only parsing): mybool_scope.

      Bind Scope bool_scope with bool.
      Notation "# x #" := (g x) (at level 40).
      Check # @@ #.
      Arguments g _%mybool_scope.
      Check # @@ #.
      Delimit Scope mybool_scope with mybool.
      Check # @@%mybool #.

Binding types of arguments to an interpretation scope
+++++++++++++++++++++++++++++++++++++++++++++++++++++

.. cmd:: Bind Scope @scope with @qualid

   When an interpretation scope is naturally associated to a type (e.g.  the
   scope of operations on the natural numbers), it may be convenient to bind it
   to this type. When a scope ``scope`` is bound to a type type, any new function
   defined later on gets its arguments of type type interpreted by default in
   scope scope (this default behavior can however be overwritten by explicitly
   using the command ``Arguments``).

   Whether the argument of a function has some type ``type`` is determined
   statically. For instance, if f is a polymorphic function of type :g:`forall
   X:Type, X -> X` and type :g:`t` is bound to a scope ``scope``, then :g:`a` of
   type :g:`t` in :g:`f t a` is not recognized as an argument to be interpreted
   in scope ``scope``.

   More generally, any coercion :n:`@class` (see Chapter :ref:`Coercions-full`)
   can be bound to an interpretation scope. The command to do it is
   :n:`Bind Scope @scope with @class`

   .. coqtop:: in

      Parameter U : Set.
      Bind Scope U_scope with U.
      Parameter Uplus : U -> U -> U.
      Parameter P : forall T:Set, T -> U -> Prop.
      Parameter f : forall T:Set, T -> U.
      Infix "+" := Uplus : U_scope.
      Unset Printing Notations.
      Open Scope nat_scope.

   .. coqtop:: all

      Check (fun x y1 y2 z t => P _ (x + t) ((f _ (y1 + y2) + z))).

   .. note:: The scopes ``type_scope`` and ``function_scope`` also have a local
             effect on interpretation. See the next section.

.. seealso::

   :cmd:`About`
     The command to show the scopes bound to the arguments of a
     function is described in Section 2.

The ``type_scope`` interpretation scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index:: type_scope

The scope ``type_scope`` has a special status. It is a primitive interpretation
scope which is temporarily activated each time a subterm of an expression is
expected to be a type. It is delimited by the key ``type``, and bound to the
coercion class ``Sortclass``. It is also used in certain situations where an
expression is statically known to be a type, including the conclusion and the
type of hypotheses within an Ltac goal match (see Section
:ref:`ltac-match-goal`), the statement of a theorem, the type of a definition,
the type of a binder, the domain and codomain of implication, the codomain of
products, and more generally any type argument of a declared or defined
constant.

The ``function_scope`` interpretation scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index:: function_scope

The scope ``function_scope`` also has a special status. 
It is temporarily activated each time the argument of a global reference is
recognized to be a ``Funclass`` istance, i.e., of type :g:`forall x:A, B` or
:g:`A -> B`.


Interpretation scopes used in the standard library of Coq
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We give an overview of the scopes used in the standard library of Coq.
For a complete list of notations in each scope, use the commands Print
Scopes or Print Scope scope.

``type_scope``
  This scope includes infix * for product types and infix + for sum types. It
  is delimited by key ``type``, and bound to the coercion class 
  ``Sortclass``, as described above.

``function_scope``
  This scope is delimited by key ``function``, and bound to the coercion class 
  ``Funclass``, as described above.

``nat_scope``
  This scope includes the standard arithmetical operators and relations on type
  nat. Positive numerals in this scope are mapped to their canonical
  representent built from :g:`O` and :g:`S`. The scope is delimited by key
  ``nat``, and bound to the type :g:`nat` (see above).

``N_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`N` (binary natural numbers). It is delimited by key ``N`` and comes
  with an interpretation for numerals as closed terms of type :g:`N`.

``Z_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`Z` (binary integer numbers). It is delimited by key ``Z`` and comes
  with an interpretation for numerals as closed term of type :g:`Z`.

``positive_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`positive` (binary strictly positive numbers). It is delimited by
  key ``positive`` and comes with an interpretation for numerals as closed
  term of type :g:`positive`.

``Q_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`Q` (rational numbers defined as fractions of an integer and a
  strictly positive integer modulo the equality of the numerator-
  denominator cross-product). As for numerals, only 0 and 1 have an
  interpretation in scope ``Q_scope`` (their interpretations are 0/1 and 1/1
  respectively).

``Qc_scope``
  This scope includes the standard arithmetical operators and relations on the
  type :g:`Qc` of rational numbers defined as the type of irreducible
  fractions of an integer and a strictly positive integer.

``real_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`R` (axiomatic real numbers). It is delimited by key ``R`` and comes
  with an interpretation for numerals using the :g:`IZR` morphism from binary
  integer numbers to :g:`R`.

``bool_scope``
  This scope includes notations for the boolean operators. It is delimited by
  key ``bool``, and bound to the type :g:`bool` (see above).

``list_scope``
  This scope includes notations for the list operators. It is delimited by key
  ``list``, and bound to the type :g:`list` (see above).

``core_scope``
  This scope includes the notation for pairs. It is delimited by key ``core``.

``string_scope``
  This scope includes notation for strings as elements of the type string.
  Special characters and escaping follow Coq conventions on strings (see
  Section 1.1). Especially, there is no convention to visualize non
  printable characters of a string. The file :file:`String.v` shows an example
  that contains quotes, a newline and a beep (i.e. the ASCII character
  of code 7).

``char_scope``
  This scope includes interpretation for all strings of the form ``"c"``
  where :g:`c` is an ASCII character, or of the form ``"nnn"`` where nnn is
  a three-digits number (possibly with leading 0's), or of the form
  ``""""``. Their respective denotations are the ASCII code of c, the
  decimal ASCII code nnn, or the ascii code of the character ``"`` (i.e.
  the ASCII code 34), all of them being represented in the type :g:`ascii`.


Displaying informations about scopes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Visibility

   This displays the current stack of notations in scopes and lonely
   notations that is used to interpret a notation. The top of the stack
   is displayed last. Notations in scopes whose interpretation is hidden
   by the same notation in a more recently open scope are not displayed.
   Hence each notation is displayed only once.

.. cmdv:: Print Visibility scope

   This displays the current stack of notations in scopes and lonely
   notations assuming that scope is pushed on top of the stack. This is
   useful to know how a subterm locally occurring in the scope ofscope is
   interpreted.

.. cmdv:: Print Scope scope

   This displays all the notations defined in interpretation scopescope.
   It also displays the delimiting key if any and the class to which the
   scope is bound, if any.

.. cmdv:: Print Scopes

   This displays all the notations, delimiting keys and corresponding
   class of all the existing interpretation scopes. It also displays the
   lonely notations.

Abbreviations
--------------

.. cmd:: {? Local} Notation @ident {+ @ident} := @term {? (only parsing)}.

   An *abbreviation* is a name, possibly applied to arguments, that
   denotes a (presumably) more complex expression. Here are examples:

   .. coqtop:: none

      Require Import List.
      Require Import Relations.
      Set Printing Notations.

   .. coqtop:: in

      Notation Nlist := (list nat).

   .. coqtop:: all

      Check 1 :: 2 :: 3 :: nil.

   .. coqtop:: in

      Notation reflexive R := (forall x, R x x).

   .. coqtop:: all

      Check forall A:Prop, A <-> A.
      Check reflexive iff.

   An abbreviation expects no precedence nor associativity, since it
   is parsed as an usual application. Abbreviations are used as
   much as possible by the Coq printers unless the modifier ``(only
   parsing)`` is given.

   Abbreviations are bound to an absolute name as an ordinary definition
   is, and they can be referred by qualified names too.

   Abbreviations are syntactic in the sense that they are bound to
   expressions which are not typed at the time of the definition of the
   abbreviation but at the time it is used. Especially, abbreviations can
   be bound to terms with holes (i.e. with “``_``”). For example:

   .. coqtop:: none reset

      Set Strict Implicit.
      Set Printing Depth 50.

   .. coqtop:: in

      Definition explicit_id (A:Set) (a:A) := a.
      Notation id := (explicit_id _).

   .. coqtop:: all

      Check (id 0).

   Abbreviations do not survive the end of sections. No typing of the
   denoted expression is performed at definition time. Type-checking is
   done only at the time of use of the abbreviation.

Tactic Notations
-----------------

Tactic notations allow to customize the syntax of the tactics of the
tactic language. Tactic notations obey the following syntax:

.. productionlist:: coq
   tacn                 : [Local] Tactic Notation [`tactic_level`] [`prod_item` … `prod_item`] := `tactic`.
   prod_item            : `string` | `tactic_argument_type`(`ident`)
   tactic_level         : (at level `natural`)
   tactic_argument_type : ident | simple_intropattern | reference
                        : | hyp | hyp_list | ne_hyp_list
                        : | constr | uconstr | constr_list | ne_constr_list
                        : | integer | integer_list | ne_integer_list
                        : | int_or_var | int_or_var_list | ne_int_or_var_list
                        : | tactic | tactic0 | tactic1 | tactic2 | tactic3
                        : | tactic4 | tactic5

.. cmd:: {? Local} Tactic Notation {? (at level @level)} {+ @prod_item} := @tactic.

   A tactic notation extends the parser and pretty-printer of tactics with a new
   rule made of the list of production items. It then evaluates into the
   tactic expression ``tactic``. For simple tactics, it is recommended to use
   a terminal symbol, i.e. a string, for the first production item. The
   tactic level indicates the parsing precedence of the tactic notation.
   This information is particularly relevant for notations of tacticals.
   Levels 0 to 5 are available (default is 0).

   .. cmd:: Print Grammar tactic

      To know the parsing precedences of the existing tacticals, use the command
      ``Print Grammar tactic``.

   Each type of tactic argument has a specific semantic regarding how it
   is parsed and how it is interpreted. The semantic is described in the
   following table. The last command gives examples of tactics which use
   the corresponding kind of argument.

   .. list-table::
      :header-rows: 1

      * - Tactic argument type
        - parsed as
        - interpreted as
        - as in tactic

      * - ``ident``
        - identifier
        - a user-given name
        - intro

      * - ``simple_intropattern``
        - intro_pattern
        - an intro_pattern
        - intros

      * - ``hyp``
        - identifier
        - an hypothesis defined in context
        - clear

      * - ``reference``
        - qualified identifier
        - a global reference of term
        - unfold

      * - ``constr``
        - term
        - a term
        - exact

      * - ``uconstr``
        - term
        - an untyped term
        - refine

      * - ``integer``
        - integer
        - an integer
        -

      * - ``int_or_var``
        - identifier or integer
        - an integer
        - do

      * - ``tactic``
        - tactic at level 5
        - a tactic
        -

      * - ``tacticn``
        - tactic at level n
        - a tactic
        -

      * - *entry*\ ``_list``
        - list of *entry*
        - a list of how *entry* is interpreted
        -

      * - ``ne_``\ *entry*\ ``_list``
        - non-empty list of *entry*
        - a list of how *entry* is interpreted
        -

   .. note:: In order to be bound in tactic definitions, each syntactic
             entry for argument type must include the case of simple L tac
             identifier as part of what it parses. This is naturally the case for
             ``ident``, ``simple_intropattern``, ``reference``, ``constr``, ... but not for ``integer``.
             This is the reason for introducing a special entry ``int_or_var`` which
             evaluates to integers only but which syntactically includes
             identifiers in order to be usable in tactic definitions.

   .. note:: The *entry*\ ``_list`` and ``ne_``\ *entry*\ ``_list`` entries can be used in
             primitive tactics or in other notations at places where a list of the
             underlying entry can be used: entry is either ``constr``, ``hyp``, ``integer``
             or ``int_or_var``.

.. cmdv:: Local Tactic Notation

   Tactic notations do not survive the end of sections. They survive
   modules unless the command Local Tactic Notation is used instead of
   Tactic Notation.

.. rubric:: Footnotes

.. [#and_or_levels] which are the levels effectively chosen in the current
   implementation of Coq

.. [#no_associativity] Coq accepts notations declared as no associative but the parser on
   which Coq is built, namely Camlp4, currently does not implement the
   no-associativity and replaces it by a left associativity; hence it is
   the same for Coq: no-associativity is in fact left associativity
