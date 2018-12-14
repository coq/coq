.. _syntaxextensionsandinterpretationscopes:

Syntax extensions and interpretation scopes
========================================================

In this chapter, we introduce advanced commands to modify the way Coq
parses and prints objects, i.e. the translations between the concrete
and internal representations of terms and commands.

The main commands to provide custom symbolic notations for terms are
:cmd:`Notation` and :cmd:`Infix`; they will be described in the
:ref:`next section <Notations>`. There is also a
variant of :cmd:`Notation` which does not modify the parser; this provides a
form of :ref:`abbreviation <Abbreviations>`. It is
sometimes expected that the same symbolic notation has different meanings in
different contexts; to achieve this form of overloading, |Coq| offers a notion
of :ref:`interpretation scopes <Scopes>`.
The main command to provide custom notations for tactics is :cmd:`Tactic Notation`.

.. coqtop:: none

   Set Printing Depth 50.

.. _Notations:

Notations
---------

Basic notations
~~~~~~~~~~~~~~~

.. cmd:: Notation

   A *notation* is a symbolic expression denoting some term or term
   pattern.

A typical notation is the use of the infix symbol ``/\`` to denote the
logical conjunction (and). Such a notation is declared by

.. coqtop:: in

   Notation "A /\ B" := (and A B).

The expression :g:`(and A B)` is the abbreviated term and the string :g:`"A /\ B"`
(called a *notation*) tells how it is symbolically written.

A notation is always surrounded by double quotes (except when the
abbreviation has the form of an ordinary applicative expression;
see :ref:`Abbreviations`). The notation is composed of *tokens* separated by
spaces. Identifiers in the string (such as ``A`` and ``B``) are the *parameters*
of the notation. Each of them must occur at least once in the denoted term. The
other elements of the string (such as ``/\``) are the *symbols*.

An identifier can be used as a symbol but it must be surrounded by
single quotes to avoid the confusion with a parameter. Similarly,
every symbol of at least 3 characters and starting with a simple quote
must be quoted (then it starts by two single quotes). Here is an
example.

.. coqtop:: in

   Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3).

A notation binds a syntactic expression to a term. Unless the parser
and pretty-printer of Coq already know how to deal with the syntactic
expression (see :ref:`ReservingNotations`), explicit precedences and
associativity rules have to be given.

.. note::

   The right-hand side of a notation is interpreted at the time the notation is
   given. In particular, disambiguation of constants, :ref:`implicit arguments
   <ImplicitArguments>` and other notations are resolved at the
   time of the declaration of the notation.

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
expression is not well-formed and that parentheses are mandatory (this is a “no
associativity”) [#no_associativity]_. We do not know of a special convention of
the associativity of disjunction and conjunction, so let us apply for instance a
right associativity (which is the choice of Coq).

Precedence levels and associativity rules of notations have to be
given between parentheses in a list of modifiers that the :cmd:`Notation`
command understands. Here is how the previous examples refine.

.. coqtop:: in

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

.. coqtop:: in

   Notation "~ x" := (not x) (at level 75, right associativity).

One can also define notations for incomplete terms, with the hole
expected to be inferred during type checking.

.. coqtop:: in

   Notation "x = y" := (@eq _ x y) (at level 70, no associativity).

One can define *closed* notations whose both sides are symbols. In this case,
the default precedence level for the inner sub-expression is 200, and the default
level for the notation itself is 0.

.. coqtop:: in

   Notation "( x , y )" := (@pair _ _ x y).

One can also define notations for binders.

.. coqtop:: in

   Notation "{ x : A | P }" := (sig A (fun x => P)).

In the last case though, there is a conflict with the notation for
type casts. The notation for types casts, as shown by the command :cmd:`Print
Grammar constr` is at level 100. To avoid ``x : A`` being parsed as a type cast,
it is necessary to put ``x`` at a level below 100, typically 99. Hence, a correct
definition is the following:

.. coqtop:: all

   Notation "{ x : A | P }" := (sig A (fun x => P)) (x at level 99).

More generally, it is required that notations are explicitly factorized on the
left. See the next section for more about factorization.

Simple factorization rules
~~~~~~~~~~~~~~~~~~~~~~~~~~

Coq extensible parsing is performed by *Camlp5* which is essentially a LL1
parser: it decides which notation to parse by looking at tokens from left to right.
Hence, some care has to be taken not to hide already existing rules by new
rules. Some simple left factorization work has to be done. Here is an example.

.. coqtop:: all

   Notation "x < y" := (lt x y) (at level 70).
   Notation "x < y < z" := (x < y /\ y < z) (at level 70).

In order to factorize the left part of the rules, the subexpression
referred to by ``y`` has to be at the same level in both rules. However the
default behavior puts ``y`` at the next level below 70 in the first rule
(``no associativity`` is the default), and at level 200 in the second
rule (``level 200`` is the default for inner expressions). To fix this, we
need to force the parsing level of ``y``, as follows.

.. coqtop:: in

   Notation "x < y" := (lt x y) (at level 70).
   Notation "x < y < z" := (x < y /\ y < z) (at level 70, y at next level).

For the sake of factorization with Coq predefined rules, simple rules
have to be observed for notations starting with a symbol, e.g., rules
starting with “\ ``{``\ ” or “\ ``(``\ ” should be put at level 0. The list
of Coq predefined notations can be found in the chapter on :ref:`thecoqlibrary`.

.. cmd:: Print Grammar constr.

   This command displays the current state of the Coq term parser.

.. cmd:: Print Grammar pattern.

   This displays the state of the subparser of patterns (the parser used in the
   grammar of the ``match with`` constructions).


Displaying symbolic notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The command :cmd:`Notation` has an effect both on the Coq parser and on the
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
  translated into horizontal-or-else-vertical printing boxes; if the
  content of the box does not fit on a single line, then every breaking
  point forces a newline and an extra indentation of the number of
  spaces given after the “ ``[``” is applied at the beginning of each
  newline (3 spaces in the example)

- well-bracketed pairs of tokens of the form ``'[v '`` and ``']'`` are
  translated into vertical printing boxes; every breaking point forces a
  newline, even if the line is large enough to display the whole content
  of the box, and an extra indentation of the number of spaces given
  after the “``[``” is applied at the beginning of each newline

Notations disappear when a section is closed. No typing of the denoted
expression is performed at definition time. Type checking is done only
at the time of use of the notation.

.. note:: Sometimes, a notation is expected only for the parser. To do
          so, the option ``only parsing`` is allowed in the list of modifiers
          of :cmd:`Notation`. Conversely, the ``only printing`` modifier can be
          used to declare that a notation should only be used for printing and
          should not declare a parsing rule. In particular, such notations do
          not modify the parser.

The Infix command
~~~~~~~~~~~~~~~~~~

The :cmd:`Infix` command is a shortening for declaring notations of infix
symbols.

.. cmd:: Infix "@symbol" := @term ({+, @modifier}).

   This command is equivalent to

       :n:`Notation "x @symbol y" := (@term x y) ({+, @modifier}).`

   where ``x`` and ``y`` are fresh names. Here is an example.

   .. coqtop:: in

      Infix "/\" := and (at level 80, right associativity).

.. _ReservingNotations:

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

.. note:: The notations mentioned in the module :ref:`init-notations` are reserved. Hence
          their precedence and associativity cannot be changed.

Simultaneous definition of terms and notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thanks to reserved notations, the inductive, co-inductive, record, recursive and
corecursive definitions can benefit from customized notations. To do this, insert
a ``where`` notation clause after the definition of the (co)inductive type or
(co)recursive term (or after the definition of each of them in case of mutual
definitions). The exact syntax is given by :token:`decl_notation` for inductive,
co-inductive, recursive and corecursive definitions and in :ref:`record-types`
for records. Here are examples:

.. coqtop:: in

   Reserved Notation "A & B" (at level 80).

.. coqtop:: in

   Inductive and' (A B : Prop) : Prop := conj' : A -> B -> A & B
   where "A & B" := (and' A B).

.. coqtop:: in

   Fixpoint plus (n m : nat) {struct n} : nat :=
   match n with
       | O => m
       | S p => S (p+m)
   end
   where "n + m" := (plus n m).

Displaying information about notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. flag:: Printing Notations

   Controls whether to use notations for printing terms wherever possible.
   Default is on.

.. seealso::

   :flag:`Printing All`
      To disable other elements in addition to notations.

.. _locating-notations:

Locating notations
~~~~~~~~~~~~~~~~~~

To know to which notations a given symbol belongs to, use the :cmd:`Locate`
command. You can call it on any (composite) symbol surrounded by double quotes.
To locate a particular notation, use a string where the variables of the
notation are replaced by “``_``” and where possible single quotes inserted around
identifiers or tokens starting with a single quote are dropped.

.. coqtop:: all

   Locate "exists".
   Locate "exists _ .. _ , _".

Notations and binders
~~~~~~~~~~~~~~~~~~~~~

Notations can include binders. This section lists
different ways to deal with binders. For further examples, see also
:ref:`RecursiveNotationsWithBinders`.

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
defined so that any :n:`@pattern` can be used in place of the
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
terms (see :ref:`init-notations`).

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
constant :g:`sumbool` (see :ref:`specification`).

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
``as pattern`` modifiers, the default is to consider sub-expressions occurring
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

.. _RecursiveNotations:

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

In the example above, the iterator :math:`φ([~]_E , [~]_I)` is :math:`cons [~]_E [~]_I`
and the terminating expression is ``nil``. Here are other examples:

.. coqtop:: in

   Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).

   Notation "[| t * ( x , y , .. , z ) ; ( a , b , .. , c )  * u |]" :=
     (pair (pair .. (pair (pair t x) (pair t y)) .. (pair t z))
           (pair .. (pair (pair a u) (pair b u)) .. (pair c u)))
     (t at level 39).

Notations with recursive patterns can be reserved like standard
notations, they can also be declared within
:ref:`interpretation scopes <Scopes>`.

.. _RecursiveNotationsWithBinders:

Notations with recursive patterns involving binders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Recursive notations can also be used with binders. The basic example
is:

.. coqtop:: in

   Notation "'exists' x .. y , p" :=
     (ex (fun x => .. (ex (fun y => p)) ..))
     (at level 200, x binder, y binder, right associativity).

The principle is the same as in :ref:`RecursiveNotations`
except that in the iterator
:math:`φ([~]_E , [~]_I)`, the placeholder :math:`[~]_E` can also occur in
position of the binding variable of a ``fun`` or a ``forall``.

To specify that the part “``x .. y``” of the notation parses a sequence of
binders, ``x`` and ``y`` must be marked as ``binder`` in the list of modifiers
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
already seen in :ref:`NotationsWithBinders`, even when the
corresponding expression is not used as a binder in the right-hand
side. E.g.:

.. coqtop:: in

   Notation "'apply_id' f a1 .. an" := (.. (f a1) .. an)
     (at level 10, f ident, a1, an at level 9).

.. _custom-entries:

Custom entries
~~~~~~~~~~~~~~

.. cmd:: Declare Custom Entry @ident

   This command allows to define new grammar entries, called *custom
   entries*, that can later be referred to using the entry name
   :n:`custom @ident`.

.. example::

   For instance, we may want to define an ad hoc
   parser for arithmetical operations and proceed as follows:

   .. coqtop:: all

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
left to be inferred by Coq when using :n:`in custom @ident`. The
level is otherwise given explicitly by using the syntax
:n:`in custom @ident at level @num`, where :n:`@num` refers to the level.

Levels are cumulative: a notation at level ``n`` of which the left end
is a term shall use rules at level less than ``n`` to parse this
sub-term. More precisely, it shall use rules at level strictly less
than ``n`` if the rule is declared with ``right associativity`` and
rules at level less or equal than ``n`` if the rule is declared with
``left associativity``. Similarly, a notation at level ``n`` of which
the right end is a term shall use by default rules at level strictly
less than ``n`` to parse this sub-term if the rule is declared left
associative and rules at level less or equal than ``n`` if the rule is
declared right associative. This is what happens for instance in the
rule

.. coqtop:: in

   Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).

where ``x`` is any expression parsed in entry
``expr`` at level less or equal than ``2`` (including, recursively,
the given rule) and ``y`` is any expression parsed in entry ``expr``
at level strictly less than ``2``.

Rules associated to an entry can refer different sub-entries. The
grammar entry name ``constr`` can be used to refer to the main grammar
of term as in the rule

.. coqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

which indicates that the subterm ``x`` should be
parsed using the main grammar. If not indicated, the level is computed
as for notations in ``constr``, e.g. using 200 as default level for
inner sub-expressions. The level can otherwise be indicated explicitly
by using ``constr at level n`` for some ``n``, or ``constr at next
level``.

Conversely, custom entries can be used to parse sub-expressions of the
main grammar, or from another custom entry as is the case in

.. coqtop:: in

   Notation "[ e ]" := e (e custom expr at level 2).

to indicate that ``e`` has to be parsed at level ``2`` of the grammar
associated to the custom entry ``expr``. The level can be omitted, as in

.. coqtop:: in

   Notation "[ e ]" := e (e custom expr)`.

in which case Coq tries to infer it.

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

.. coqtop:: in

   Notation "( x )" := x (in custom expr at level 0, x at level 2).

and

.. coqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

it is used as a *grammar coercion* which means that it is used to parse or
print an expression which is not available in the current grammar at the
current level of parsing or printing for this grammar but which is available
in another grammar or in another level of the current grammar. For instance,

.. coqtop:: in

   Notation "( x )" := x (in custom expr at level 0, x at level 2).

tells that parentheses can be inserted to parse or print an expression
declared at level ``2`` of ``expr`` whenever this expression is
expected to be used as a subterm at level 0 or 1.  This allows for
instance to parse and print :g:`Add x y` as a subterm of :g:`Mul (Add
x y) z` using the syntax ``(x + y) z``. Similarly,

.. coqtop:: in

   Notation "{ x }" := x (in custom expr at level 0, x constr).

gives a way to let any arbitrary expression which is not handled by the
custom entry ``expr`` be parsed or printed by the main grammar of term
up to the insertion of a pair of curly brackets.

.. cmd:: Print Grammar @ident.

   This displays the state of the grammar for terms and grammar for
   patterns associated to the custom entry :token:`ident`.

Summary
~~~~~~~

.. _NotationSyntax:

Syntax of notations
+++++++++++++++++++

The different syntactic forms taken by the commands declaring
notations are given below. The optional :production:`scope` is described in
:ref:`Scopes`.

.. productionlist:: coq
   notation      : [Local] Notation `string` := `term` [`modifiers`] [: `scope`].
                 : | [Local] Infix `string` := `qualid` [`modifiers`] [: `scope`].
                 : | [Local] Reserved Notation `string` [`modifiers`] .
                 : | Inductive `ind_body` [`decl_notation`] with … with `ind_body` [`decl_notation`].
                 : | CoInductive `ind_body` [`decl_notation`] with … with `ind_body` [`decl_notation`].
                 : | Fixpoint `fix_body` [`decl_notation`] with … with `fix_body` [`decl_notation`].
                 : | CoFixpoint `cofix_body` [`decl_notation`] with … with `cofix_body` [`decl_notation`].
                 : | [Local] Declare Custom Entry `ident`.
   decl_notation : [where `string` := `term` [: `scope`] and … and `string` := `term` [: `scope`]].
   modifiers     : at level `num`
                 : in custom `ident`
                 : in custom `ident` at level `num`
                 : | `ident` , … , `ident` at level `num` [`binderinterp`]
                 : | `ident` , … , `ident` at next level [`binderinterp`]
                 : | `ident` `explicit_subentry`
                 : | left associativity
                 : | right associativity
                 : | no associativity
                 : | only parsing
                 : | only printing
                 : | format `string`
   explicit_subentry : ident
                 : | global
                 : | bigint
                 : | [strict] pattern [at level `num`]
                 : | binder
                 : | closed binder
                 : | constr [`binderinterp`]
                 : | constr at level `num` [`binderinterp`]
                 : | constr at next level [`binderinterp`]
                 : | custom [`binderinterp`]
                 : | custom at level `num` [`binderinterp`]
                 : | custom at next level [`binderinterp`]
   binderinterp  : as ident
                 : | as pattern
                 : | as strict pattern

.. note:: No typing of the denoted expression is performed at definition
          time. Type checking is done only at the time of use of the notation.

.. note:: Some examples of Notation may be found in the files composing
          the initial state of Coq (see directory :file:`$COQLIB/theories/Init`).

.. note:: The notation ``"{ x }"`` has a special status in the main grammars of
          terms and patterns so that
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
++++++++++++++++++++++++

Notations disappear when a section is closed.

.. cmd:: Local Notation @notation

   Notations survive modules unless the command ``Local Notation`` is used instead
   of :cmd:`Notation`.

.. cmd:: Local Declare Custom Entry @ident

   Custom entries survive modules unless the command ``Local Declare
   Custom Entry`` is used instead of :cmd:`Declare Custom Entry`.

.. _Scopes:

Interpretation scopes
----------------------

An *interpretation scope* is a set of notations for terms with their
interpretations. Interpretation scopes provide a weak, purely
syntactical form of notation overloading: the same notation, for
instance the infix symbol ``+``, can be used to denote distinct
definitions of the additive operator. Depending on which interpretation
scopes are currently open, the interpretation is different.
Interpretation scopes can include an interpretation for numerals and
strings. However, this is only made possible at the Objective Caml
level.

See :ref:`above <NotationSyntax>` for the syntax of notations including the
possibility to declare them in a given scope. Here is a typical example which
declares the notation for conjunction in the scope ``type_scope``.

.. coqtop:: in

   Notation "A /\ B" := (and A B) : type_scope.

.. note:: A notation not defined in a scope is called a *lonely*
          notation.

Global interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At any time, the interpretation of a notation for a term is done within
a *stack* of interpretation scopes and lonely notations. In case a
notation has several interpretations, the actual interpretation is the
one defined by (or in) the more recently declared (or opened) lonely
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
   but all its invocations.

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

.. _LocalInterpretationRulesForNotations:

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
   :name: Arguments (scopes)

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
   accordingly to the argument scopes bound to this reference.

   .. cmdv:: Arguments @qualid : clear scopes

      This command can be used to clear argument scopes of :token:`qualid`.

   .. cmdv:: Arguments @qualid {+ @name%scope} : extra scopes

      Defines extra argument scopes, to be used in case of coercion to ``Funclass``
      (see the :ref:`implicitcoercions` chapter) or with a computed type.

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

   The command :cmd:`About` can be used to show the scopes bound to the
   arguments of a function.

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
   to this type. When a scope ``scope`` is bound to a type ``type``, any new function
   defined later on gets its arguments of type ``type`` interpreted by default in
   scope scope (this default behavior can however be overwritten by explicitly
   using the command :cmd:`Arguments`).

   Whether the argument of a function has some type ``type`` is determined
   statically. For instance, if ``f`` is a polymorphic function of type
   :g:`forall X:Type, X -> X` and type :g:`t` is bound to a scope ``scope``,
   then :g:`a` of type :g:`t` in :g:`f t a` is not recognized as an argument to
   be interpreted in scope ``scope``.

   More generally, any coercion :n:`@class` (see the :ref:`implicitcoercions` chapter)
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

The ``type_scope`` interpretation scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
  nat. Positive numerals in this scope are mapped to their canonical
  representent built from :g:`O` and :g:`S`. The scope is delimited by the key
  ``nat``, and bound to the type :g:`nat` (see above).

``N_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`N` (binary natural numbers). It is delimited by the key ``N`` and comes
  with an interpretation for numerals as closed terms of type :g:`N`.

``Z_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`Z` (binary integer numbers). It is delimited by the key ``Z`` and comes
  with an interpretation for numerals as closed terms of type :g:`Z`.

``positive_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`positive` (binary strictly positive numbers). It is delimited by
  key ``positive`` and comes with an interpretation for numerals as closed
  terms of type :g:`positive`.

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
  type :g:`R` (axiomatic real numbers). It is delimited by the key ``R`` and comes
  with an interpretation for numerals using the :g:`IZR` morphism from binary
  integer numbers to :g:`R`.

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
  Special characters and escaping follow Coq conventions on strings (see
  :ref:`lexical-conventions`). Especially, there is no convention to visualize non
  printable characters of a string. The file :file:`String.v` shows an example
  that contains quotes, a newline and a beep (i.e. the ASCII character
  of code 7).

``char_scope``
  This scope includes interpretation for all strings of the form ``"c"``
  where :g:`c` is an ASCII character, or of the form ``"nnn"`` where nnn is
  a three-digits number (possibly with leading 0's), or of the form
  ``""""``. Their respective denotations are the ASCII code of :g:`c`, the
  decimal ASCII code ``nnn``, or the ascii code of the character ``"`` (i.e.
  the ASCII code 34), all of them being represented in the type :g:`ascii`.


Displaying information about scopes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: Print Visibility

   This displays the current stack of notations in scopes and lonely
   notations that is used to interpret a notation. The top of the stack
   is displayed last. Notations in scopes whose interpretation is hidden
   by the same notation in a more recently opened scope are not displayed.
   Hence each notation is displayed only once.

   .. cmdv:: Print Visibility @scope

      This displays the current stack of notations in scopes and lonely
      notations assuming that :token:`scope` is pushed on top of the stack. This is
      useful to know how a subterm locally occurring in the scope :token:`scope` is
      interpreted.

.. cmd:: Print Scopes

   This displays all the notations, delimiting keys and corresponding
   classes of all the existing interpretation scopes. It also displays the
   lonely notations.

   .. cmdv:: Print Scope @scope
      :name: Print Scope

      This displays all the notations defined in the interpretation scope :token:`scope`.
      It also displays the delimiting key if any and the class to which the
      scope is bound, if any.

.. _Abbreviations:

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

   An abbreviation is bound to an absolute name as an ordinary definition is
   and it also can be referred to by a qualified name.

   Abbreviations are syntactic in the sense that they are bound to
   expressions which are not typed at the time of the definition of the
   abbreviation but at the time they are used. Especially, abbreviations
   can be bound to terms with holes (i.e. with “``_``”). For example:

   .. coqtop:: none reset

      Set Strict Implicit.
      Set Printing Depth 50.

   .. coqtop:: in

      Definition explicit_id (A:Set) (a:A) := a.

   .. coqtop:: in

      Notation id := (explicit_id _).

   .. coqtop:: all

      Check (id 0).

   Abbreviations disappear when a section is closed. No typing of the
   denoted expression is performed at definition time. Type checking is
   done only at the time of use of the abbreviation.

Numeral notations
-----------------

.. cmd:: Numeral Notation @ident__1 @ident__2 @ident__3 : @scope.
   :name: Numeral Notation

   This command allows the user to customize the way numeral literals
   are parsed and printed.

   The token :n:`@ident__1` should be the name of an inductive type,
   while :n:`@ident__2` and :n:`@ident__3` should be the names of the
   parsing and printing functions, respectively.  The parsing function
   :n:`@ident__2` should have one of the following types:

     * :n:`Decimal.int -> @ident__1`
     * :n:`Decimal.int -> option @ident__1`
     * :n:`Decimal.uint -> @ident__1`
     * :n:`Decimal.uint -> option @ident__1`
     * :n:`Z -> @ident__1`
     * :n:`Z -> option @ident__1`

   And the printing function :n:`@ident__3` should have one of the
   following types:

     * :n:`@ident__1 -> Decimal.int`
     * :n:`@ident__1 -> option Decimal.int`
     * :n:`@ident__1 -> Decimal.uint`
     * :n:`@ident__1 -> option Decimal.uint`
     * :n:`@ident__1 -> Z`
     * :n:`@ident__1 -> option Z`

     When parsing, the application of the parsing function
     :n:`@ident__2` to the number will be fully reduced, and universes
     of the resulting term will be refreshed.

   .. cmdv:: Numeral Notation @ident__1 @ident__2 @ident__3 : @scope (warning after @num).

     When a literal larger than :token:`num` is parsed, a warning
     message about possible stack overflow, resulting from evaluating
     :n:`@ident__2`, will be displayed.

   .. cmdv:: Numeral Notation @ident__1 @ident__2 @ident__3 : @scope (abstract after @num).

     When a literal :g:`m` larger than :token:`num` is parsed, the
     result will be :n:`(@ident__2 m)`, without reduction of this
     application to a normal form.  Here :g:`m` will be a
     :g:`Decimal.int` or :g:`Decimal.uint` or :g:`Z`, depending on the
     type of the parsing function :n:`@ident__2`. This allows for a
     more compact representation of literals in types such as :g:`nat`,
     and limits parse failures due to stack overflow.  Note that a
     warning will be emitted when an integer larger than :token:`num`
     is parsed.  Note that :n:`(abstract after @num)` has no effect
     when :n:`@ident__2` lands in an :g:`option` type.

   .. exn:: Cannot interpret this number as a value of type @type

     The numeral notation registered for :token:`type` does not support
     the given numeral.  This error is given when the interpretation
     function returns :g:`None`, or if the interpretation is registered
     for only non-negative integers, and the given numeral is negative.

   .. exn:: @ident should go from Decimal.int to @type or (option @type). Instead of Decimal.int, the types Decimal.uint or Z could be used{? (require BinNums first)}.

     The parsing function given to the :cmd:`Numeral Notation`
     vernacular is not of the right type.

   .. exn:: @ident should go from @type to Decimal.int or (option Decimal.int).  Instead of Decimal.int, the types Decimal.uint or Z could be used{? (require BinNums first)}.

     The printing function given to the :cmd:`Numeral Notation`
     vernacular is not of the right type.

   .. exn:: @type is not an inductive type.

     Numeral notations can only be declared for inductive types with no
     arguments.

   .. exn:: Unexpected term @term while parsing a numeral notation.

     Parsing functions must always return ground terms, made up of
     applications of constructors and inductive types.  Parsing
     functions may not return terms containing axioms, bare
     (co)fixpoints, lambdas, etc.

   .. exn:: Unexpected non-option term @term while parsing a numeral notation.

     Parsing functions expected to return an :g:`option` must always
     return a concrete :g:`Some` or :g:`None` when applied to a
     concrete numeral expressed as a decimal.  They may not return
     opaque constants.

   .. exn:: Cannot interpret in @scope because @ident could not be found in the current environment.

     The inductive type used to register the numeral notation is no
     longer available in the environment.  Most likely, this is because
     the numeral notation was declared inside a functor for an
     inductive type inside the functor.  This use case is not currently
     supported.

     Alternatively, you might be trying to use a primitive token
     notation from a plugin which forgot to specify which module you
     must :g:`Require` for access to that notation.

   .. exn:: Syntax error: [prim:reference] expected after 'Notation' (in [vernac:command]).

     The type passed to :cmd:`Numeral Notation` must be a single
     identifier.

   .. exn:: Syntax error: [prim:reference] expected after [prim:reference] (in [vernac:command]).

     Both functions passed to :cmd:`Numeral Notation` must be single
     identifiers.

   .. exn:: The reference @ident was not found in the current environment.

     Identifiers passed to :cmd:`Numeral Notation` must exist in the
     global environment.

   .. exn:: @ident is bound to a notation that does not denote a reference.

     Identifiers passed to :cmd:`Numeral Notation` must be global
     references, or notations which denote to single identifiers.

   .. warn:: Stack overflow or segmentation fault happens when working with large numbers in @type (threshold may vary depending on your system limits and on the command executed).

     When a :cmd:`Numeral Notation` is registered in the current scope
     with :n:`(warning after @num)`, this warning is emitted when
     parsing a numeral greater than or equal to :token:`num`.

   .. warn:: To avoid stack overflow, large numbers in @type are interpreted as applications of @ident__2.

     When a :cmd:`Numeral Notation` is registered in the current scope
     with :n:`(abstract after @num)`, this warning is emitted when
     parsing a numeral greater than or equal to :token:`num`.
     Typically, this indicates that the fully computed representation
     of numerals can be so large that non-tail-recursive OCaml
     functions run out of stack space when trying to walk them.

     For example

     .. coqtop:: all

        Check 90000.

   .. warn:: The 'abstract after' directive has no effect when the parsing function (@ident__2) targets an option type.

     As noted above, the :n:`(abstract after @num)` directive has no
     effect when :n:`@ident__2` lands in an :g:`option` type.

.. _TacticNotation:

Tactic Notations
-----------------

Tactic notations allow to customize the syntax of tactics. They have the following syntax:

.. productionlist:: coq
   tacn                 : Tactic Notation [`tactic_level`] [`prod_item` … `prod_item`] := `tactic`.
   prod_item            : `string` | `tactic_argument_type`(`ident`)
   tactic_level         : (at level `num`)
   tactic_argument_type : ident | simple_intropattern | reference
                        : | hyp | hyp_list | ne_hyp_list
                        : | constr | uconstr | constr_list | ne_constr_list
                        : | integer | integer_list | ne_integer_list
                        : | int_or_var | int_or_var_list | ne_int_or_var_list
                        : | tactic | tactic0 | tactic1 | tactic2 | tactic3
                        : | tactic4 | tactic5

.. cmd:: Tactic Notation {? (at level @level)} {+ @prod_item} := @tactic.

   A tactic notation extends the parser and pretty-printer of tactics with a new
   rule made of the list of production items. It then evaluates into the
   tactic expression ``tactic``. For simple tactics, it is recommended to use
   a terminal symbol, i.e. a string, for the first production item. The
   tactic level indicates the parsing precedence of the tactic notation.
   This information is particularly relevant for notations of tacticals.
   Levels 0 to 5 are available (default is 5).

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
        - an intro pattern
        - intros

      * - ``hyp``
        - identifier
        - a hypothesis defined in context
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
             entry for argument type must include the case of a simple |Ltac|
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

   Tactic notations disappear when a section is closed. They survive when
   a module is closed unless the command ``Local Tactic Notation`` is used instead
   of :cmd:`Tactic Notation`.

.. rubric:: Footnotes

.. [#and_or_levels] which are the levels effectively chosen in the current
   implementation of Coq

.. [#no_associativity] Coq accepts notations declared as nonassociative but the parser on
   which Coq is built, namely Camlp5, currently does not implement ``no associativity`` and
   replaces it with ``left associativity``; hence it is the same for Coq: ``no associativity``
   is in fact ``left associativity`` for the purposes of parsing
