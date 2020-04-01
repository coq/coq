.. _syntax-extensions-and-notation-scopes:

Syntax extensions and notation scopes
=====================================

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
of :ref:`notation scopes <Scopes>`.
The main command to provide custom notations for tactics is :cmd:`Tactic Notation`.

.. coqtop:: none

   Set Printing Depth 50.

.. _Notations:

Notations
---------


Basic notations
~~~~~~~~~~~~~~~

.. cmd:: Notation @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @scope_name }

   Defines a *notation*, an alternate syntax for entering or displaying
   a specific term or term pattern.

   This command supports the :attr:`local` attribute, which limits its effect to the
   current module.
   If the command is inside a section, its effect is limited to the section.

   Specifying :token:`scope_name` associates the notation with that scope.  Otherwise
   it is a *lonely notation*, that is, not associated with a scope.

   .. todo indentation of this chapter is not consistent with other chapters.  Do we have a standard?

For example, the following definition permits using the infix expression :g:`A /\ B`
to represent :g:`(and A B)`:

.. coqtop:: in

   Notation "A /\ B" := (and A B).

:g:`"A /\ B"` is a *notation*, which tells how to represent the abbreviated term
:g:`(and A B)`.

Notations must be in double quotes, except when the
abbreviation has the form of an ordinary applicative expression;
see :ref:`Abbreviations`. The notation consists of *tokens* separated by
spaces. Alphanumeric strings (such as ``A`` and ``B``) are the *parameters*
of the notation. Each of them must occur at least once in the abbreviated term. The
other elements of the string (such as ``/\``) are the *symbols*.

Substrings enclosed in single quotes are treated as literals.  This is necessary
for substrings that would otherwise be interpreted as :n:`@ident`\s.  Similarly,
every symbol of at least 3 characters and starting with a simple quote
must be quoted (then it starts by two single quotes). Here is an
example.

.. coqtop:: in

   Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3).

A notation binds a syntactic expression to a term. Unless the parser
and pretty-printer of Coq already know how to deal with the syntactic
expression (such as through :cmd:`Reserved Notation` or for notations
that contain only literals), explicit precedences and
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
associativity”) [#no_associativity]_. We do not know of a special convention for
the associativity of disjunction and conjunction, so let us apply
right associativity (which is the choice of Coq).

Precedence levels and associativity rules of notations are specified with a list of
parenthesized :n:`@syntax_modifier`\s.  Here is how the previous examples refine:

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
type casts. The notation for type casts, as shown by the command :cmd:`Print
Grammar` `constr` is at level 100. To avoid ``x : A`` being parsed as a type cast,
it is necessary to put ``x`` at a level below 100, typically 99. Hence, a correct
definition is the following:

.. coqtop:: none

   Reset Initial.

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
   Fail Notation "x < y < z" := (x < y /\ y < z) (at level 70).

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

The second, more powerful control on printing is by using :n:`@syntax_modifier`\s. Here is an example

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

.. note:: Sometimes, a notation is expected only for the parser. To do
          so, the option ``only parsing`` is allowed in the list of :n:`@syntax_modifier`\s
          in :cmd:`Notation`. Conversely, the ``only printing`` :n:`@syntax_modifier` can be
          used to declare that a notation should only be used for printing and
          should not declare a parsing rule. In particular, such notations do
          not modify the parser.

The Infix command
~~~~~~~~~~~~~~~~~~

The :cmd:`Infix` command is a shortcut for declaring notations for infix
symbols.

.. cmd:: Infix @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @scope_name }

   This command is equivalent to

       :n:`Notation "x @string y" := (@one_term x y) {? ( {+, @syntax_modifier } ) } {? : @scope_name }`

   where ``x`` and ``y`` are fresh names and omitting the quotes around :n:`@string`.
   Here is an example:

   .. coqtop:: in

      Infix "/\" := and (at level 80, right associativity).

.. _ReservingNotations:

Reserving notations
~~~~~~~~~~~~~~~~~~~

.. cmd:: Reserved Notation @string {? ( {+, @syntax_modifier } ) }

   A given notation may be used in different contexts. Coq expects all
   uses of the notation to be defined at the same precedence and with the
   same associativity. To avoid giving the precedence and associativity
   every time, this command declares a parsing rule (:token:`string`) in advance
   without giving its interpretation. Here is an example from the initial
   state of Coq.

   .. coqtop:: in

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

Simultaneous definition of terms and notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thanks to reserved notations, inductive, co-inductive, record, recursive and
corecursive definitions can use customized notations. To do this, insert
a :token:`decl_notations` clause after the definition of the (co)inductive type or
(co)recursive term (or after the definition of each of them in case of mutual
definitions). The exact syntax is given by :n:`@decl_notation` for inductive,
co-inductive, recursive and corecursive definitions and in :ref:`record-types`
for records.

   .. insertprodn decl_notations decl_notation

   .. prodn::
      decl_notations ::= where @decl_notation {* and @decl_notation }
      decl_notation ::= @string := @one_term {? ( only parsing ) } {? : @scope_name }

Here are examples:

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

.. flag:: Printing Parentheses

   If on, parentheses are printed even if implied by associativity and precedence
   Default is off.

.. seealso::

   :flag:`Printing All` to disable other elements in addition to notations.


.. cmd:: Print Grammar @ident

   Shows the grammar for the nonterminal :token:`ident`, which must be one of the following:

   - `constr` - for :token:`term`\s
   - `pattern` - for :token:`pattern`\s
   - `tactic` - for currently-defined tactic notations, :token:`tactic`\s and tacticals
     (corresponding to :token:`ltac_expr` in the documentation).
   - `vernac` - for :token:`command`\s

   The first three of these give the precedence and associativity for each construct.
   For example, these lines printed by `Print Grammar tactic` indicates that the `try` construct
   is at level 3 and right-associative.  `SELF` represents the `tactic_expr` nonterminal
   at level 5 (the top level)::

     | "3" RIGHTA
       [ IDENT "try"; SELF

   Note that the productions printed by this command are represented in the form used by
   |Coq|'s parser (coqpp), which differs from how productions are shown in the documentation.

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

Inheritance of the properties of arguments of constants bound to a notation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If the right-hand side of a notation is a partially applied constant,
the notation inherits the implicit arguments (see
:ref:`ImplicitArguments`) and notation scopes (see
:ref:`Scopes`) of the constant. For instance:

.. coqtop:: in reset

   Record R := {dom : Type; op : forall {A}, A -> dom}.
   Notation "# x" := (@op x) (at level 8).

.. coqtop:: all

   Check fun x:R => # x 3.

As an exception, if the right-hand side is just of the form
:n:`@@qualid`, this conventionally stops the inheritance of implicit
arguments (but not of notation scopes).

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

Note the :n:`@syntax_modifier x ident` in the declaration of the
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

The :n:`@syntax_modifier p pattern` in the declaration of the notation tells to parse
:g:`p` as a pattern. Note that a single variable is both an identifier and a
pattern, so, e.g., the following also works:

.. coqtop:: all

   Check subset 'x, x=0.

If one wants to prevent such a notation to be used for printing when the
pattern is reduced to a single identifier, one has to use instead
the :n:`@syntax_modifier p strict pattern`. For parsing, however, a
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

.. coqdoc::

   Notation "{ x : A | P }" := (sig (fun x : A => P))
       (at level 0, x at level 99 as ident).

This is so because the grammar also contains rules starting with :g:`{}` and
followed by a term, such as the rule for the notation :g:`{ A } + { B }` for the
constant :g:`sumbool` (see :ref:`specification`).

Then, in the rule, ``x ident`` is replaced by ``x at level 99 as ident`` meaning
that ``x`` is parsed as a term at level 99 (as done in the notation for
:g:`sumbool`), but that this term has actually to be an identifier.

The notation :g:`{ x | P }` is already defined in the standard
library with the ``as ident`` :n:`@syntax_modifier`. We cannot redefine it but
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
``as pattern`` :n:`@syntax_modifier`\s, the default is to consider sub-expressions occurring
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

Notations with expressions used both as binder and term
+++++++++++++++++++++++++++++++++++++++++++++++++++++++

It is possible to use parameters of the notation both in term and
binding position. Here is an example:

.. coqtop:: in

   Definition force n (P:nat -> Prop) := forall n', n' >= n -> P n'.
   Notation "▢_ n P" := (force n (fun n => P))
     (at level 0, n ident, P at level 9, format "▢_ n  P").

.. coqtop:: all

   Check exists p, ▢_p (p >= 1).

More generally, the parameter can be a pattern, as in the following
variant:

.. coqtop:: in reset

   Definition force2 q (P:nat*nat -> Prop) :=
     (forall n', n' >= fst q -> forall p', p' >= snd q -> P q).

   Notation "▢_ p P" := (force2 p (fun p => P))
     (at level 0, p pattern at level 0, P at level 9, format "▢_ p  P").

.. coqtop:: all

   Check exists x y, ▢_(x,y) (x >= 1 /\ y >= 2).

This support is experimental. For instance, the notation is used for
printing only if the occurrence of the parameter in term position
comes in the right-hand side before the occurrence in binding position.

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

In the example above, the iterator :math:`φ([~]_E , [~]_I)` is :math:`cons [~]_E\, [~]_I`
and the terminating expression is ``nil``. Here are other examples:

.. coqtop:: in

   Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).

   Notation "[| t * ( x , y , .. , z ) ; ( a , b , .. , c )  * u |]" :=
     (pair (pair .. (pair (pair t x) (pair t y)) .. (pair t z))
           (pair .. (pair (pair a u) (pair b u)) .. (pair c u)))
     (t at level 39).

Notations with recursive patterns can be reserved like standard
notations, they can also be declared within
:ref:`notation scopes <Scopes>`.

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
grammar entry is called ``constr``. However, one may sometimes want
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

   Defines new grammar entries, called *custom
   entries*, that can later be referred to using the entry name
   :n:`custom @ident`.

   This command supports the :attr:`local` attribute, which limits the entry to the
   current module.

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
subterm. More precisely, it shall use rules at level strictly less
than ``n`` if the rule is declared with ``right associativity`` and
rules at level less or equal than ``n`` if the rule is declared with
``left associativity``. Similarly, a notation at level ``n`` of which
the right end is a term shall use by default rules at level strictly
less than ``n`` to parse this subterm if the rule is declared left
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

.. coqdoc::

   Notation "[ e ]" := e (e custom expr).

in which case Coq infer it. If the sub-expression is at a border of
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

.. cmd:: Print Custom Grammar @ident
   :name: Print Custom Grammar

   This displays the state of the grammar for terms associated to
   the custom entry :token:`ident`.

.. _NotationSyntax:

Syntax
~~~~~~~

Here are the syntax elements used by the various notation commands.

   .. insertprodn syntax_modifier level

   .. prodn::
      syntax_modifier ::= at level @num
      | in custom @ident {? at level @num }
      | {+, @ident } at @level
      | @ident at @level {? @binder_interp }
      | @ident @explicit_subentry
      | @ident @binder_interp
      | left associativity
      | right associativity
      | no associativity
      | only parsing
      | only printing
      | format @string {? @string }
      explicit_subentry ::= ident
      | global
      | bigint
      | strict pattern {? at level @num }
      | binder
      | closed binder
      | constr {? at @level } {? @binder_interp }
      | custom @ident {? at @level } {? @binder_interp }
      | pattern {? at level @num }
      binder_interp ::= as ident
      | as pattern
      | as strict pattern
      level ::= level @num
      | next level

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

.. note:: Notations such as ``"( p | q )"`` (or starting with ``"( x | "``,
          more generally) are deprecated as they conflict with the syntax for
          nested disjunctive patterns (see :ref:`extendedpatternmatching`),
          and are not honored in pattern expressions.

          .. warn:: Use of @string Notation is deprecated as it is inconsistent with pattern syntax.

             This warning is disabled by default to avoid spurious diagnostics
             due to legacy notation in the Coq standard library.
             It can be turned on with the ``-w disj-pattern-notation`` flag.

.. _Scopes:

Notation scopes
---------------

A *notation scope* is a set of notations for terms with their
interpretations. Notation scopes provide a weak, purely
syntactic form of notation overloading: a symbol may
refer to different definitions depending on which notation scopes
are currently open.  For instance, the infix symbol ``+`` can be
used to refer to distinct definitions of the addition operator,
such as for natural numbers, integers or reals.
Notation scopes can include an interpretation for numerals and
strings with the :cmd:`Numeral Notation` and :cmd:`String Notation` commands.

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
   state of Coq declares the following notation scopes:
   ``core_scope``, ``type_scope``, ``function_scope``, ``nat_scope``,
   ``bool_scope``, ``list_scope``, ``int_scope``, ``uint_scope``.

   Use commands such as :cmd:`Notation` to add notations to the scope.

Global interpretation rules for notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

At any time, the interpretation of a notation for a term is done within
a *stack* of notation scopes and lonely notations. If a
notation is defined in multiple scopes, |Coq| uses the interpretation from
the most recently opened notation scope or declared lonely notation.

Note that "stack" is a misleading name.  Each scope or lonely notation can only appear in
the stack once.  New items are pushed onto the top of the stack, except that
adding a item that's already in the stack moves it to the top of the stack instead.
Scopes are removed by name (e.g. by :cmd:`Close Scope`) wherever they are in the
stack, rather than through "pop" operations.

Use the :cmd:`Print Visibility` command to display the current notation scope stack.

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

The notation scope stack can be locally extended within
a :token:`term` with the syntax
:n:`(@term)%@scope_key` (or simply :n:`@term0%@scope_key` for atomic terms).

In this case, :n:`@term` is
interpreted in the scope stack extended with the scope bound to :n:`@scope_key`.

.. cmd:: Delimit Scope @scope_name with @scope_key

   Binds the delimiting key :token:`scope_key` to a scope.

.. cmd:: Undelimit Scope @scope_name

   Removes the delimiting keys associated with a scope.

Binding types or coercion classes to a notation scope
++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. cmd:: Bind Scope @scope_name with {+ @class }

   Binds the notation scope :token:`scope_name` to the type or coercion class :token:`class`.
   When bound, arguments of that type for any function will be interpreted in
   that scope by default.  This default can be overridden for individual functions
   with the :cmd:`Arguments` command.  The association may be convenient
   when a notation scope is naturally associated with a :token:`type` (e.g.
   `nat` and the natural numbers).

   Whether the argument of a function has some type ``type`` is determined
   statically. For instance, if ``f`` is a polymorphic function of type
   :g:`forall X:Type, X -> X` and type :g:`t` is bound to a scope ``scope``,
   then :g:`a` of type :g:`t` in :g:`f t a` is not recognized as an argument to
   be interpreted in scope ``scope``.

   .. coqtop:: in reset

      Parameter U : Set.
      Declare Scope U_scope.
      Bind Scope U_scope with U.
      Parameter Uplus : U -> U -> U.
      Parameter P : forall T:Set, T -> U -> Prop.
      Parameter f : forall T:Set, T -> U.
      Infix "+" := Uplus : U_scope.
      Unset Printing Notations.
      Open Scope nat_scope.

   .. coqtop:: all

      Check (fun x y1 y2 z t => P _ (x + t) ((f _ (y1 + y2) + z))).

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


Notation scopes used in the standard library of Coq
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
  nat. Positive integer numerals in this scope are mapped to their canonical
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
  denominator cross-product) and comes with an interpretation for numerals
  as closed terms of type :g:`Q`.

``Qc_scope``
  This scope includes the standard arithmetical operators and relations on the
  type :g:`Qc` of rational numbers defined as the type of irreducible
  fractions of an integer and a strictly positive integer.

``R_scope``
  This scope includes the standard arithmetical operators and relations on
  type :g:`R` (axiomatic real numbers). It is delimited by the key ``R`` and comes
  with an interpretation for numerals using the :g:`IZR` morphism from binary
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
   The display also includes lonely notations.

   .. todo should the command report all delimiting keys?

   Use the :cmd:`Print Visibility` command to display the current notation scope stack.

.. cmd:: Print Scope @scope_name
   :name: Print Scope

   Displays all notations defined in the notation scope :n:`@scope_name`.
   It also displays the delimiting key and the class to which the
   scope is bound, if any.

.. _Abbreviations:

Abbreviations
--------------

.. cmd:: Notation @ident {* @ident__parm } := @one_term {? ( only parsing ) }
   :name: Notation (abbreviation)

   .. todo: for some reason, Sphinx doesn't complain about a duplicate name if
      :name: is omitted

   Defines an abbreviation :token:`ident` with the parameters :n:`@ident__parm`.

   This command supports the :attr:`local` attribute, which limits the notation to the
   current module.

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

   .. coqtop:: in

      Notation Plus1 B := (Nat.add B 1).

   .. coqtop:: all

      Compute (Plus1 3).

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

   Like for notations, if the right-hand side of an abbreviation is a
   partially applied constant, the abbreviation inherits the implicit
   arguments and notation scopes of the constant. As an
   exception, if the right-hand side is just of the form :n:`@@qualid`,
   this conventionally stops the inheritance of implicit arguments.

   Like for notations, it is possible to bind binders in
   abbreviations. Here is an example:

   .. coqtop:: in reset

      Definition force2 q (P:nat*nat -> Prop) :=
        (forall n', n' >= fst q -> forall p', p' >= snd q -> P q).

      Notation F p P := (force2 p (fun p => P)).
      Check exists x y, F (x,y) (x >= 1 /\ y >= 2).

.. extracted from Gallina chapter

Numerals and strings
--------------------

.. insertprodn primitive_notations primitive_notations

.. prodn::
   primitive_notations ::= @numeral
   | @string

Numerals and strings have no predefined semantics in the calculus. They are
merely notations that can be bound to objects through the notation mechanism.
Initially, numerals are bound to Peano’s representation of natural
numbers (see :ref:`datatypes`).

.. note::

   Negative integers are not at the same level as :n:`@num`, for this
   would make precedence unnatural.

.. _numeral-notations:

Numeral notations
~~~~~~~~~~~~~~~~~

.. cmd:: Numeral Notation @qualid @qualid__parse @qualid__print : @scope_name {? @numeral_modifier }
   :name: Numeral Notation

   .. insertprodn numeral_modifier numeral_modifier

   .. prodn::
      numeral_modifier ::= ( warning after @numeral )
      | ( abstract after @numeral )

   This command allows the user to customize the way numeral literals
   are parsed and printed.

      :n:`@qualid`
         the name of an inductive type,
         while :n:`@qualid__parse` and :n:`@qualid__print` should be the names of the
         parsing and printing functions, respectively.  The parsing function
         :n:`@qualid__parse` should have one of the following types:

            * :n:`Numeral.int -> @qualid`
            * :n:`Numeral.int -> option @qualid`
            * :n:`Numeral.uint -> @qualid`
            * :n:`Numeral.uint -> option @qualid`
            * :n:`Z -> @qualid`
            * :n:`Z -> option @qualid`
            * :n:`Numeral.numeral -> @qualid`
            * :n:`Numeral.numeral -> option @qualid`

         And the printing function :n:`@qualid__print` should have one of the
         following types:

            * :n:`@qualid -> Numeral.int`
            * :n:`@qualid -> option Numeral.int`
            * :n:`@qualid -> Numeral.uint`
            * :n:`@qualid -> option Numeral.uint`
            * :n:`@qualid -> Z`
            * :n:`@qualid -> option Z`
            * :n:`@qualid -> Numeral.numeral`
            * :n:`@qualid -> option Numeral.numeral`

         .. deprecated:: 8.12
            Numeral notations on :g:`Decimal.uint`, :g:`Decimal.int` and
            :g:`Decimal.decimal` are replaced respectively by numeral
            notations on :g:`Numeral.uint`, :g:`Numeral.int` and
            :g:`Numeral.numeral`.

         When parsing, the application of the parsing function
         :n:`@qualid__parse` to the number will be fully reduced, and universes
         of the resulting term will be refreshed.

         Note that only fully-reduced ground terms (terms containing only
         function application, constructors, inductive type families,
         sorts, and primitive integers) will be considered for printing.

      :n:`( warning after @numeral )`
         displays a warning message about a possible stack
         overflow when calling :n:`@qualid__parse` to parse a literal larger than :n:`@numeral`.

         .. warn:: Stack overflow or segmentation fault happens when working with large numbers in @type (threshold may vary depending on your system limits and on the command executed).

            When a :cmd:`Numeral Notation` is registered in the current scope
            with :n:`(warning after @numeral)`, this warning is emitted when
            parsing a numeral greater than or equal to :token:`numeral`.

      :n:`( abstract after @numeral )`
         returns :n:`(@qualid__parse m)` when parsing a literal
         :n:`m` that's greater than :n:`@numeral` rather than reducing it to a normal form.
         Here :g:`m` will be a
         :g:`Numeral.int` or :g:`Numeral.uint` or :g:`Z`, depending on the
         type of the parsing function :n:`@qualid__parse`. This allows for a
         more compact representation of literals in types such as :g:`nat`,
         and limits parse failures due to stack overflow.  Note that a
         warning will be emitted when an integer larger than :token:`numeral`
         is parsed.  Note that :n:`(abstract after @numeral)` has no effect
         when :n:`@qualid__parse` lands in an :g:`option` type.

         .. warn:: To avoid stack overflow, large numbers in @type are interpreted as applications of @qualid__parse.

            When a :cmd:`Numeral Notation` is registered in the current scope
            with :n:`(abstract after @numeral)`, this warning is emitted when
            parsing a numeral greater than or equal to :token:`numeral`.
            Typically, this indicates that the fully computed representation
            of numerals can be so large that non-tail-recursive OCaml
            functions run out of stack space when trying to walk them.

         .. warn:: The 'abstract after' directive has no effect when the parsing function (@qualid__parse) targets an option type.

            As noted above, the :n:`(abstract after @num)` directive has no
            effect when :n:`@qualid__parse` lands in an :g:`option` type.

   .. exn:: Cannot interpret this number as a value of type @type

     The numeral notation registered for :token:`type` does not support
     the given numeral.  This error is given when the interpretation
     function returns :g:`None`, or if the interpretation is registered
     only for integers or non-negative integers, and the given numeral
     has a fractional or exponent part or is negative.


   .. exn:: @qualid__parse should go from Numeral.int to @type or (option @type). Instead of Numeral.int, the types Numeral.uint or Z or Int63.int or Numeral.numeral could be used (you may need to require BinNums or Numeral or Int63 first).

     The parsing function given to the :cmd:`Numeral Notation`
     vernacular is not of the right type.

   .. exn:: @qualid__print should go from @type to Numeral.int or (option Numeral.int).  Instead of Numeral.int, the types Numeral.uint or Z or Int63.int or Numeral.numeral could be used (you may need to require BinNums or Numeral or Int63 first).

     The printing function given to the :cmd:`Numeral Notation`
     vernacular is not of the right type.

   .. exn:: Unexpected term @term while parsing a numeral notation.

     Parsing functions must always return ground terms, made up of
     applications of constructors, inductive types, and primitive
     integers.  Parsing functions may not return terms containing
     axioms, bare (co)fixpoints, lambdas, etc.

   .. exn:: Unexpected non-option term @term while parsing a numeral notation.

     Parsing functions expected to return an :g:`option` must always
     return a concrete :g:`Some` or :g:`None` when applied to a
     concrete numeral expressed as a (hexa)decimal.  They may not return
     opaque constants.

String notations
~~~~~~~~~~~~~~~~

.. cmd:: String Notation @qualid @qualid__parse @qualid__print : @scope_name
   :name: String Notation

   Allows the user to customize how strings are parsed and printed.

   The token :n:`@qualid` should be the name of an inductive type,
   while :n:`@qualid__parse` and :n:`@qualid__print` should be the names of the
   parsing and printing functions, respectively.  The parsing function
   :n:`@qualid__parse` should have one of the following types:

      * :n:`Byte.byte -> @qualid`
      * :n:`Byte.byte -> option @qualid`
      * :n:`list Byte.byte -> @qualid`
      * :n:`list Byte.byte -> option @qualid`

   The printing function :n:`@qualid__print` should have one of the
   following types:

      * :n:`@qualid -> Byte.byte`
      * :n:`@qualid -> option Byte.byte`
      * :n:`@qualid -> list Byte.byte`
      * :n:`@qualid -> option (list Byte.byte)`

   When parsing, the application of the parsing function
   :n:`@qualid__parse` to the string will be fully reduced, and universes
   of the resulting term will be refreshed.

   Note that only fully-reduced ground terms (terms containing only
   function application, constructors, inductive type families,
   sorts, and primitive integers) will be considered for printing.

   .. exn:: Cannot interpret this string as a value of type @type

     The string notation registered for :token:`type` does not support
     the given string.  This error is given when the interpretation
     function returns :g:`None`.

   .. exn:: @qualid__parse should go from Byte.byte or (list Byte.byte) to @type or (option @type).

     The parsing function given to the :cmd:`String Notation`
     vernacular is not of the right type.

   .. exn:: @qualid__print should go from @type to Byte.byte or (option Byte.byte) or (list Byte.byte) or (option (list Byte.byte)).

     The printing function given to the :cmd:`String Notation`
     vernacular is not of the right type.

   .. exn:: Unexpected term @term while parsing a string notation.

     Parsing functions must always return ground terms, made up of
     applications of constructors, inductive types, and primitive
     integers.  Parsing functions may not return terms containing
     axioms, bare (co)fixpoints, lambdas, etc.

   .. exn:: Unexpected non-option term @term while parsing a string notation.

     Parsing functions expected to return an :g:`option` must always
     return a concrete :g:`Some` or :g:`None` when applied to a
     concrete string expressed as a decimal.  They may not return
     opaque constants.

The following errors apply to both string and numeral notations:

   .. exn:: @type is not an inductive type.

     String and numeral notations can only be declared for inductive types with no
     arguments.

   .. exn:: Cannot interpret in @scope_name because @qualid could not be found in the current environment.

     The inductive type used to register the string or numeral notation is no
     longer available in the environment.  Most likely, this is because
     the notation was declared inside a functor for an
     inductive type inside the functor.  This use case is not currently
     supported.

     Alternatively, you might be trying to use a primitive token
     notation from a plugin which forgot to specify which module you
     must :g:`Require` for access to that notation.

   .. exn:: Syntax error: [prim:reference] expected after 'Notation' (in [vernac:command]).

     The type passed to :cmd:`String Notation` or :cmd:`Numeral Notation` must be a single qualified
     identifier.

   .. exn:: Syntax error: [prim:reference] expected after [prim:reference] (in [vernac:command]).

     Both functions passed to :cmd:`String Notation` or :cmd:`Numeral Notation` must be single qualified
     identifiers.

     .. todo: generally we don't document syntax errors.  Is this a good execption?

   .. exn:: @qualid is bound to a notation that does not denote a reference.

     Identifiers passed to :cmd:`String Notation` or :cmd:`Numeral Notation` must be global
     references, or notations which evaluate to single qualified identifiers.

     .. todo note on "single qualified identifiers" https://github.com/coq/coq/pull/11718#discussion_r415076703

.. _TacticNotation:

Tactic Notations
-----------------

Tactic notations allow customizing the syntax of tactics.

.. todo move to the Ltac chapter

.. todo to discuss after moving to the ltac chapter:
   any words of wisdom on when to use tactic notation vs ltac?
   can you run into problems if you shadow another tactic or tactic notation?
   If so, how to avoid ambiguity?

.. cmd:: Tactic Notation {? ( at level @num ) } {+ @ltac_production_item } := @ltac_expr

   .. insertprodn ltac_production_item ltac_production_item

   .. prodn::
      ltac_production_item ::= @string
      | @ident {? ( @ident {? , @string } ) }

   Defines a *tactic notation*, which extends the parsing and pretty-printing of tactics.

   This command supports the :attr:`local` attribute, which limits the notation to the
   current module.

      :token:`num`
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

   .. coqtop:: in

      Tactic Notation "destruct_with_eqn" constr(x) := destruct x eqn:?.

   For a complex example, examine the 16 `Tactic Notation "setoid_replace"`\s
   defined in :file:`$COQLIB/theories/Classes/SetoidTactics.v`, which are designed
   to accept any subset of 4 optional parameters.

   The nonterminals that can specified in the tactic notation are:

     .. todo uconstr represents a type with holes.  At the moment uconstr doesn't
        appear in the documented grammar.  Maybe worth ressurecting with a better name,
        maybe "open_term"?
        see https://github.com/coq/coq/pull/11718#discussion_r413721234

     .. todo 'open_constr' appears to be another possible value based on the
        the message from "Tactic Notation open_constr := idtac".
        Also (at least) "ref", "string", "preident", "int" and "ssrpatternarg".
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
        - a global reference of term
        - :tacn:`unfold`

      * - ``smart_global``
        - :token:`reference`
        - a global reference of term
        - :tacn:`with_strategy`

      * - ``constr``
        - :token:`term`
        - a term
        - :tacn:`exact`

      * - ``uconstr``
        - :token:`term`
        - an untyped term
        - :tacn:`refine`

      * - ``integer``
        - :token:`int`
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
   implementation of Coq

.. [#no_associativity] Coq accepts notations declared as nonassociative but the parser on
   which Coq is built, namely Camlp5, currently does not implement ``no associativity`` and
   replaces it with ``left associativity``; hence it is the same for Coq: ``no associativity``
   is in fact ``left associativity`` for the purposes of parsing
