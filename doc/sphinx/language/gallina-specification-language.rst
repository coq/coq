.. _gallinaspecificationlanguage:

------------------------------------
 The Gallina specification language
------------------------------------

This chapter describes Gallina, the specification language of Coq. It allows
developing mathematical theories and to prove specifications of programs. The
theories are built from axioms, hypotheses, parameters, lemmas, theorems and
definitions of constants, functions, predicates and sets. The syntax of logical
objects involved in theories is described in Section :ref:`term`. The
language of commands, called *The Vernacular* is described in Section
:ref:`vernacular`.

In Coq, logical objects are typed to ensure their logical correctness.  The
rules implemented by the typing algorithm are described in Chapter :ref:`calculusofinductiveconstructions`.


..  About the grammars in the manual
    ================================

    Grammars are presented in Backus-Naur form (BNF). Terminal symbols are
    set in black ``typewriter font``. In addition, there are special notations for
    regular expressions.

    An expression enclosed in square brackets ``[…]`` means at most one
    occurrence of this expression (this corresponds to an optional
    component).

    The notation “``entry sep … sep entry``” stands for a non empty sequence
    of expressions parsed by entry and separated by the literal “``sep``” [1]_.

    Similarly, the notation “``entry … entry``” stands for a non empty
    sequence of expressions parsed by the “``entry``” entry, without any
    separator between.

    At the end, the notation “``[entry sep … sep entry]``” stands for a
    possibly empty sequence of expressions parsed by the “``entry``” entry,
    separated by the literal “``sep``”.

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

.. _term:

Terms
=====

Syntax of terms
---------------

The following grammars describe the basic syntax of the terms of the
*Calculus of Inductive Constructions* (also called Cic). The formal
presentation of Cic is given in Chapter :ref:`calculusofinductiveconstructions`. Extensions of this syntax
are given in Chapter :ref:`extensionsofgallina`. How to customize the syntax
is described in Chapter :ref:`syntaxextensionsandinterpretationscopes`.

.. insertprodn term field_def

.. prodn::
   term ::= forall @open_binders , @term
   | fun @open_binders => @term
   | @term_let
   | if @term {? {? as @name } return @term100 } then @term else @term
   | @term_fix
   | @term_cofix
   | @term100
   term100 ::= @term_cast
   | @term10
   term10 ::= @term1 {+ @arg }
   | @ @qualid {? @univ_annot } {* @term1 }
   | @term1
   arg ::= ( @ident := @term )
   | @term1
   one_term ::= @term1
   | @ @qualid {? @univ_annot }
   term1 ::= @term_projection
   | @term0 % @scope
   | @term0
   term0 ::= @qualid {? @univ_annot }
   | @sort
   | @numeral
   | @string
   | _
   | @term_evar
   | @term_match
   | ( @term )
   | %{%| {* @field_def } %|%}
   | `%{ @term %}
   | `( @term )
   | ltac : ( @ltac_expr )
   field_def ::= @qualid {* @binder } := @term

.. note::

   Many commands and tactics use :n:`@one_term` rather than :n:`@term`.
   The former need to be enclosed in parentheses unless they're very
   simple, such as a single identifier.  This avoids confusing a space-separated
   list of terms with a :n:`@term1` applied to a list of arguments.

.. _types:

Types
-----

.. prodn::
   type ::= @term

:n:`@type`\s are a subset of :n:`@term`\s; not every :n:`@term` is a :n:`@type`.
Every term has an associated type, which
can be determined by applying the :ref:`typing-rules`.  Distinct terms
may share the same type, for example 0 and 1 are both of type `nat`, the
natural numbers.

.. _gallina-identifiers:

Qualified identifiers and simple identifiers
--------------------------------------------

.. insertprodn qualid field_ident

.. prodn::
   qualid ::= @ident {* @field_ident }
   field_ident ::= .@ident

*Qualified identifiers* (:n:`@qualid`) denote *global constants*
(definitions, lemmas, theorems, remarks or facts), *global variables*
(parameters or axioms), *inductive types* or *constructors of inductive
types*. *Simple identifiers* (or shortly :n:`@ident`) are a syntactic subset
of qualified identifiers. Identifiers may also denote *local variables*,
while qualified identifiers do not.

Field identifiers, written :n:`@field_ident`, are identifiers prefixed by
`.` (dot) with no blank between the dot and the identifier.


Numerals and strings
--------------------

Numerals and strings have no predefined semantics in the calculus. They are
merely notations that can be bound to objects through the notation mechanism
(see Chapter :ref:`syntaxextensionsandinterpretationscopes` for details).
Initially, numerals are bound to Peano’s representation of natural
numbers (see :ref:`datatypes`).

.. note::

   Negative integers are not at the same level as :n:`@num`, for this
   would make precedence unnatural.

.. index::
   single: Set (sort)
   single: SProp
   single: Prop
   single: Type

Sorts
-----

.. insertprodn sort univ_constraint

.. prodn::
   sort ::= Set
   | Prop
   | SProp
   | Type
   | Type @%{ _ %}
   | Type @%{ @universe %}
   universe ::= max ( {+, @universe_expr } )
   | @universe_expr
   universe_expr ::= @universe_name {? + @num }
   universe_name ::= @qualid
   | Set
   | Prop
   univ_annot ::= @%{ {* @universe_level } %}
   universe_level ::= Set
   | Prop
   | Type
   | _
   | @qualid
   univ_decl ::= @%{ {* @ident } {? + } {? %| {*, @univ_constraint } {? + } } %}
   univ_constraint ::= @universe_name {| < | = | <= } @universe_name

There are four sorts :g:`SProp`, :g:`Prop`, :g:`Set`  and :g:`Type`.

-  :g:`SProp` is the universe of *definitionally irrelevant
   propositions* (also called *strict propositions*).

-  :g:`Prop` is the universe of *logical propositions*. The logical propositions
   themselves are typing the proofs. We denote propositions by :n:`@form`.
   This constitutes a semantic subclass of the syntactic class :n:`@term`.

-  :g:`Set` is the universe of *program types* or *specifications*. The
   specifications themselves are typing the programs. We denote
   specifications by :n:`@specif`. This constitutes a semantic subclass of
   the syntactic class :n:`@term`.

-  :g:`Type` is the type of sorts.

More on sorts can be found in Section :ref:`sorts`.

.. _binders:

Binders
-------

.. insertprodn open_binders binder

.. prodn::
   open_binders ::= {+ @name } : @term
   | {+ @binder }
   name ::= _
   | @ident
   binder ::= @name
   | ( {+ @name } : @type )
   | ( @name {? : @type } := @term )
   | @implicit_binders
   | @generalizing_binder
   | ( @name : @type %| @term )
   | ' @pattern0

Various constructions such as :g:`fun`, :g:`forall`, :g:`fix` and :g:`cofix`
*bind* variables. A binding is represented by an identifier. If the binding
variable is not used in the expression, the identifier can be replaced by the
symbol :g:`_`. When the type of a bound variable cannot be synthesized by the
system, it can be specified with the notation :n:`(@ident : @type)`. There is also
a notation for a sequence of binding variables sharing the same type:
:n:`({+ @ident} : @type)`. A
binder can also be any pattern prefixed by a quote, e.g. :g:`'(x,y)`.

Some constructions allow the binding of a variable to value. This is
called a “let-binder”. The entry :n:`@binder` of the grammar accepts
either an assumption binder as defined above or a let-binder. The notation in
the latter case is :n:`(@ident := @term)`. In a let-binder, only one
variable can be introduced at the same time. It is also possible to give
the type of the variable as follows:
:n:`(@ident : @type := @term)`.

Lists of :n:`@binder`\s are allowed. In the case of :g:`fun` and :g:`forall`,
it is intended that at least one binder of the list is an assumption otherwise
fun and forall gets identical. Moreover, parentheses can be omitted in
the case of a single sequence of bindings sharing the same type (e.g.:
:g:`fun (x y z : A) => t` can be shortened in :g:`fun x y z : A => t`).

.. index:: fun ... => ...

Abstractions: fun
-----------------

The expression :n:`fun @ident : @type => @term` defines the
*abstraction* of the variable :n:`@ident`, of type :n:`@type`, over the term
:n:`@term`. It denotes a function of the variable :n:`@ident` that evaluates to
the expression :n:`@term` (e.g. :g:`fun x : A => x` denotes the identity
function on type :g:`A`). The keyword :g:`fun` can be followed by several
binders as given in Section :ref:`binders`. Functions over
several variables are equivalent to an iteration of one-variable
functions. For instance the expression
:n:`fun {+ @ident__i } : @type => @term`
denotes the same function as :n:`{+ fun @ident__i : @type => } @term`. If
a let-binder occurs in
the list of binders, it is expanded to a let-in definition (see
Section :ref:`let-in`).

.. index:: forall

Products: forall
----------------

The expression :n:`forall @ident : @type, @term` denotes the
*product* of the variable :n:`@ident` of type :n:`@type`, over the term :n:`@term`.
As for abstractions, :g:`forall` is followed by a binder list, and products
over several variables are equivalent to an iteration of one-variable
products. Note that :n:`@term` is intended to be a type.

If the variable :n:`@ident` occurs in :n:`@term`, the product is called
*dependent product*. The intention behind a dependent product
:g:`forall x : A, B` is twofold. It denotes either
the universal quantification of the variable :g:`x` of type :g:`A`
in the proposition :g:`B` or the functional dependent product from
:g:`A` to :g:`B` (a construction usually written
:math:`\Pi_{x:A}.B` in set theory).

Non dependent product types have a special notation: :g:`A -> B` stands for
:g:`forall _ : A, B`. The *non dependent product* is used both to denote
the propositional implication and function types.

Applications
------------

:n:`@term__fun @term` denotes applying the function :n:`@term__fun` to :token:`term`.

:n:`@term__fun {+ @term__i }` denotes applying
:n:`@term__fun` to the arguments :n:`@term__i`.  It is
equivalent to :n:`( … ( @term__fun @term__1 ) … ) @term__n`:
associativity is to the left.

The notation :n:`(@ident := @term)` for arguments is used for making
explicit the value of implicit arguments (see
Section :ref:`explicit-applications`).

.. index::
   single: ... : ... (type cast)
   single: ... <: ...
   single: ... <<: ...

Type cast
---------

.. insertprodn term_cast term_cast

.. prodn::
   term_cast ::= @term10 <: @term
   | @term10 <<: @term
   | @term10 : @term
   | @term10 :>

The expression :n:`@term : @type` is a type cast expression. It enforces
the type of :n:`@term` to be :n:`@type`.

:n:`@term <: @type` locally sets up the virtual machine for checking that
:n:`@term` has type :n:`@type`.

:n:`@term <<: @type` uses native compilation for checking that :n:`@term`
has type :n:`@type`.

.. index:: _

Inferable subterms
------------------

Expressions often contain redundant pieces of information. Subterms that can be
automatically inferred by Coq can be replaced by the symbol ``_`` and Coq will
guess the missing piece of information.

.. index:: let ... := ... (term)

.. _let-in:

Let-in definitions
------------------

.. insertprodn term_let term_let

.. prodn::
   term_let ::= let @name {? : @type } := @term in @term
   | let @name {+ @binder } {? : @type } := @term in @term
   | let ( {*, @name } ) {? {? as @name } return @term100 } := @term in @term
   | let ' @pattern := @term {? return @term100 } in @term
   | let ' @pattern in @pattern := @term return @term100 in @term

:n:`let @ident := @term in @term’`
denotes the local binding of :n:`@term` to the variable
:n:`@ident` in :n:`@term`’. There is a syntactic sugar for let-in
definition of functions: :n:`let @ident {+ @binder} := @term in @term’`
stands for :n:`let @ident := fun {+ @binder} => @term in @term’`.

.. index:: match ... with ...

Definition by cases: match
--------------------------

.. insertprodn term_match pattern0

.. prodn::
   term_match ::= match {+, @case_item } {? return @term100 } with {? %| } {*| @eqn } end
   case_item ::= @term100 {? as @name } {? in @pattern }
   eqn ::= {+| {+, @pattern } } => @term
   pattern ::= @pattern10 : @term
   | @pattern10
   pattern10 ::= @pattern1 as @name
   | @pattern1 {* @pattern1 }
   | @ @qualid {* @pattern1 }
   pattern1 ::= @pattern0 % @scope
   | @pattern0
   pattern0 ::= @qualid
   | %{%| {* @qualid := @pattern } %|%}
   | _
   | ( {+| @pattern } )
   | @numeral
   | @string

Objects of inductive types can be destructured by a case-analysis
construction called *pattern matching* expression. A pattern matching
expression is used to analyze the structure of an inductive object and
to apply specific treatments accordingly.

This paragraph describes the basic form of pattern matching. See
Section :ref:`Mult-match` and Chapter :ref:`extendedpatternmatching` for the description
of the general form. The basic form of pattern matching is characterized
by a single :n:`@case_item` expression, an :n:`@eqn` restricted to a
single :n:`@pattern` and :n:`@pattern` restricted to the form
:n:`@qualid {* @ident}`.

The expression
:n:`match @term {? return @term100 } with {+| @pattern__i => @term__i } end` denotes a
*pattern matching* over the term :n:`@term` (expected to be
of an inductive type :math:`I`). The :n:`@term__i`
are the *branches* of the pattern matching
expression. Each :n:`@pattern__i` has the form :n:`@qualid @ident`
where :n:`@qualid` must denote a constructor. There should be
exactly one branch for every constructor of :math:`I`.

The :n:`return @term100` clause gives the type returned by the whole match
expression. There are several cases. In the *non dependent* case, all
branches have the same type, and the :n:`return @term100` specifies that type.
In this case, :n:`return @term100` can usually be omitted as it can be
inferred from the type of the branches [1]_.

In the *dependent* case, there are three subcases. In the first subcase,
the type in each branch may depend on the exact value being matched in
the branch. In this case, the whole pattern matching itself depends on
the term being matched. This dependency of the term being matched in the
return type is expressed with an :n:`@ident` clause where :n:`@ident`
is dependent in the return type. For instance, in the following example:

.. coqtop:: in

   Inductive bool : Type := true : bool | false : bool.
   Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : eq A x x.
   Inductive or (A:Prop) (B:Prop) : Prop :=
     | or_introl : A -> or A B
     | or_intror : B -> or A B.

   Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
     match b as x return or (eq bool x true) (eq bool x false) with
     | true => or_introl (eq bool true true) (eq bool true false) (eq_refl bool true)
     | false => or_intror (eq bool false true) (eq bool false false) (eq_refl bool false)
     end.

the branches have respective types ":g:`or (eq bool true true) (eq bool true false)`"
and ":g:`or (eq bool false true) (eq bool false false)`" while the whole
pattern matching expression has type ":g:`or (eq bool b true) (eq bool b false)`",
the identifier :g:`b` being used to represent the dependency.

.. note::

   When the term being matched is a variable, the ``as`` clause can be
   omitted and the term being matched can serve itself as binding name in
   the return type. For instance, the following alternative definition is
   accepted and has the same meaning as the previous one.

   .. coqtop:: none

      Reset bool_case.

   .. coqtop:: in

      Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
      match b return or (eq bool b true) (eq bool b false) with
      | true => or_introl (eq bool true true) (eq bool true false) (eq_refl bool true)
      | false => or_intror (eq bool false true) (eq bool false false) (eq_refl bool false)
      end.

The second subcase is only relevant for annotated inductive types such
as the equality predicate (see Section :ref:`coq-equality`),
the order predicate on natural numbers or the type of lists of a given
length (see Section :ref:`matching-dependent`). In this configuration, the
type of each branch can depend on the type dependencies specific to the
branch and the whole pattern matching expression has a type determined
by the specific dependencies in the type of the term being matched. This
dependency of the return type in the annotations of the inductive type
is expressed with a clause in the form
:n:`in @qualid {+ _ } {+ @pattern }`, where

-  :n:`@qualid` is the inductive type of the term being matched;

-  the holes :n:`_` match the parameters of the inductive type: the
   return type is not dependent on them.

-  each :n:`@pattern` matches the annotations of the
   inductive type: the return type is dependent on them

-  in the basic case which we describe below, each :n:`@pattern`
   is a name :n:`@ident`; see :ref:`match-in-patterns` for the
   general case

For instance, in the following example:

.. coqtop:: in

   Definition eq_sym (A:Type) (x y:A) (H:eq A x y) : eq A y x :=
   match H in eq _ _ z return eq A z x with
   | eq_refl _ _ => eq_refl A x
   end.

the type of the branch is :g:`eq A x x` because the third argument of
:g:`eq` is :g:`x` in the type of the pattern :g:`eq_refl`. On the contrary, the
type of the whole pattern matching expression has type :g:`eq A y x` because the
third argument of eq is y in the type of H. This dependency of the case analysis
in the third argument of :g:`eq` is expressed by the identifier :g:`z` in the
return type.

Finally, the third subcase is a combination of the first and second
subcase. In particular, it only applies to pattern matching on terms in
a type with annotations. For this third subcase, both the clauses ``as`` and
``in`` are available.

There are specific notations for case analysis on types with one or two
constructors: ``if … then … else …`` and ``let (…,…) := … in …`` (see
Sections :ref:`if-then-else` and :ref:`irrefutable-patterns`).

.. index::
   single: fix
   single: cofix

Recursive and co-recursive functions: fix and cofix
---------------------------------------------------

.. insertprodn term_fix fixannot

.. prodn::
   term_fix ::= let fix @fix_body in @term
   | fix @fix_body {? {+ with @fix_body } for @ident }
   fix_body ::= @ident {* @binder } {? @fixannot } {? : @type } := @term
   fixannot ::= %{ struct @ident %}
   | %{ wf @one_term @ident %}
   | %{ measure @one_term {? @ident } {? @one_term } %}


The expression ":n:`fix @ident__1 @binder__1 : @type__1 := @term__1 with … with @ident__n @binder__n : @type__n := @term__n for @ident__i`" denotes the
:math:`i`-th component of a block of functions defined by mutual structural
recursion. It is the local counterpart of the :cmd:`Fixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

The association of a single fixpoint and a local definition have a special
syntax: :n:`let fix @ident {* @binder } := @term in` stands for
:n:`let @ident := fix @ident {* @binder } := @term in`. The same applies for co-fixpoints.

Some options of :n:`@fixannot` are only supported in specific constructs.  :n:`fix` and :n:`let fix`
only support the :n:`struct` option, while :n:`wf` and :n:`measure` are only supported in
commands such as :cmd:`Function` and :cmd:`Program Fixpoint`.

.. insertprodn term_cofix cofix_body

.. prodn::
   term_cofix ::= let cofix @cofix_body in @term
   | cofix @cofix_body {? {+ with @cofix_body } for @ident }
   cofix_body ::= @ident {* @binder } {? : @type } := @term

The expression
":n:`cofix @ident__1 @binder__1 : @type__1 with … with @ident__n @binder__n : @type__n for @ident__i`"
denotes the :math:`i`-th component of a block of terms defined by a mutual guarded
co-recursion. It is the local counterpart of the :cmd:`CoFixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

.. _vernacular:

The Vernacular
==============

.. insertprodn vernacular sentence

.. prodn::
   vernacular ::= {* @sentence }
   sentence ::= {? @all_attrs } @command .
   | {? @all_attrs } {? @num : } @query_command .
   | {? @all_attrs } {? @toplevel_selector } @ltac_expr {| . | ... }
   | @control_command

The top-level input to |Coq| is a series of :n:`@sentence`\s,
which are :production:`tactic`\s or :production:`command`\s,
generally terminated with a period
and optionally decorated with :ref:`gallina-attributes`.  :n:`@ltac_expr` syntax supports both simple
and compound tactics.  For example: ``split`` is a simple tactic while ``split; auto`` combines two
simple tactics.

Tactics specify how to transform the current proof state as a step in creating a proof.  They
are syntactically valid only when |Coq| is in proof mode, such as after a :cmd:`Theorem` command
and before any subsequent proof-terminating command such as :cmd:`Qed`.  See :ref:`proofhandling` for more
on proof mode.

By convention, command names begin with uppercase letters, while
tactic names begin with lowercase letters.  Commands appear in the
HTML documentation in blue boxes after the label "Command".  In the pdf, they appear
after the boldface label "Command:".  Commands are listed in the :ref:`command_index`.

Similarly, tactics appear after the label "Tactic".  Tactics are listed in the :ref:`tactic_index`.

.. _gallina-assumptions:

Assumptions
-----------

Assumptions extend the environment with axioms, parameters, hypotheses
or variables. An assumption binds an :n:`@ident` to a :n:`@type`. It is accepted
by Coq if and only if this :n:`@type` is a correct type in the environment
preexisting the declaration and if :n:`@ident` was not previously defined in
the same module. This :n:`@type` is considered to be the type (or
specification, or statement) assumed by :n:`@ident` and we say that :n:`@ident`
has type :n:`@type`.

.. _Axiom:

.. cmd:: @assumption_token {? Inline {? ( @num ) } } {| {+ ( @assumpt ) } | @assumpt }
   :name: Axiom; Axioms; Conjecture; Conjectures; Hypothesis; Hypotheses; Parameter; Parameters; Variable; Variables

   .. insertprodn assumption_token of_type

   .. prodn::
      assumption_token ::= {| Axiom | Axioms }
      | {| Conjecture | Conjectures }
      | {| Parameter | Parameters }
      | {| Hypothesis | Hypotheses }
      | {| Variable | Variables }
      assumpt ::= {+ @ident_decl } @of_type
      ident_decl ::= @ident {? @univ_decl }
      of_type ::= {| : | :> | :>> } @type

   These commands bind one or more :n:`@ident`\(s) to specified :n:`@type`\(s) as their specifications in
   the global context. The fact asserted by the :n:`@type` (or, equivalently, the existence
   of an object of this type) is accepted as a postulate.

   :cmd:`Axiom`, :cmd:`Conjecture`, :cmd:`Parameter` and their plural forms
   are equivalent.  They can take the :attr:`local` attribute (see :ref:`gallina-attributes`),
   which makes the defined :n:`@ident`\s accessible by :cmd:`Import` and its variants
   only through their fully qualified names.

   Similarly, :cmd:`Hypothesis`, :cmd:`Variable` and their plural forms are equivalent.  Outside
   of a section, these are equivalent to :n:`Local Parameter`.  Inside a section, the
   :n:`@ident`\s defined are only accessible within the section.  When the current section
   is closed, the :n:`@ident`\(s) become undefined and every object depending on them will be explicitly
   parameterized (i.e., the variables are *discharged*).  See Section :ref:`section-mechanism`.

   The :n:`Inline` clause is only relevant inside functors.  See :cmd:`Module`.

.. example:: Simple assumptions

    .. coqtop:: reset in

       Parameter X Y : Set.
       Parameter (R : X -> Y -> Prop) (S : Y -> X -> Prop).
       Axiom R_S_inv : forall x y, R x y <-> S y x.

.. exn:: @ident already exists.
   :name: @ident already exists. (Axiom)
   :undocumented:

.. warn:: @ident is declared as a local axiom

   Warning generated when using :cmd:`Variable` or its equivalent
   instead of :n:`Local Parameter` or its equivalent.

.. note::
   We advise using the commands :cmd:`Axiom`, :cmd:`Conjecture` and
   :cmd:`Hypothesis` (and their plural forms) for logical postulates (i.e. when
   the assertion :n:`@type` is of sort :g:`Prop`), and to use the commands
   :cmd:`Parameter` and :cmd:`Variable` (and their plural forms) in other cases
   (corresponding to the declaration of an abstract object of the given type).

.. _gallina-definitions:

Definitions
-----------

Definitions extend the environment with associations of names to terms.
A definition can be seen as a way to give a meaning to a name or as a
way to abbreviate a term. In any case, the name can later be replaced at
any time by its definition.

The operation of unfolding a name into its definition is called
:math:`\delta`-conversion (see Section :ref:`delta-reduction`). A
definition is accepted by the system if and only if the defined term is
well-typed in the current context of the definition and if the name is
not already used. The name defined by the definition is called a
*constant* and the term it refers to is its *body*. A definition has a
type which is the type of its body.

A formal presentation of constants and environments is given in
Section :ref:`typing-rules`.

.. cmd:: {| Definition | Example } @ident_decl @def_body
   :name: Definition; Example

   .. insertprodn def_body def_body

   .. prodn::
      def_body ::= {* @binder } {? : @type } := {? @reduce } @term
      | {* @binder } : @type

   These commands bind :n:`@term` to the name :n:`@ident` in the environment,
   provided that :n:`@term` is well-typed.  They can take the :attr:`local` attribute (see :ref:`gallina-attributes`),
   which makes the defined :n:`@ident` accessible by :cmd:`Import` and its variants
   only through their fully qualified names.
   If :n:`@reduce` is present then :n:`@ident` is bound to the result of the specified
   computation on :n:`@term`.

   These commands also support the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`program` and
   :attr:`canonical` attributes.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

   The form :n:`Definition @ident : @type := @term` checks that the type of :n:`@term`
   is definitionally equal to :n:`@type`, and registers :n:`@ident` as being of type
   :n:`@type`, and bound to value :n:`@term`.

   The form :n:`Definition @ident {* @binder } : @type := @term` is equivalent to
   :n:`Definition @ident : forall {* @binder }, @type := fun {* @binder } => @term`.

   .. seealso:: :cmd:`Opaque`, :cmd:`Transparent`, :tacn:`unfold`.

   .. exn:: @ident already exists.
      :name: @ident already exists. (Definition)
      :undocumented:

   .. exn:: The term @term has type @type while it is expected to have type @type'.
      :undocumented:

.. _gallina-inductive-definitions:

Inductive types
---------------

.. cmd:: Inductive @inductive_definition {* with @inductive_definition }

   .. insertprodn inductive_definition constructor

   .. prodn::
      inductive_definition ::= {? > } @ident_decl {* @binder } {? %| {* @binder } } {? : @type } {? := {? @constructors_or_record } } {? @decl_notations }
      constructors_or_record ::= {? %| } {+| @constructor }
      | {? @ident } %{ {*; @record_field } %}
      constructor ::= @ident {* @binder } {? @of_type }

   This command defines one or more
   inductive types and its constructors.  Coq generates destructors
   depending on the universe that the inductive type belongs to.

   The destructors are named :n:`@ident`\ ``_rect``, :n:`@ident`\ ``_ind``,
   :n:`@ident`\ ``_rec`` and :n:`@ident`\ ``_sind``, which
   respectively correspond to elimination principles on :g:`Type`, :g:`Prop`,
   :g:`Set` and :g:`SProp`.  The type of the destructors
   expresses structural induction/recursion principles over objects of
   type :n:`@ident`.  The constant :n:`@ident`\ ``_ind`` is always
   generated, whereas :n:`@ident`\ ``_rec`` and :n:`@ident`\ ``_rect``
   may be impossible to derive (for example, when :n:`@ident` is a
   proposition).

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

   Mutually inductive types can be defined by including multiple :n:`@inductive_definition`\s.
   The :n:`@ident`\s are simultaneously added to the environment before the types of constructors are checked.
   Each :n:`@ident` can be used independently thereafter.
   See :ref:`mutually_inductive_types`.

   If the entire inductive definition is parameterized with :n:`@binder`\s, the parameters correspond
   to a local context in which the entire set of inductive declarations is interpreted.
   For this reason, the parameters must be strictly the same for each inductive type.
   See :ref:`parametrized-inductive-types`.

   Constructor :n:`@ident`\s can come with :n:`@binder`\s, in which case
   the actual type of the constructor is :n:`forall {* @binder }, @type`.

   .. exn:: Non strictly positive occurrence of @ident in @type.

      The types of the constructors have to satisfy a *positivity condition*
      (see Section :ref:`positivity`). This condition ensures the soundness of
      the inductive definition. The positivity checking can be disabled using
      the :flag:`Positivity Checking` flag (see :ref:`controlling-typing-flags`).

   .. exn:: The conclusion of @type is not valid; it must be built from @ident.

      The conclusion of the type of the constructors must be the inductive type
      :n:`@ident` being defined (or :n:`@ident` applied to arguments in
      the case of annotated inductive types — cf. next section).

The following subsections show examples of simple inductive types,
simple annotated inductive types, simple parametric inductive types,
mutually inductive types and private (matching) inductive types.

.. _simple-inductive-types:

Simple inductive types
~~~~~~~~~~~~~~~~~~~~~~

A simple inductive type belongs to a universe that is a simple :n:`@sort`.

.. example::

   The set of natural numbers is defined as:

   .. coqtop:: reset all

      Inductive nat : Set :=
      | O : nat
      | S : nat -> nat.

   The type nat is defined as the least :g:`Set` containing :g:`O` and closed by
   the :g:`S` constructor. The names :g:`nat`, :g:`O` and :g:`S` are added to the
   environment.

   This definition generates four elimination principles:
   :g:`nat_rect`, :g:`nat_ind`, :g:`nat_rec` and :g:`nat_sind`. The type of :g:`nat_ind` is:

   .. coqtop:: all

      Check nat_ind.

   This is the well known structural induction principle over natural
   numbers, i.e. the second-order form of Peano’s induction principle. It
   allows proving universal properties of natural numbers (:g:`forall
   n:nat, P n`) by induction on :g:`n`.

   The types of :g:`nat_rect`, :g:`nat_rec` and :g:`nat_sind` are similar, except that they
   apply to, respectively, :g:`(P:nat->Type)`, :g:`(P:nat->Set)` and :g:`(P:nat->SProp)`. They correspond to
   primitive induction principles (allowing dependent types) respectively
   over sorts ```Type``, ``Set`` and ``SProp``.

In the case where inductive types don't have annotations (the next section
gives an example of annotations), a constructor can be defined
by giving the type of its arguments alone.

.. example::

   .. coqtop:: reset none

      Reset nat.

   .. coqtop:: in

      Inductive nat : Set := O | S (_:nat).

Simple annotated inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In annotated inductive types, the universe where the inductive type
is defined is no longer a simple :n:`@sort`, but what is called an arity,
which is a type whose conclusion is a :n:`@sort`.

.. example::

   As an example of annotated inductive types, let us define the
   :g:`even` predicate:

   .. coqtop:: all

      Inductive even : nat -> Prop :=
      | even_0 : even O
      | even_SS : forall n:nat, even n -> even (S (S n)).

   The type :g:`nat->Prop` means that :g:`even` is a unary predicate (inductively
   defined) over natural numbers. The type of its two constructors are the
   defining clauses of the predicate :g:`even`. The type of :g:`even_ind` is:

   .. coqtop:: all

      Check even_ind.

   From a mathematical point of view, this asserts that the natural numbers satisfying
   the predicate :g:`even` are exactly in the smallest set of naturals satisfying the
   clauses :g:`even_0` or :g:`even_SS`. This is why, when we want to prove any
   predicate :g:`P` over elements of :g:`even`, it is enough to prove it for :g:`O`
   and to prove that if any natural number :g:`n` satisfies :g:`P` its double
   successor :g:`(S (S n))` satisfies also :g:`P`. This is analogous to the
   structural induction principle we got for :g:`nat`.

.. _parametrized-inductive-types:

Parameterized inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the previous example, each constructor introduces a different
instance of the predicate :g:`even`. In some cases, all the constructors
introduce the same generic instance of the inductive definition, in
which case, instead of an annotation, we use a context of parameters
which are :n:`@binder`\s shared by all the constructors of the definition.

Parameters differ from inductive type annotations in that the
conclusion of each type of constructor invokes the inductive type with
the same parameter values of its specification.

.. example::

   A typical example is the definition of polymorphic lists:

   .. coqtop:: all

      Inductive list (A:Set) : Set :=
      | nil : list A
      | cons : A -> list A -> list A.

   In the type of :g:`nil` and :g:`cons`, we write ":g:`list A`" and not
   just ":g:`list`". The constructors :g:`nil` and :g:`cons` have these types:

   .. coqtop:: all

      Check nil.
      Check cons.

   Observe that the destructors are also quantified with :g:`(A:Set)`, for example:

   .. coqtop:: all

      Check list_ind.

   Once again, the types of the constructor arguments and of the conclusion can be omitted:

   .. coqtop:: none

      Reset list.

   .. coqtop:: in

      Inductive list (A:Set) : Set := nil | cons (_:A) (_:list A).

.. note::
   + The constructor type can
     recursively invoke the inductive definition on an argument which is not
     the parameter itself.

     One can define :

     .. coqtop:: all

        Inductive list2 (A:Set) : Set :=
        | nil2 : list2 A
        | cons2 : A -> list2 (A*A) -> list2 A.

     that can also be written by specifying only the type of the arguments:

     .. coqtop:: all reset

        Inductive list2 (A:Set) : Set :=
        | nil2
        | cons2 (_:A) (_:list2 (A*A)).

     But the following definition will give an error:

     .. coqtop:: all

        Fail Inductive listw (A:Set) : Set :=
        | nilw : listw (A*A)
        | consw : A -> listw (A*A) -> listw (A*A).

     because the conclusion of the type of constructors should be :g:`listw A`
     in both cases.

   + A parameterized inductive definition can be defined using annotations
     instead of parameters but it will sometimes give a different (bigger)
     sort for the inductive definition and will produce a less convenient
     rule for case elimination.

.. flag:: Uniform Inductive Parameters

     When this flag is set (it is off by default),
     inductive definitions are abstracted over their parameters
     before type checking constructors, allowing to write:

     .. coqtop:: all

        Set Uniform Inductive Parameters.
        Inductive list3 (A:Set) : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.

     This behavior is essentially equivalent to starting a new section
     and using :cmd:`Context` to give the uniform parameters, like so
     (cf. :ref:`section-mechanism`):

     .. coqtop:: all reset

        Section list3.
        Context (A:Set).
        Inductive list3 : Set :=
        | nil3 : list3
        | cons3 : A -> list3 -> list3.
        End list3.

     For finer control, you can use a ``|`` between the uniform and
     the non-uniform parameters:

     .. coqtop:: in reset

        Inductive Acc {A:Type} (R:A->A->Prop) | (x:A) : Prop
          := Acc_in : (forall y, R y x -> Acc y) -> Acc x.

     The flag can then be seen as deciding whether the ``|`` is at the
     beginning (when the flag is unset) or at the end (when it is set)
     of the parameters when not explicitly given.

.. seealso::
   Section :ref:`inductive-definitions` and the :tacn:`induction` tactic.

.. _mutually_inductive_types:

Mutually defined inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. example:: Mutually defined inductive types

   A typical example of mutually inductive data types is trees and
   forests. We assume two types :g:`A` and :g:`B` that are given as variables. The types can
   be declared like this:

   .. coqtop:: in

      Parameters A B : Set.

      Inductive tree : Set := node : A -> forest -> tree

      with forest : Set :=
      | leaf : B -> forest
      | cons : tree -> forest -> forest.

   This declaration automatically generates eight induction principles. They are not the most
   general principles, but they correspond to each inductive part seen as a single inductive definition.

   To illustrate this point on our example, here are the types of :g:`tree_rec`
   and :g:`forest_rec`.

   .. coqtop:: all

      Check tree_rec.

      Check forest_rec.

   Assume we want to parameterize our mutual inductive definitions with the
   two type variables :g:`A` and :g:`B`, the declaration should be
   done as follows:

   .. coqdoc::

      Inductive tree (A B:Set) : Set := node : A -> forest A B -> tree A B

      with forest (A B:Set) : Set :=
      | leaf : B -> forest A B
      | cons : tree A B -> forest A B -> forest A B.

   Assume we define an inductive definition inside a section
   (cf. :ref:`section-mechanism`). When the section is closed, the variables
   declared in the section and occurring free in the declaration are added as
   parameters to the inductive definition.

.. seealso::
   A generic command :cmd:`Scheme` is useful to build automatically various
   mutual induction principles.

Private (matching) inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. attr:: private(matching)

   This attribute can be used to forbid the use of the :g:`match`
   construct on objects of this inductive type outside of the module
   where it is defined.  There is also a legacy syntax using the
   ``Private`` prefix (cf. :n:`@legacy_attr`).

   The main use case of private (matching) inductive types is to emulate
   quotient types / higher-order inductive types in projects such as
   the `HoTT library <https://github.com/HoTT/HoTT>`_.

.. example::

   .. coqtop:: all

      Module Foo.
      #[ private(matching) ] Inductive my_nat := my_O : my_nat | my_S : my_nat -> my_nat.
      Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).
      End Foo.
      Import Foo.
      Fail Check (fun x : my_nat => match x with my_O => true | my_S _ => false end).

Variants
~~~~~~~~

.. cmd:: Variant @variant_definition {* with @variant_definition }

   .. insertprodn variant_definition variant_definition

   .. prodn::
      variant_definition ::= @ident_decl {* @binder } {? %| {* @binder } } {? : @type } := {? %| } {+| @constructor } {? @decl_notations }

   The :cmd:`Variant` command is similar to the :cmd:`Inductive` command, except
   that it disallows recursive definition of types (for instance, lists cannot
   be defined using :cmd:`Variant`). No induction scheme is generated for
   this variant, unless the :flag:`Nonrecursive Elimination Schemes` flag is on.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

   .. exn:: The @num th argument of @ident must be @ident in @type.
      :undocumented:

.. _coinductive-types:

Co-inductive types
------------------

The objects of an inductive type are well-founded with respect to the
constructors of the type. In other words, such objects contain only a
*finite* number of constructors. Co-inductive types arise from relaxing
this condition, and admitting types whose objects contain an infinity of
constructors. Infinite objects are introduced by a non-ending (but
effective) process of construction, defined in terms of the constructors
of the type.

.. cmd:: CoInductive @inductive_definition {* with @inductive_definition }

   This command introduces a co-inductive type.
   The syntax of the command is the same as the command :cmd:`Inductive`.
   No principle of induction is derived from the definition of a co-inductive
   type, since such principles only make sense for inductive types.
   For co-inductive types, the only elimination principle is case analysis.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(monomorphic)`, :attr:`universes(template)`,
   :attr:`universes(notemplate)`, :attr:`universes(cumulative)`,
   :attr:`universes(noncumulative)` and :attr:`private(matching)`
   attributes.

.. example::

   The type of infinite sequences of natural numbers, usually called streams,
   is an example of a co-inductive type.

   .. coqtop:: in

      CoInductive Stream : Set := Seq : nat -> Stream -> Stream.

   The usual destructors on streams :g:`hd:Stream->nat` and :g:`tl:Str->Str`
   can be defined as follows:

   .. coqtop:: in

      Definition hd (x:Stream) := let (a,s) := x in a.
      Definition tl (x:Stream) := let (a,s) := x in s.

Definitions of co-inductive predicates and blocks of mutually
co-inductive definitions are also allowed.

.. example::

   The extensional equality on streams is an example of a co-inductive type:

   .. coqtop:: in

      CoInductive EqSt : Stream -> Stream -> Prop :=
        eqst : forall s1 s2:Stream,
                 hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

   In order to prove the extensional equality of two streams :g:`s1` and :g:`s2`
   we have to construct an infinite proof of equality, that is, an infinite
   object of type :g:`(EqSt s1 s2)`. We will see how to introduce infinite
   objects in Section :ref:`cofixpoint`.

Caveat
~~~~~~

The ability to define co-inductive types by constructors, hereafter called
*positive co-inductive types*, is known to break subject reduction. The story is
a bit long: this is due to dependent pattern-matching which implies
propositional η-equality, which itself would require full η-conversion for
subject reduction to hold, but full η-conversion is not acceptable as it would
make type-checking undecidable.

Since the introduction of primitive records in Coq 8.5, an alternative
presentation is available, called *negative co-inductive types*. This consists
in defining a co-inductive type as a primitive record type through its
projections. Such a technique is akin to the *co-pattern* style that can be
found in e.g. Agda, and preserves subject reduction.

The above example can be rewritten in the following way.

.. coqtop:: none

   Reset Stream.

.. coqtop:: all

   Set Primitive Projections.
   CoInductive Stream : Set := Seq { hd : nat; tl : Stream }.
   CoInductive EqSt (s1 s2: Stream) : Prop := eqst {
     eqst_hd : hd s1 = hd s2;
     eqst_tl : EqSt (tl s1) (tl s2);
   }.

Some properties that hold over positive streams are lost when going to the
negative presentation, typically when they imply equality over streams.
For instance, propositional η-equality is lost when going to the negative
presentation. It is nonetheless logically consistent to recover it through an
axiom.

.. coqtop:: all

   Axiom Stream_eta : forall s: Stream, s = Seq (hd s) (tl s).

More generally, as in the case of positive coinductive types, it is consistent
to further identify extensional equality of coinductive types with propositional
equality:

.. coqtop:: all

   Axiom Stream_ext : forall (s1 s2: Stream), EqSt s1 s2 -> s1 = s2.

As of Coq 8.9, it is now advised to use negative co-inductive types rather than
their positive counterparts.

.. seealso::
   :ref:`primitive_projections` for more information about negative
   records and primitive projections.


Definition of recursive functions
---------------------------------

Definition of functions by recursion over inductive objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This section describes the primitive form of definition by recursion over
inductive objects. See the :cmd:`Function` command for more advanced
constructions.

.. _Fixpoint:

.. cmd:: Fixpoint @fix_definition {* with @fix_definition }

   .. insertprodn fix_definition fix_definition

   .. prodn::
      fix_definition ::= @ident_decl {* @binder } {? @fixannot } {? : @type } {? := @term } {? @decl_notations }

   This command allows defining functions by pattern matching over inductive
   objects using a fixed point construction. The meaning of this declaration is
   to define :n:`@ident` as a recursive function with arguments specified by
   the :n:`@binder`\s such that :n:`@ident` applied to arguments
   corresponding to these :n:`@binder`\s has type :n:`@type`, and is
   equivalent to the expression :n:`@term`. The type of :n:`@ident` is
   consequently :n:`forall {* @binder }, @type` and its value is equivalent
   to :n:`fun {* @binder } => @term`.

   To be accepted, a :cmd:`Fixpoint` definition has to satisfy syntactical
   constraints on a special argument called the decreasing argument. They
   are needed to ensure that the :cmd:`Fixpoint` definition always terminates.
   The point of the :n:`{struct @ident}` annotation (see :n:`@fixannot`) is to
   let the user tell the system which argument decreases along the recursive calls.

   The :n:`{struct @ident}` annotation may be left implicit, in which case the
   system successively tries arguments from left to right until it finds one
   that satisfies the decreasing condition.

   :cmd:`Fixpoint` without the :attr:`program` attribute does not support the
   :n:`wf` or :n:`measure` clauses of :n:`@fixannot`.

   The :n:`with` clause allows simultaneously defining several mutual fixpoints.
   It is especially useful when defining functions over mutually defined
   inductive types.  Example: :ref:`Mutual Fixpoints<example_mutual_fixpoints>`.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

   .. note::

      + Some fixpoints may have several arguments that fit as decreasing
        arguments, and this choice influences the reduction of the fixpoint.
        Hence an explicit annotation must be used if the leftmost decreasing
        argument is not the desired one. Writing explicit annotations can also
        speed up type checking of large mutual fixpoints.

      + In order to keep the strong normalization property, the fixed point
        reduction will only be performed when the argument in position of the
        decreasing argument (which type should be in an inductive definition)
        starts with a constructor.


   .. example::

      One can define the addition function as :

      .. coqtop:: all

         Fixpoint add (n m:nat) {struct n} : nat :=
         match n with
         | O => m
         | S p => S (add p m)
         end.

      The match operator matches a value (here :g:`n`) with the various
      constructors of its (inductive) type. The remaining arguments give the
      respective values to be returned, as functions of the parameters of the
      corresponding constructor. Thus here when :g:`n` equals :g:`O` we return
      :g:`m`, and when :g:`n` equals :g:`(S p)` we return :g:`(S (add p m))`.

      The match operator is formally described in
      Section :ref:`match-construction`.
      The system recognizes that in the inductive call :g:`(add p m)` the first
      argument actually decreases because it is a *pattern variable* coming
      from :g:`match n with`.

   .. example::

      The following definition is not correct and generates an error message:

      .. coqtop:: all

         Fail Fixpoint wrongplus (n m:nat) {struct n} : nat :=
         match m with
         | O => n
         | S p => S (wrongplus n p)
         end.

      because the declared decreasing argument :g:`n` does not actually
      decrease in the recursive call. The function computing the addition over
      the second argument should rather be written:

      .. coqtop:: all

         Fixpoint plus (n m:nat) {struct m} : nat :=
         match m with
         | O => n
         | S p => S (plus n p)
         end.

   .. example::

      The recursive call may not only be on direct subterms of the recursive
      variable :g:`n` but also on a deeper subterm and we can directly write
      the function :g:`mod2` which gives the remainder modulo 2 of a natural
      number.

      .. coqtop:: all

         Fixpoint mod2 (n:nat) : nat :=
         match n with
         | O => O
         | S p => match p with
                  | O => S O
                  | S q => mod2 q
                  end
         end.

.. _example_mutual_fixpoints:

   .. example:: Mutual fixpoints

      The size of trees and forests can be defined the following way:

      .. coqtop:: all

         Fixpoint tree_size (t:tree) : nat :=
         match t with
         | node a f => S (forest_size f)
         end
         with forest_size (f:forest) : nat :=
         match f with
         | leaf b => 1
         | cons t f' => (tree_size t + forest_size f')
         end.

.. _cofixpoint:

Definitions of recursive objects in co-inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: CoFixpoint @cofix_definition {* with @cofix_definition }

   .. insertprodn cofix_definition cofix_definition

   .. prodn::
      cofix_definition ::= @ident_decl {* @binder } {? : @type } {? := @term } {? @decl_notations }

   This command introduces a method for constructing an infinite object of a
   coinductive type. For example, the stream containing all natural numbers can
   be introduced applying the following method to the number :g:`O` (see
   Section :ref:`coinductive-types` for the definition of :g:`Stream`, :g:`hd`
   and :g:`tl`):

   .. coqtop:: all

      CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).

   Unlike recursive definitions, there is no decreasing argument in a
   co-recursive definition. To be admissible, a method of construction must
   provide at least one extra constructor of the infinite object for each
   iteration. A syntactical guard condition is imposed on co-recursive
   definitions in order to ensure this: each recursive call in the
   definition must be protected by at least one constructor, and only by
   constructors. That is the case in the former definition, where the single
   recursive call of :g:`from` is guarded by an application of :g:`Seq`.
   On the contrary, the following recursive function does not satisfy the
   guard condition:

   .. coqtop:: all

      Fail CoFixpoint filter (p:nat -> bool) (s:Stream) : Stream :=
        if p (hd s) then Seq (hd s) (filter p (tl s)) else filter p (tl s).

   The elimination of co-recursive definition is done lazily, i.e. the
   definition is expanded only when it occurs at the head of an application
   which is the argument of a case analysis expression. In any other
   context, it is considered as a canonical expression which is completely
   evaluated. We can test this using the command :cmd:`Eval`, which computes
   the normal forms of a term:

   .. coqtop:: all

      Eval compute in (from 0).
      Eval compute in (hd (from 0)).
      Eval compute in (tl (from 0)).

   As in the :cmd:`Fixpoint` command, the :n:`with` clause allows simultaneously
   defining several mutual cofixpoints.

   If :n:`@term` is omitted, :n:`@type` is required and Coq enters proof editing mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a constant
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.

.. _Computations:

Computations
------------

.. insertprodn reduce pattern_occ

.. prodn::
   reduce ::= Eval @red_expr in
   red_expr ::= red
   | hnf
   | simpl {? @delta_flag } {? @ref_or_pattern_occ }
   | cbv {? @strategy_flag }
   | cbn {? @strategy_flag }
   | lazy {? @strategy_flag }
   | compute {? @delta_flag }
   | vm_compute {? @ref_or_pattern_occ }
   | native_compute {? @ref_or_pattern_occ }
   | unfold {+, @unfold_occ }
   | fold {+ @one_term }
   | pattern {+, @pattern_occ }
   | @ident
   delta_flag ::= {? - } [ {+ @smart_qualid } ]
   strategy_flag ::= {+ @red_flags }
   | @delta_flag
   red_flags ::= beta
   | iota
   | match
   | fix
   | cofix
   | zeta
   | delta {? @delta_flag }
   ref_or_pattern_occ ::= @smart_qualid {? at @occs_nums }
   | @one_term {? at @occs_nums }
   occs_nums ::= {+ {| @num | @ident } }
   | - {| @num | @ident } {* @int_or_var }
   int_or_var ::= @int
   | @ident
   unfold_occ ::= @smart_qualid {? at @occs_nums }
   pattern_occ ::= @one_term {? at @occs_nums }

See :ref:`Conversion-rules`.

.. todo:: Add text here

.. _Assertions:

Assertions and proofs
---------------------

An assertion states a proposition (or a type) of which the proof (or an
inhabitant of the type) is interactively built using tactics. The interactive
proof mode is described in Chapter :ref:`proofhandling` and the tactics in
Chapter :ref:`Tactics`. The basic assertion command is:

.. cmd:: @thm_token @ident_decl {* @binder } : @type {* with @ident_decl {* @binder } : @type }
   :name: Theorem; Lemma; Fact; Remark; Corollary; Proposition; Property

   .. insertprodn thm_token thm_token

   .. prodn::
      thm_token ::= Theorem
      | Lemma
      | Fact
      | Remark
      | Corollary
      | Proposition
      | Property

   After the statement is asserted, Coq needs a proof. Once a proof of
   :n:`@type` under the assumptions represented by :n:`@binder`\s is given and
   validated, the proof is generalized into a proof of :n:`forall {* @binder }, @type` and
   the theorem is bound to the name :n:`@ident` in the environment.

   Forms using the :n:`with` clause are useful for theorems that are proved by simultaneous induction
   over a mutually inductive assumption, or that assert mutually dependent
   statements in some mutual co-inductive type. It is equivalent to
   :cmd:`Fixpoint` or :cmd:`CoFixpoint` but using tactics to build the proof of
   the statements (or the body of the specification, depending on the point of
   view). The inductive or co-inductive types on which the induction or
   coinduction has to be done is assumed to be non ambiguous and is guessed by
   the system.

   Like in a :cmd:`Fixpoint` or :cmd:`CoFixpoint` definition, the induction hypotheses
   have to be used on *structurally smaller* arguments (for a :cmd:`Fixpoint`) or
   be *guarded by a constructor* (for a :cmd:`CoFixpoint`). The verification that
   recursive proof arguments are correct is done only at the time of registering
   the lemma in the environment. To know if the use of induction hypotheses is
   correct at some time of the interactive development of a proof, use the
   command :cmd:`Guarded`.

   .. exn:: The term @term has type @type which should be Set, Prop or Type.
      :undocumented:

   .. exn:: @ident already exists.
      :name: @ident already exists. (Theorem)

      The name you provided is already defined. You have then to choose
      another name.

   .. exn:: Nested proofs are not allowed unless you turn the Nested Proofs Allowed flag on.

      You are asserting a new statement while already being in proof editing mode.
      This feature, called nested proofs, is disabled by default.
      To activate it, turn the :flag:`Nested Proofs Allowed` flag on.

Proofs start with the keyword :cmd:`Proof`. Then Coq enters the proof editing mode
until the proof is completed. In proof editing mode, the user primarily enters
tactics, which are described in chapter :ref:`Tactics`. The user may also enter
commands to manage the proof editing mode. They are described in Chapter
:ref:`proofhandling`.

When the proof is complete, use the :cmd:`Qed` command so the kernel verifies
the proof and adds it to the environment.

.. note::

   #. Several statements can be simultaneously asserted provided the
      :flag:`Nested Proofs Allowed` flag was turned on.

   #. Not only other assertions but any vernacular command can be given
      while in the process of proving a given assertion. In this case, the
      command is understood as if it would have been given before the
      statements still to be proved. Nonetheless, this practice is discouraged
      and may stop working in future versions.

   #. Proofs ended by :cmd:`Qed` are declared opaque. Their content cannot be
      unfolded (see :ref:`performingcomputations`), thus
      realizing some form of *proof-irrelevance*. To be able to unfold a
      proof, the proof should be ended by :cmd:`Defined`.

   #. :cmd:`Proof` is recommended but can currently be omitted. On the opposite
      side, :cmd:`Qed` (or :cmd:`Defined`) is mandatory to validate a proof.

   #. One can also use :cmd:`Admitted` in place of :cmd:`Qed` to turn the
      current asserted statement into an axiom and exit the proof editing mode.

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

.. attr:: deprecated ( {? since = @string , } {? note = @string } )
   :name: deprecated

    At least one of :n:`since` or :n:`note` must be present.  If both are present,
    either one may appear first and they must be separated by a comma.

    This attribute is supported by the following commands: :cmd:`Ltac`,
    :cmd:`Tactic Notation`, :cmd:`Notation`, :cmd:`Infix`.

    It can trigger the following warnings:

    .. warn:: Tactic @qualid is deprecated since @string__since. @string__note.
              Tactic Notation @qualid is deprecated since @string__since. @string__note.
              Notation @string is deprecated since @string__since. @string__note.

       :n:`@qualid` or :n:`@string` is the notation, :n:`@string__since` is the version number,
       :n:`@string__note` is the note (usually explains the replacement).

    .. example::

       .. coqtop:: all reset warn

          #[deprecated(since="8.9.0", note="Use idtac instead.")]
          Ltac foo := idtac.

          Goal True.
          Proof.
          now foo.
          Abort.

.. warn:: Unsupported attribute

   This warning is an error by default. It is caused by using a
   command with some attribute it does not understand.

.. [1]
   Except if the inductive type is empty in which case there is no
   equation that can be used to infer the return type.
