.. _BNF-syntax:

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


About the grammars in the manual
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


Lexical conventions
===================

Blanks
  Space, newline and horizontal tabulation are considered as blanks.
  Blanks are ignored but they separate tokens.

Comments
  Comments in Coq are enclosed between ``(*`` and ``*)``, and can be nested.
  They can contain any character. However, string literals must be
  correctly closed. Comments are treated as blanks.

Identifiers and access identifiers
  Identifiers, written ident, are sequences of letters, digits, ``_`` and
  ``'``, that do not start with a digit or ``'``. That is, they are
  recognized by the following lexical class:

  .. productionlist:: coq
     first_letter      : a..z ∣ A..Z ∣ _ ∣ unicode-letter
     subsequent_letter : a..z ∣ A..Z ∣ 0..9 ∣ _ ∣ ' ∣ unicode-letter ∣ unicode-id-part
     ident             : `first_letter` [`subsequent_letter` … `subsequent_letter`]
     access_ident      : . `ident`

  All characters are meaningful. In particular, identifiers are case-
  sensitive. The entry ``unicode-letter`` non-exhaustively includes Latin,
  Greek, Gothic, Cyrillic, Arabic, Hebrew, Georgian, Hangul, Hiragana
  and Katakana characters, CJK ideographs, mathematical letter-like
  symbols, hyphens, non-breaking space, … The entry ``unicode-id-part`` non-
  exhaustively includes symbols for prime letters and subscripts.

  Access identifiers, written :token:`access_ident`, are identifiers prefixed by
  `.` (dot) without blank. They are used in the syntax of qualified
  identifiers.

Natural numbers and integers
  Numerals are sequences of digits. Integers are numerals optionally
  preceded by a minus sign.

  .. productionlist:: coq
     digit   : 0..9
     num     : `digit` … `digit`
     integer : [-] `num`

Strings
  Strings are delimited by ``"`` (double quote), and enclose a sequence of
  any characters different from ``"`` or the sequence ``""`` to denote the
  double quote character. In grammars, the entry for quoted strings is
  :production:`string`.

Keywords
  The following identifiers are reserved keywords, and cannot be
  employed otherwise::

    _ as at cofix else end exists exists2 fix for
    forall fun if IF in let match mod Prop return
    Set then Type using where with

Special tokens
  The following sequences of characters are special tokens::

    ! % & && ( () ) * + ++ , - -> . .( ..
    / /\ : :: :< := :> ; < <- <-> <: <= <> =
    => =_D > >-> >= ? ?= @ [ \/ ] ^ { | |-
    || } ~

  Lexical ambiguities are resolved according to the “longest match”
  rule: when a sequence of non alphanumerical characters can be
  decomposed into several different ways, then the first token is the
  longest possible one (among all tokens defined at this moment), and so
  on.

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

.. productionlist:: coq
   term             : forall `binders` , `term`
                    : | fun `binders` => `term`
                    : | fix `fix_bodies`
                    : | cofix `cofix_bodies`
                    : | let `ident` [`binders`] [: `term`] := `term` in `term`
                    : | let fix `fix_body` in `term`
                    : | let cofix `cofix_body` in `term`
                    : | let ( [`name` , … , `name`] ) [`dep_ret_type`] := `term` in `term`
                    : | let ' `pattern` [in `term`] := `term` [`return_type`] in `term`
                    : | if `term` [`dep_ret_type`] then `term` else `term`
                    : | `term` : `term`
                    : | `term` <: `term`
                    : | `term` :>
                    : | `term` -> `term`
                    : | `term` arg … arg
                    : | @ `qualid` [`term` … `term`]
                    : | `term` % `ident`
                    : | match `match_item` , … , `match_item` [`return_type`] with
                    :   [[|] `equation` | … | `equation`] end
                    : | `qualid`
                    : | `sort`
                    : | num
                    : | _
                    : | ( `term` )
   arg              : `term`
                    : | ( `ident` := `term` )
   binders          : `binder` … `binder`
   binder           : `name`
                    : | ( `name` … `name` : `term` )
                    : | ( `name` [: `term`] := `term` )
   name             : `ident` | _
   qualid           : `ident` | `qualid` `access_ident`
   sort             : Prop | Set | Type
   fix_bodies       : `fix_body`
                    : | `fix_body` with `fix_body` with … with `fix_body` for `ident`
   cofix_bodies     : `cofix_body`
                    : | `cofix_body` with `cofix_body` with … with `cofix_body` for `ident`
   fix_body         : `ident` `binders` [annotation] [: `term`] := `term`
   cofix_body       : `ident` [`binders`] [: `term`] := `term`
   annotation       : { struct `ident` }
   match_item       : `term` [as `name`] [in `qualid` [`pattern` … `pattern`]]
   dep_ret_type     : [as `name`] `return_type`
   return_type      : return `term`
   equation         : `mult_pattern` | … | `mult_pattern` => `term`
   mult_pattern     : `pattern` , … , `pattern`
   pattern          : `qualid` `pattern` … `pattern`
                    : | @ `qualid` `pattern` … `pattern`
                    : | `pattern` as `ident`
                    : | `pattern` % `ident`
                    : | `qualid`
                    : | _
                    : | num
                    : | ( `or_pattern` , … , `or_pattern` )
   or_pattern       : `pattern` | … | `pattern`


Types
-----

Coq terms are typed. Coq types are recognized by the same syntactic
class as :token`term`. We denote by :token:`type` the semantic subclass
of types inside the syntactic class :token:`term`.

Qualified identifiers and simple identifiers
--------------------------------------------

*Qualified identifiers* (:token:`qualid`) denote *global constants*
(definitions, lemmas, theorems, remarks or facts), *global variables*
(parameters or axioms), *inductive types* or *constructors of inductive
types*. *Simple identifiers* (or shortly :token:`ident`) are a syntactic subset
of qualified identifiers. Identifiers may also denote local *variables*,
what qualified identifiers do not.

Numerals
--------

Numerals have no definite semantics in the calculus. They are mere
notations that can be bound to objects through the notation mechanism
(see Chapter :ref:`syntaxextensionsandinterpretationscopes` for details).
Initially, numerals are bound to Peano’s representation of natural
numbers (see :ref:`datatypes`).

.. note::

   negative integers are not at the same level as :token:`num`, for this
   would make precedence unnatural.

Sorts
-----

There are three sorts :g:`Set`, :g:`Prop` and :g:`Type`.

-  :g:`Prop` is the universe of *logical propositions*. The logical propositions
   themselves are typing the proofs. We denote propositions by *form*.
   This constitutes a semantic subclass of the syntactic class :token:`term`.

-  :g:`Set` is is the universe of *program types* or *specifications*. The
   specifications themselves are typing the programs. We denote
   specifications by *specif*. This constitutes a semantic subclass of
   the syntactic class :token:`term`.

-  :g:`Type` is the type of :g:`Prop` and :g:`Set`

More on sorts can be found in Section :ref:`sorts`.

.. _binders:

Binders
-------

Various constructions such as :g:`fun`, :g:`forall`, :g:`fix` and :g:`cofix`
*bind* variables. A binding is represented by an identifier. If the binding
variable is not used in the expression, the identifier can be replaced by the
symbol :g:`_`. When the type of a bound variable cannot be synthesized by the
system, it can be specified with the notation ``(ident : type)``. There is also
a notation for a sequence of binding variables sharing the same type:
``(``:token:`ident`:math:`_1`…:token:`ident`:math:`_n` : :token:`type```)``. A
binder can also be any pattern prefixed by a quote, e.g. :g:`'(x,y)`.

Some constructions allow the binding of a variable to value. This is
called a “let-binder”. The entry :token:`binder` of the grammar accepts
either an assumption binder as defined above or a let-binder. The notation in
the latter case is ``(ident := term)``. In a let-binder, only one
variable can be introduced at the same time. It is also possible to give
the type of the variable as follows:
``(ident : term := term)``.

Lists of :token:`binder` are allowed. In the case of :g:`fun` and :g:`forall`,
it is intended that at least one binder of the list is an assumption otherwise
fun and forall gets identical. Moreover, parentheses can be omitted in
the case of a single sequence of bindings sharing the same type (e.g.:
:g:`fun (x y z : A) => t` can be shortened in :g:`fun x y z : A => t`).

Abstractions
------------

The expression ``fun ident : type => term`` defines the
*abstraction* of the variable :token:`ident`, of type :token:`type`, over the term
:token:`term`. It denotes a function of the variable :token:`ident` that evaluates to
the expression :token:`term` (e.g. :g:`fun x : A => x` denotes the identity
function on type :g:`A`). The keyword :g:`fun` can be followed by several
binders as given in Section :ref:`binders`. Functions over
several variables are equivalent to an iteration of one-variable
functions. For instance the expression
“fun :token:`ident`\ :math:`_{1}` … :token:`ident`\ :math:`_{n}` 
: :token:`type` => :token:`term`”
denotes the same function as “ fun :token:`ident`\
:math:`_{1}` : :token:`type` => … 
fun :token:`ident`\ :math:`_{n}` : :token:`type` => :token:`term`”. If
a let-binder occurs in
the list of binders, it is expanded to a let-in definition (see
Section :ref:`let-in`).

Products
--------

The expression :g:`forall ident : type, term` denotes the
*product* of the variable :token:`ident` of type :token:`type`, over the term :token:`term`.
As for abstractions, :g:`forall` is followed by a binder list, and products
over several variables are equivalent to an iteration of one-variable
products. Note that :token:`term` is intended to be a type.

If the variable :token:`ident` occurs in :token:`term`, the product is called
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

The expression :token:`term`\ :math:`_0` :token:`term`\ :math:`_1` denotes the
application of :token:`term`\ :math:`_0` to :token:`term`\ :math:`_1`.

The expression :token:`term`\ :math:`_0` :token:`term`\ :math:`_1` ...
:token:`term`\ :math:`_n` denotes the application of the term
:token:`term`\ :math:`_0` to the arguments :token:`term`\ :math:`_1` ... then
:token:`term`\ :math:`_n`. It is equivalent to ( … ( :token:`term`\ :math:`_0`
:token:`term`\ :math:`_1` ) … ) :token:`term`\ :math:`_n` : associativity is to the
left.

The notation ``(ident := term)`` for arguments is used for making
explicit the value of implicit arguments (see
Section :ref:`implicitarguments`).

Type cast
---------

The expression ``term : type`` is a type cast expression. It enforces
the type of :token:`term` to be :token:`type`.

``term <: type`` locally sets up the virtual machine for checking that
:token:`term` has type :token:`type`.

Inferable subterms
------------------

Expressions often contain redundant pieces of information. Subterms that can be
automatically inferred by Coq can be replaced by the symbol ``_`` and Coq will
guess the missing piece of information.

.. _let-in:

Let-in definitions
------------------

``let`` :token:`ident` := :token:`term`:math:`_1` in :token:`term`:math:`_2`
denotes the local binding of :token:`term`:math:`_1` to the variable
:token:`ident` in :token:`term`:math:`_2`. There is a syntactic sugar for let-in
definition of functions: ``let`` :token:`ident` :token:`binder`:math:`_1` …
:token:`binder`:math:`_n` := :token:`term`:math:`_1` in :token:`term`:math:`_2`
stands for ``let`` :token:`ident` := ``fun`` :token:`binder`:math:`_1` …
:token:`binder`:math:`_n` => :token:`term`:math:`_1` in :token:`term`:math:`_2`.

Definition by case analysis
---------------------------

Objects of inductive types can be destructurated by a case-analysis
construction called *pattern-matching* expression. A pattern-matching
expression is used to analyze the structure of an inductive objects and
to apply specific treatments accordingly.

This paragraph describes the basic form of pattern-matching. See
Section :ref:`extended pattern-matching` and Chapter :ref:`extendedpatternmatching` for the description
of the general form. The basic form of pattern-matching is characterized
by a single :token:`match_item` expression, a :token:`mult_pattern` restricted to a
single :token:`pattern` and :token:`pattern` restricted to the form
:token:`qualid` :token:`ident`.

The expression match :token:`term`:math:`_0` :token:`return_type` with
:token:`pattern`:math:`_1` => :token:`term`:math:`_1` :math:`|` … :math:`|`
:token:`pattern`:math:`_n` => :token:`term`:math:`_n` end, denotes a
:token:`pattern-matching` over the term :token:`term`:math:`_0` (expected to be
of an inductive type :math:`I`). The terms :token:`term`:math:`_1`\ …\
:token:`term`:math:`_n` are the :token:`branches` of the pattern-matching
expression. Each of :token:`pattern`:math:`_i` has a form :token:`qualid`
:token:`ident` where :token:`qualid` must denote a constructor. There should be
exactly one branch for every constructor of :math:`I`.

The :token:`return_type` expresses the type returned by the whole match
expression. There are several cases. In the *non dependent* case, all
branches have the same type, and the :token:`return_type` is the common type of
branches. In this case, :token:`return_type` can usually be omitted as it can be
inferred from the type of the branches [2]_.

In the *dependent* case, there are three subcases. In the first subcase,
the type in each branch may depend on the exact value being matched in
the branch. In this case, the whole pattern-matching itself depends on
the term being matched. This dependency of the term being matched in the
return type is expressed with an “as :token:`ident`” clause where :token:`ident`
is dependent in the return type. For instance, in the following example:

.. coqtop:: in

   Inductive bool : Type := true : bool | false : bool.
   Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : eq A x x.
   Inductive or (A:Prop) (B:Prop) : Prop :=
     | or_introl : A -> or A B
     | or_intror : B -> or A B.

   Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
     match b as x return or (eq bool x true) (eq bool x false) with
     | true => or_introl (eq bool true true) (eq bool true false)
       (eq_refl bool true)
     | false => or_intror (eq bool false true) (eq bool false false)
       (eq_refl bool false)
     end.

the branches have respective types or :g:`eq bool true true :g:`eq bool true
false` and or :g:`eq bool false true` :g:`eq bool false false` while the whole
pattern-matching expression has type or :g:`eq bool b true` :g:`eq bool b
false`, the identifier :g:`x` being used to represent the dependency. Remark
that when the term being matched is a variable, the as clause can be
omitted and the term being matched can serve itself as binding name in
the return type. For instance, the following alternative definition is
accepted and has the same meaning as the previous one.

.. coqtop:: in

   Definition bool_case (b:bool) : or (eq bool b true) (eq bool b false) :=
     match b return or (eq bool b true) (eq bool b false) with
     | true => or_introl (eq bool true true) (eq bool true false)
       (eq_refl bool true)
     | false => or_intror (eq bool false true) (eq bool false false)
       (eq_refl bool false)
   end.

The second subcase is only relevant for annotated inductive types such
as the equality predicate (see Section :ref:`Equality`),
the order predicate on natural numbers or the type of lists of a given
length (see Section :ref:`listn`). In this configuration, the
type of each branch can depend on the type dependencies specific to the
branch and the whole pattern-matching expression has a type determined
by the specific dependencies in the type of the term being matched. This
dependency of the return type in the annotations of the inductive type
is expressed using a “in I _ ... _ :token:`pattern`:math:`_1` ...
:token:`pattern`:math:`_n`” clause, where

-  :math:`I` is the inductive type of the term being matched;

-  the :g:`_` are matching the parameters of the inductive type: the
   return type is not dependent on them.

-  the :token:`pattern`:math:`_i` are matching the annotations of the
   inductive type: the return type is dependent on them

-  in the basic case which we describe below, each :token:`pattern`:math:`_i`
   is a name :token:`ident`:math:`_i`; see :ref:`match-in-patterns` for the
   general case

For instance, in the following example:

.. coqtop:: in

   Definition eq_sym (A:Type) (x y:A) (H:eq A x y) : eq A y x :=
   match H in eq _ _ z return eq A z x with
   | eq_refl _ => eq_refl A x
   end.

the type of the branch has type :g:`eq A x x` because the third argument of
g:`eq` is g:`x` in the type of the pattern :g:`refl_equal`. On the contrary, the
type of the whole pattern-matching expression has type :g:`eq A y x` because the
third argument of eq is y in the type of H. This dependency of the case analysis
in the third argument of :g:`eq` is expressed by the identifier g:`z` in the
return type.

Finally, the third subcase is a combination of the first and second
subcase. In particular, it only applies to pattern-matching on terms in
a type with annotations. For this third subcase, both the clauses as and
in are available.

There are specific notations for case analysis on types with one or two
constructors: “if … then … else …” and “let (…, ” (see
Sections :ref:`if-then-else` and :ref:`Letin`).

Recursive functions
-------------------

The expression “fix :token:`ident`:math:`_1` :token:`binder`:math:`_1` :
:token:`type`:math:`_1` ``:=`` :token:`term`:math:`_1` with … with
:token:`ident`:math:`_n` :token:`binder`:math:`_n` : :token:`type`:math:`_n` ``:=``
:token:`term`:math:`_n` for :token:`ident`:math:`_i`” denotes the
:math:`i`\ component of a block of functions defined by mutual
well-founded recursion. It is the local counterpart of the ``Fixpoint``
command. See Section :ref:`Fixpoint` for more details. When
:math:`n=1`, the “for :token:`ident`:math:`_i`” clause is omitted.

The expression “cofix :token:`ident`:math:`_1` :token:`binder`:math:`_1` :
:token:`type`:math:`_1` with … with :token:`ident`:math:`_n` :token:`binder`:math:`_n`
: :token:`type`:math:`_n` for :token:`ident`:math:`_i`” denotes the
:math:`i`\ component of a block of terms defined by a mutual guarded
co-recursion. It is the local counterpart of the ``CoFixpoint`` command. See
Section :ref:`CoFixpoint` for more details. When
:math:`n=1`, the “ for :token:`ident`:math:`_i`” clause is omitted.

The association of a single fixpoint and a local definition have a special
syntax: “let fix f … := … in …” stands for “let f := fix f … := … in …”. The
same applies for co-fixpoints.

.. _vernacular:

The Vernacular
==============

.. productionlist:: coq
   sentence           : `assumption`
                      : | `definition`
                      : | `inductive`
                      : | `fixpoint`
                      : | `assertion` `proof`
   assumption         : `assumption_keyword` `assums`.
   assumption_keyword : Axiom | Conjecture
                      : | Parameter | Parameters
                      : | Variable | Variables
                      : | Hypothesis | Hypotheses
   assums             : `ident` … `ident` : `term`
                      : | ( `ident` … `ident` : `term` ) … ( `ident` … `ident` : `term` )
   definition         : [Local] Definition `ident` [`binders`] [: `term`] := `term` .
                      : | Let `ident` [`binders`] [: `term`] := `term` .
   inductive          : Inductive `ind_body` with … with `ind_body` .
                      : | CoInductive `ind_body` with … with `ind_body` .
   ind_body           : `ident` [`binders`] : `term` :=
                      : [[|] `ident` [`binders`] [:`term`] | … | `ident` [`binders`] [:`term`]]
   fixpoint           : Fixpoint `fix_body` with … with `fix_body` .
                      : | CoFixpoint `cofix_body` with … with `cofix_body` .
   assertion          : `assertion_keyword` `ident` [`binders`] : `term` .
   assertion_keyword  : Theorem | Lemma
                      : | Remark | Fact
                      : | Corollary | Proposition
                      : | Definition | Example
   proof              : Proof . … Qed .
                      : | Proof . … Defined .
                      : | Proof . … Admitted .

.. todo:: This use of … in this grammar is inconsistent

This grammar describes *The Vernacular* which is the language of
commands of Gallina. A sentence of the vernacular language, like in
many natural languages, begins with a capital letter and ends with a
dot.

The different kinds of command are described hereafter. They all suppose
that the terms occurring in the sentences are well-typed.

Assumptions
-----------

Assumptions extend the environment with axioms, parameters, hypotheses
or variables. An assumption binds an :token:`ident` to a :token:`type`. It is accepted
by Coq if and only if this :token:`type` is a correct type in the environment
preexisting the declaration and if :token:`ident` was not previously defined in
the same module. This :token:`type` is considered to be the type (or
specification, or statement) assumed by :token:`ident` and we say that :token:`ident`
has type :token:`type`.

.. cmd:: Axiom @ident : @term.

   This command links *term* to the name *ident* as its specification in
   the global context. The fact asserted by *term* is thus assumed as a
   postulate.

.. exn:: @ident already exists

.. cmdv:: Parameter @ident : @term.

   Is equivalent to ``Axiom`` :token:`ident` : :token:`term`

.. cmdv:: Parameter {+ @ident } : @term.

   Adds parameters with specification :token:`term`

.. cmdv:: Parameter {+ ( {+ @ident } : @term ) }.

   Adds blocks of parameters with different specifications.

.. cmdv:: Parameters {+ ( {+ @ident } : @term ) }.

   Synonym of ``Parameter``.

.. cmdv:: Local Axiom @ident : @term.

   Such axioms are never made accessible through their unqualified
   name by ``Import`` and its variants (see :ref:`Import`). You
   have to explicitly give their fully qualified name to refer to
   them.

.. cmdv:: Conjecture @ident : @term

   Is equivalent to ``Axiom`` :token:`ident` : :token:`term`.

.. cmd:: Variable @ident : @term.

This command links :token:`term` to the name :token:`ident` in the context of
the current section (see Section :ref:`Section` for a description of the section
mechanism). When the current section is closed, name :token:`ident` will be
unknown and every object using this variable will be explicitly parametrized
(the variable is *discharged*). Using the ``Variable`` command out of any
section is equivalent to using ``Local Parameter``.

.. exn:: @ident already exists

.. cmdv:: Variable {+ @ident } : @term.

   Links :token:`term` to each :token:`ident`.

.. cmdv:: Variable {+ ( {+ @ident } : @term) }.

   Adds blocks of variables with different specifications.

.. cmdv:: Variables {+ ( {+ @ident } : @term) }.

.. cmdv:: Hypothesis {+ ( {+ @ident } : @term) }.

.. cmdv:: Hypotheses {+ ( {+ @ident } : @term) }.

Synonyms of ``Variable``.

It is advised to use the keywords ``Axiom`` and ``Hypothesis`` for
logical postulates (i.e. when the assertion *term* is of sort ``Prop``),
and to use the keywords ``Parameter`` and ``Variable`` in other cases
(corresponding to the declaration of an abstract mathematical entity).

.. _gallina_def:

Definitions
-----------

Definitions extend the environment with associations of names to terms.
A definition can be seen as a way to give a meaning to a name or as a
way to abbreviate a term. In any case, the name can later be replaced at
any time by its definition.

The operation of unfolding a name into its definition is called
:math:`\delta`-conversion (see Section :ref:`delta`). A
definition is accepted by the system if and only if the defined term is
well-typed in the current context of the definition and if the name is
not already used. The name defined by the definition is called a
*constant* and the term it refers to is its *body*. A definition has a
type which is the type of its body.

A formal presentation of constants and environments is given in
Section :ref:`Typed-terms`.

.. cmd:: Definition @ident := @term.

   This command binds :token:`term` to the name :token:`ident` in the environment,
   provided that :token:`term` is well-typed.

.. exn:: @ident already exists

.. cmdv:: Definition @ident : @term := @term.

   It checks that the type of :token:`term`:math:`_2` is definitionally equal to
   :token:`term`:math:`_1`, and registers :token:`ident` as being of type
   :token:`term`:math:`_1`, and bound to value :token:`term`:math:`_2`.


.. cmdv:: Definition @ident {* @binder } : @term := @term.

   This is equivalent to ``Definition`` :token:`ident` : :g:`forall`
   :token:`binder`:math:`_1` … :token:`binder`:math:`_n`, :token:`term`:math:`_1` := 
   fun :token:`binder`:math:`_1` …
   :token:`binder`:math:`_n` => :token:`term`:math:`_2`.

.. cmdv:: Local Definition @ident := @term.

   Such definitions are never made accessible through their
   unqualified name by Import and its variants (see :ref:`Import`).
   You have to explicitly give their fully qualified name to refer to them.

.. cmdv:: Example @ident := @term.

.. cmdv:: Example @ident : @term := @term.

.. cmdv:: Example @ident {* @binder } : @term := @term.

These are synonyms of the Definition forms.

.. exn:: The term @term has type @type while it is expected to have type @type

See also Sections :ref:`Opaque,Transparent,unfold`.

.. cmd:: Let @ident := @term.

This command binds the value :token:`term` to the name :token:`ident` in the
environment of the current section. The name :token:`ident` disappears when the
current section is eventually closed, and, all persistent objects (such
as theorems) defined within the section and depending on :token:`ident` are
prefixed by the let-in definition ``let`` :token:`ident` ``:=`` :token:`term`
``in``. Using the ``Let`` command out of any section is equivalent to using
``Local Definition``.

.. exn:: @ident already exists

.. cmdv:: Let @ident : @term := @term.

.. cmdv:: Let Fixpoint @ident @fix_body {* with @fix_body}.

.. cmdv:: Let CoFixpoint @ident @cofix_body {* with @cofix_body}.

See also Sections :ref:`Section,Opaque,Transparent,unfold`.

Inductive definitions
---------------------

We gradually explain simple inductive types, simple annotated inductive
types, simple parametric inductive types, mutually inductive types. We
explain also co-inductive types.

Simple inductive types
~~~~~~~~~~~~~~~~~~~~~~

The definition of a simple inductive type has the following form:

.. cmd:: Inductive @ident : @sort := {? | } @ident : @type {* | @ident : @type }

The name :token:`ident` is the name of the inductively defined type and
:token:`sort` is the universes where it lives. The :token:`ident` are the names
of its constructors and :token:`type` their respective types. The types of the
constructors have to satisfy a *positivity condition* (see Section
:ref:`Positivity`) for :token:`ident`. This condition ensures the soundness of
the inductive definition. If this is the case, the :token:`ident` are added to
the environment with their respective types. Accordingly to the universe where
the inductive type lives (e.g. its type :token:`sort`), Coq provides a number of
destructors for :token:`ident`. Destructors are named ``ident_ind``,
``ident_rec`` or ``ident_rect`` which respectively correspond to
elimination principles on :g:`Prop`, :g:`Set` and :g:`Type`. The type of the
destructors expresses structural induction/recursion principles over objects of
:token:`ident`. We give below two examples of the use of the Inductive
definitions.

The set of natural numbers is defined as:

.. coqtop:: all

   Inductive nat : Set :=
   | O : nat
   | S : nat -> nat.

The type nat is defined as the least :g:`Set` containing :g:`O` and closed by
the :g:`S` constructor. The names :g:`nat`, :g:`O` and :g:`S` are added to the
environment.

Now let us have a look at the elimination principles. They are three of them:
:g:`nat_ind`, :g:`nat_rec` and :g:`nat_rect`. The type of :g:`nat_ind` is:

.. coqtop:: all

   Check nat_ind.

This is the well known structural induction principle over natural
numbers, i.e. the second-order form of Peano’s induction principle. It
allows proving some universal property of natural numbers (:g:`forall
n:nat, P n`) by induction on :g:`n`.

The types of :g:`nat_rec` and :g:`nat_rect` are similar, except that they pertain
to :g:`(P:nat->Set)` and :g:`(P:nat->Type)` respectively. They correspond to
primitive induction principles (allowing dependent types) respectively
over sorts ``Set`` and ``Type``. The constant ``ident_ind`` is always
provided, whereas ``ident_rec`` and ``ident_rect`` can be impossible
to derive (for example, when :token:`ident` is a proposition).

.. coqtop:: in

   Inductive nat : Set := O | S (_:nat).

In the case where inductive types have no annotations (next section
gives an example of such annotations), a constructor can be defined
by only giving the type of its arguments.

Simple annotated inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In an annotated inductive types, the universe where the inductive type
is defined is no longer a simple sort, but what is called an arity,
which is a type whose conclusion is a sort.

As an example of annotated inductive types, let us define the
:g:`even` predicate:

.. coqtop:: all

   Inductive even : nat -> Prop :=
   | even_0 : even O
   | even_SS : forall n:nat, even n -> even (S (S n)).

The type :g:`nat->Prop` means that even is a unary predicate (inductively
defined) over natural numbers. The type of its two constructors are the
defining clauses of the predicate even. The type of :g:`even_ind` is:

.. coqtop:: all

   Check even_ind.

From a mathematical point of view it asserts that the natural numbers satisfying
the predicate even are exactly in the smallest set of naturals satisfying the
clauses :g:`even_0` or :g:`even_SS`. This is why, when we want to prove any
predicate :g:`P` over elements of :g:`even`, it is enough to prove it for :g:`O`
and to prove that if any natural number :g:`n` satisfies :g:`P` its double
successor :g:`(S (S n))` satisfies also :g:`P`. This is indeed analogous to the
structural induction principle we got for :g:`nat`.

.. exn:: Non strictly positive occurrence of @ident in @type

.. exn:: The conclusion of @type is not valid; it must be built from @ident

Parametrized inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the previous example, each constructor introduces a different
instance of the predicate even. In some cases, all the constructors
introduces the same generic instance of the inductive definition, in
which case, instead of an annotation, we use a context of parameters
which are binders shared by all the constructors of the definition.

The general scheme is:

.. cmdv:: Inductive @ident {+ @binder} : @term := {? | } @ident : @type {* | @ident : @type}

Parameters differ from inductive type annotations in the fact that the
conclusion of each type of constructor :g:`term` invoke the inductive type with
the same values of parameters as its specification.

A typical example is the definition of polymorphic lists:

.. coqtop:: in

   Inductive list (A:Set) : Set :=
   | nil : list A
   | cons : A -> list A -> list A.

.. note::

   In the type of :g:`nil` and :g:`cons`, we write :g:`(list A)` and not
   just :g:`list`. The constructors :g:`nil` and :g:`cons` will have respectively
   types:

   .. coqtop:: all

      Check nil.
      Check cons.

   Types of destructors are also quantified with :g:`(A:Set)`.

Variants
++++++++

.. coqtop:: in

   Inductive list (A:Set) : Set := nil | cons (_:A) (_:list A).

This is an alternative definition of lists where we specify the
arguments of the constructors rather than their full type.

.. coqtop:: in

   Variant sum (A B:Set) : Set := left : A -> sum A B | right : B -> sum A B.

The ``Variant`` keyword is identical to the ``Inductive`` keyword, except
that it disallows recursive definition of types (in particular lists cannot
be defined with the Variant keyword). No induction scheme is generated for
this variant, unless the option ``Nonrecursive Elimination Schemes`` is set
(see :ref:`set-nonrecursive-elimination-schemes`).

.. exn:: The @num th argument of @ident must be @ident in @type

New from Coq V8.1
+++++++++++++++++

The condition on parameters for inductive definitions has been relaxed
since Coq V8.1. It is now possible in the type of a constructor, to
invoke recursively the inductive definition on an argument which is not
the parameter itself.

One can define :

.. coqtop:: all

   Inductive list2 (A:Set) : Set :=
   | nil2 : list2 A
   | cons2 : A -> list2 (A*A) -> list2 A.

that can also be written by specifying only the type of the arguments:

.. coqtop:: all reset

   Inductive list2 (A:Set) : Set := nil2 | cons2 (_:A) (_:list2 (A*A)).

But the following definition will give an error:

.. coqtop:: all

   Fail Inductive listw (A:Set) : Set :=
   | nilw : listw (A*A)
   | consw : A -> listw (A*A) -> listw (A*A).

Because the conclusion of the type of constructors should be :g:`listw A` in
both cases.

A parametrized inductive definition can be defined using annotations
instead of parameters but it will sometimes give a different (bigger)
sort for the inductive definition and will produce a less convenient
rule for case elimination.

See also Sections :ref:`Cic-inductive-definitions,Tac-induction`.

Mutually defined inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The definition of a block of mutually inductive types has the form:

.. cmdv:: Inductive @ident : @term := {? | } @ident : @type {* | @ident : @type } {* with @ident : @term := {? | } @ident : @type {* | @ident : @type }}.

It has the same semantics as the above ``Inductive`` definition for each
:token:`ident` All :token:`ident` are simultaneously added to the environment.
Then well-typing of constructors can be checked. Each one of the :token:`ident`
can be used on its own.

It is also possible to parametrize these inductive definitions. However,
parameters correspond to a local context in which the whole set of
inductive declarations is done. For this reason, the parameters must be
strictly the same for each inductive types The extended syntax is:

.. cmdv:: Inductive @ident {+ @binder} : @term := {? | } @ident : @type {* | @ident : @type } {* with @ident {+ @binder} : @term := {? | } @ident : @type {* | @ident : @type }}.

The typical example of a mutual inductive data type is the one for trees and
forests. We assume given two types :g:`A` and :g:`B` as variables. It can
be declared the following way.

.. coqtop:: in

   Variables A B : Set.

   Inductive tree : Set :=
     node : A -> forest -> tree

   with forest : Set :=
   | leaf : B -> forest
   | cons : tree -> forest -> forest.

This declaration generates automatically six induction principles. They are
respectively called :g:`tree_rec`, :g:`tree_ind`, :g:`tree_rect`,
:g:`forest_rec`, :g:`forest_ind`, :g:`forest_rect`. These ones are not the most
general ones but are just the induction principles corresponding to each
inductive part seen as a single inductive definition.

To illustrate this point on our example, we give the types of :g:`tree_rec`
and :g:`forest_rec`.

.. coqtop:: all

   Check tree_rec.

   Check forest_rec.

Assume we want to parametrize our mutual inductive definitions with the
two type variables :g:`A` and :g:`B`, the declaration should be
done the following way:

.. coqtop:: in

   Inductive tree (A B:Set) : Set :=
     node : A -> forest A B -> tree A B

   with forest (A B:Set) : Set :=
     | leaf : B -> forest A B
     | cons : tree A B -> forest A B -> forest A B.

Assume we define an inductive definition inside a section. When the
section is closed, the variables declared in the section and occurring
free in the declaration are added as parameters to the inductive
definition.

See also Section :ref:`Section`.

Co-inductive types
~~~~~~~~~~~~~~~~~~

The objects of an inductive type are well-founded with respect to the
constructors of the type. In other words, such objects contain only a
*finite* number of constructors. Co-inductive types arise from relaxing
this condition, and admitting types whose objects contain an infinity of
constructors. Infinite objects are introduced by a non-ending (but
effective) process of construction, defined in terms of the constructors
of the type.

An example of a co-inductive type is the type of infinite sequences of
natural numbers, usually called streams. It can be introduced in
Coq using the ``CoInductive`` command:

.. coqtop:: all

   CoInductive Stream : Set :=
     Seq : nat -> Stream -> Stream.

The syntax of this command is the same as the command ``Inductive`` (see
Section :ref:`gal-Inductive-Definitions`. Notice that no principle of induction
is derived from the definition of a co-inductive type, since such principles
only make sense for inductive ones. For co-inductive ones, the only elimination
principle is case analysis. For example, the usual destructors on streams
:g:`hd:Stream->nat` and :g:`tl:Str->Str` can be defined as follows:

.. coqtop:: all

   Definition hd (x:Stream) := let (a,s) := x in a.
   Definition tl (x:Stream) := let (a,s) := x in s.

Definition of co-inductive predicates and blocks of mutually
co-inductive definitions are also allowed. An example of a co-inductive
predicate is the extensional equality on streams:

.. coqtop:: all

   CoInductive EqSt : Stream -> Stream -> Prop :=
     eqst : forall s1 s2:Stream,
              hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

In order to prove the extensionally equality of two streams :g:`s1` and :g:`s2`
we have to construct an infinite proof of equality, that is, an infinite object
of type :g:`(EqSt s1 s2)`. We will see how to introduce infinite objects in
Section :ref:`CoFixpoint`.

Definition of recursive functions
---------------------------------

Definition of functions by recursion over inductive objects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This section describes the primitive form of definition by recursion over
inductive objects. See Section :ref:`Function` for more advanced constructions.
The command:

.. cmd:: Fixpoint @ident @params {struct @ident} : @type := @term.

allows defining functions by pattern-matching over inductive objects
using a fixed point construction. The meaning of this declaration is to
define :token:`ident` a recursive function with arguments specified by the
binders in :token:`params` such that :token:`ident` applied to arguments corresponding
to these binders has type :token:`type`:math:`_0`, and is equivalent to the
expression :token:`term`:math:`_0`. The type of the :token:`ident` is consequently
:g:`forall` :token:`params`, :token:`type`:math:`_0` and the value is equivalent to
:g:`fun` :token:`params` :g:`=>` :token:`term`:math:`_0`.

To be accepted, a ``Fixpoint`` definition has to satisfy some syntactical
constraints on a special argument called the decreasing argument. They
are needed to ensure that the Fixpoint definition always terminates. The
point of the {struct :token:`ident`} annotation is to let the user tell the
system which argument decreases along the recursive calls. For instance,
one can define the addition function as :

.. coqtop:: all

   Fixpoint add (n m:nat) {struct n} : nat :=
   match n with
   | O => m
   | S p => S (add p m)
   end.

The ``{struct`` :token:`ident```}`` annotation may be left implicit, in this case the
system try successively arguments from left to right until it finds one that
satisfies the decreasing condition.

.. note::

   Some fixpoints may have several arguments that fit as decreasing
   arguments, and this choice influences the reduction of the fixpoint. Hence an
   explicit annotation must be used if the leftmost decreasing argument is not the
   desired one. Writing explicit annotations can also speed up type-checking of
   large mutual fixpoints.

The match operator matches a value (here :g:`n`) with the various
constructors of its (inductive) type. The remaining arguments give the
respective values to be returned, as functions of the parameters of the
corresponding constructor. Thus here when :g:`n` equals :g:`O` we return
:g:`m`, and when :g:`n` equals :g:`(S p)` we return :g:`(S (add p m))`.

The match operator is formally described in detail in Section :ref:`Caseexpr`.
The system recognizes that in the inductive call :g:`(add p m)` the first
argument actually decreases because it is a *pattern variable* coming from
:g:`match n with`.

.. example::

  The following definition is not correct and generates an error message:

  .. coqtop:: all

     Fail Fixpoint wrongplus (n m:nat) {struct n} : nat :=
     match m with
     | O => n
     | S p => S (wrongplus n p)
     end.

  because the declared decreasing argument n actually does not decrease in
  the recursive call. The function computing the addition over the second
  argument should rather be written:

  .. coqtop:: all

     Fixpoint plus (n m:nat) {struct m} : nat :=
     match m with
     | O => n
     | S p => S (plus n p)
     end.

.. example::

  The ordinary match operation on natural numbers can be mimicked in the
  following way.

  .. coqtop:: all

     Fixpoint nat_match
       (C:Set) (f0:C) (fS:nat -> C -> C) (n:nat) {struct n} : C :=
     match n with
     | O => f0
     | S p => fS p (nat_match C f0 fS p)
     end.

.. example::

  The recursive call may not only be on direct subterms of the recursive
  variable n but also on a deeper subterm and we can directly write the
  function mod2 which gives the remainder modulo 2 of a natural number.

  .. coqtop:: all

     Fixpoint mod2 (n:nat) : nat :=
     match n with
     | O => O
     | S p => match p with
              | O => S O
              | S q => mod2 q
              end
     end.

In order to keep the strong normalization property, the fixed point
reduction will only be performed when the argument in position of the
decreasing argument (which type should be in an inductive definition)
starts with a constructor.

The ``Fixpoint`` construction enjoys also the with extension to define functions
over mutually defined inductive types or more generally any mutually recursive
definitions.

.. cmdv:: Fixpoint @ident @params {struct @ident} : @type := @term {* with @ident {+ @params} : @type := @term}.

allows to define simultaneously fixpoints.

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

A generic command Scheme is useful to build automatically various mutual
induction principles. It is described in Section :ref:`Scheme`.

Definitions of recursive objects in co-inductive types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. cmd:: CoFixpoint @ident : @type := @term.

introduces a method for constructing an infinite object of a coinductive
type. For example, the stream containing all natural numbers can be
introduced applying the following method to the number :ref:`O` (see
Section :ref:`CoInductiveTypes` for the definition of :g:`Stream`, :g:`hd` and
:g:`tl`):

.. coqtop:: all

   CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).

Oppositely to recursive ones, there is no decreasing argument in a
co-recursive definition. To be admissible, a method of construction must
provide at least one extra constructor of the infinite object for each
iteration. A syntactical guard condition is imposed on co-recursive
definitions in order to ensure this: each recursive call in the
definition must be protected by at least one constructor, and only by
constructors. That is the case in the former definition, where the
single recursive call of :g:`from` is guarded by an application of
:g:`Seq`. On the contrary, the following recursive function does not
satisfy the guard condition:

.. coqtop:: all

   Fail CoFixpoint filter (p:nat -> bool) (s:Stream) : Stream :=
     if p (hd s) then Seq (hd s) (filter p (tl s)) else filter p (tl s).

The elimination of co-recursive definition is done lazily, i.e. the
definition is expanded only when it occurs at the head of an application
which is the argument of a case analysis expression. In any other
context, it is considered as a canonical expression which is completely
evaluated. We can test this using the command ``Eval``, which computes
the normal forms of a term:

.. coqtop:: all

   Eval compute in (from 0).
   Eval compute in (hd (from 0)).
   Eval compute in (tl (from 0)).

.. cmdv:: CoFixpoint @ident @params : @type := @term

   As for most constructions, arguments of co-fixpoints expressions
   can be introduced before the :g:`:=` sign.

.. cmdv:: CoFixpoint @ident : @type := @term {+ with @ident : @type := @term }

   As in the ``Fixpoint`` command (see Section :ref:`Fixpoint`), it is possible
   to introduce a block of mutually dependent methods.

.. _Assertions:

Assertions and proofs
---------------------

An assertion states a proposition (or a type) of which the proof (or an
inhabitant of the type) is interactively built using tactics. The interactive
proof mode is described in Chapter :ref:`Proof-handling` and the tactics in
Chapter :ref:`Tactics`. The basic assertion command is:

.. cmd:: Theorem @ident : @type.

After the statement is asserted, Coq needs a proof. Once a proof of
:token:`type` under the assumptions represented by :token:`binders` is given and
validated, the proof is generalized into a proof of forall , :token:`type` and
the theorem is bound to the name :token:`ident` in the environment.

.. exn:: The term @term has type @type which should be Set, Prop or Type

.. exn:: @ident already exists

   The name you provided is already defined. You have then to choose
   another name.

.. cmdv:: Lemma @ident : @type.

.. cmdv:: Remark @ident : @type.

.. cmdv:: Fact @ident : @type.

.. cmdv:: Corollary @ident : @type.

.. cmdv:: Proposition @ident : @type.

   These commands are synonyms of ``Theorem`` :token:`ident` : :token:`type`.

.. cmdv:: Theorem @ident : @type {* with @ident : @type}.

   This command is useful for theorems that are proved by simultaneous
   induction over a mutually inductive assumption, or that assert
   mutually dependent statements in some mutual co-inductive type. It is
   equivalent to ``Fixpoint`` or ``CoFixpoint`` (see
   Section :ref:`CoFixpoint`) but using tactics to build
   the proof of the statements (or the body of the specification,
   depending on the point of view). The inductive or co-inductive types
   on which the induction or coinduction has to be done is assumed to be
   non ambiguous and is guessed by the system.

   Like in a ``Fixpoint`` or ``CoFixpoint`` definition, the induction hypotheses
   have to be used on *structurally smaller* arguments (for a ``Fixpoint``) or
   be *guarded by a constructor* (for a ``CoFixpoint``). The verification that
   recursive proof arguments are correct is done only at the time of registering
   the lemma in the environment. To know if the use of induction hypotheses is
   correct at some time of the interactive development of a proof, use the
   command Guarded (see Section :ref:`Guarded`).

   The command can be used also with ``Lemma``, ``Remark``, etc. instead of
   ``Theorem``.

.. cmdv:: Definition @ident : @type.

   This allows defining a term of type :token:`type` using the proof editing
   mode. It behaves as Theorem but is intended to be used in conjunction with
   Defined (see :ref:`Defined`) in order to define a constant of which the
   computational behavior is relevant.

   The command can be used also with ``Example`` instead of ``Definition``.

   See also Sections :ref:`Opaque` :ref:`Transparent` :ref:`unfold`.

.. cmdv:: Let @ident : @type.

   Like Definition :token:`ident` : :token:`type`. except that the definition is
   turned into a let-in definition generalized over the declarations depending
   on it after closing the current section.

.. cmdv:: Fixpoint @ident @binders with .

   This generalizes the syntax of Fixpoint so that one or more bodies
   can be defined interactively using the proof editing mode (when a
   body is omitted, its type is mandatory in the syntax). When the block
   of proofs is completed, it is intended to be ended by Defined.

.. cmdv:: CoFixpoint @ident with.

   This generalizes the syntax of CoFixpoint so that one or more bodies
   can be defined interactively using the proof editing mode.

.. cmd:: Proof. … Qed.

A proof starts by the keyword Proof. Then Coq enters the proof editing mode
until the proof is completed. The proof editing mode essentially contains
tactics that are described in chapter :ref:`Tactics`. Besides tactics, there are
commands to manage the proof editing mode. They are described in Chapter
:ref:`Proof-handling`. When the proof is completed it should be validated and
put in the environment using the keyword Qed.

.. exn:: @ident already exists

.. note::

   #. Several statements can be simultaneously asserted.

   #. Not only other assertions but any vernacular command can be given
      while in the process of proving a given assertion. In this case, the
      command is understood as if it would have been given before the
      statements still to be proved.

   #. Proof is recommended but can currently be omitted. On the opposite
      side, Qed (or Defined, see below) is mandatory to validate a proof.

   #. Proofs ended by Qed are declared opaque. Their content cannot be
      unfolded (see :ref:`Conversion-tactics`), thus
      realizing some form of *proof-irrelevance*. To be able to unfold a
      proof, the proof should be ended by Defined (see below).

.. cmdv:: Proof. … Defined.

   Same as ``Proof. … Qed.`` but the proof is then declared transparent,
   which means that its content can be explicitly used for
   type-checking and that it can be unfolded in conversion tactics
   (see :ref:`Conversion-tactics,Opaque,Transparent`).

.. cmdv:: Proof. … Admitted.

   Turns the current asserted statement into an axiom and exits the proof mode.

.. [1]
   This is similar to the expression “*entry* :math:`\{` sep *entry*
   :math:`\}`” in standard BNF, or “*entry* :math:`(` sep *entry*
   :math:`)`\ \*” in the syntax of regular expressions.

.. [2]
   Except if the inductive type is empty in which case there is no
   equation that can be used to infer the return type.
