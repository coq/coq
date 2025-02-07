.. |bdi| replace:: βδι
.. |ra| replace:: :math:`\rightarrow_{\beta\delta\iota}`
.. |la| replace:: :math:`\leftarrow_{\beta\delta\iota}`
.. |eq| replace:: `=`:sub:`(by the main correctness theorem)`
.. |re| replace:: ``(PEeval`` `v` `ap`\ ``)``
.. |le| replace:: ``(Pphi_dev`` `v` ``(norm`` `ap`\ ``))``
.. |N| replace:: ``N``
.. |nat| replace:: ``nat``
.. |Z| replace:: ``Z``

.. _theringandfieldtacticfamilies:

ring and field: solvers for polynomial and rational equations
=============================================================

:Author: Bruno Barras, Benjamin Grégoire, Assia Mahboubi, Laurent Théry [#f1]_

.. note::
   The tactics described in this chapter require the Stdlib library.

This chapter presents the tactics dedicated to dealing with ring and
field equations.

What does this tactic do?
------------------------------

``ring`` does associative-commutative rewriting in ring and semiring
structures. Assume you have two binary functions :math:`\oplus` and
:math:`\otimes` that are associative and commutative, with :math:`\oplus`
distributive on :math:`\otimes`, and two constants 0 and 1 that are unities for
:math:`\oplus` and :math:`\otimes`. A polynomial is an expression built on
variables :math:`V_0`, :math:`V_1`, :math:`\dots` and constants by application
of :math:`\oplus` and :math:`\otimes`.

Let an ordered product be a product of variables :math:`V_{i_1} \otimes \dots
\otimes V_{i_n}` verifying :math:`i_1 ≤ i_2 ≤ \dots ≤ i_n` . Let a monomial be
the product of a constant and an ordered product. We can order the monomials by
the lexicographic order on products of variables. Let a canonical sum be an
ordered sum of monomials that are all different, i.e. each monomial in the sum
is strictly less than the following monomial according to the lexicographic
order. It is an easy theorem to show that every polynomial is equivalent (modulo
the ring properties) to exactly one canonical sum. This canonical sum is called
the normal form of the polynomial. In fact, the actual representation shares
monomials with same prefixes. So what does the ``ring`` tactic do? It normalizes polynomials over
any ring or semiring structure. The basic use of ``ring`` is to simplify ring
expressions, so that the user does not have to deal manually with the theorems
of associativity and commutativity.


.. example::

   In the ring of integers, the normal form of

     :math:`x (3 + yx + 25(1 − z)) + zx`

   is

     :math:`28x + (−24)xz + xxy`.


``ring`` is also able to compute a normal form modulo monomial equalities.
For example, under the hypothesis that :math:`2x^2 = yz+1`, the normal form of
:math:`2(x + 1)x − x − zy` is :math:`x+1`.

The variables map
----------------------

It is frequent to have an expression built with :math:`+` and :math:`\times`,
but rarely on variables only. Let us associate a number to each subterm of a
ring expression in the Gallina language. For example, consider this expression
in the semiring ``nat``:

::

    (plus (mult (plus (f (5)) x) x)
          (mult (if b then (4) else (f (3))) (2)))


As a ring expression, it has 3 subterms. Give each subterm a number in
an arbitrary order:

=====  ===============  =========================
0      :math:`\mapsto`  if b then (4) else (f (3))
1      :math:`\mapsto`  (f (5))
2      :math:`\mapsto`  x
=====  ===============  =========================

Then normalize the “abstract” polynomial
:math:`((V_1 \oplus V_2 ) \otimes V_2) \oplus (V_0 \otimes 2)`
In our example the normal form is:
:math:`(2 \otimes V_0 ) \oplus (V_1 \otimes V_2) \oplus (V_2 \otimes V_2 )`.
Then substitute the variables by their values in the variables map to
get the concrete normal polynomial:

::

    (plus (mult (2) (if b then (4) else (f (3)))) 
          (plus (mult (f (5)) x) (mult x x))) 


Is it automatic?
---------------------

Yes, building the variables map and doing the substitution after
normalizing is automatically done by the tactic. So you can just
forget this paragraph and use the tactic according to your intuition.

Concrete usage
--------------------------

.. tacn:: ring {? [ {+ @one_term } ] }

   Solves polynomical equations of a ring
   (or semiring) structure. It proceeds by normalizing both sides
   of the equation (w.r.t. associativity, commutativity and
   distributivity, constant propagation, rewriting of monomials) and
   syntactically comparing the results.

   :n:`[ {+ @one_term } ]`
     If specified, the tactic decides the equality of two terms modulo ring operations and
     the equalities defined by the :token:`one_term`\s.
     Each :token:`one_term` has to be a proof of some equality :g:`m = p`, where :g:`m`
     is a monomial (after “abstraction”), :g:`p` a polynomial and :g:`=` is the
     corresponding equality of the ring structure.

.. tacn:: ring_simplify {? [ {+ @one_term } ] } {+ @one_term } {? in @ident }

   Applies the normalization procedure described above to
   the given :token:`one_term`\s. The tactic then replaces all occurrences of the :token:`one_term`\s
   given in the conclusion of the goal by their normal forms. If no :token:`one_term`
   is given, then the conclusion should be an equation and both
   sides are normalized. The tactic can also be applied in a hypothesis.

   :n:`in @ident`
     If specified, the tactic performs the simplification in the hypothesis named :token:`ident`.

   .. note::

     :n:`ring_simplify @one_term__1; ring_simplify @one_term__2` is not equivalent to
     :n:`ring_simplify @one_term__1 @one_term__2`.

     In the latter case the variables map is shared between the two :token:`one_term`\s, and
     common subterm :g:`t` of :n:`@one_term__1` and :n:`@one_term__2`
     will have the same associated variable number. So the first
     alternative should be avoided for :token:`one_term`\s belonging to the same ring
     theory.

   The tactic must be loaded by ``Require Import Ring``. The ring structures
   must be declared with the ``Add Ring`` command (see below). The ring of
   booleans is predefined; if one wants to use the tactic on |nat| one must
   first require the module ``ArithRing`` exported by ``Arith``); for |Z|, do
   ``Require Import ZArithRing`` or simply ``Require Import ZArith``; for |N|, do
   ``Require Import NArithRing`` or ``Require Import NArith``.

   All declared field structures can be printed with the :cmd:`Print Rings` command.

   .. cmd:: Print Rings
      :undocumented:

.. example::

  .. rocqtop:: all extra-stdlib

    From Stdlib Require Import ZArith.
    Open Scope Z_scope.
    Goal forall a b c:Z, 
        (a + b + c) ^ 2 = 
         a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
    intros; ring.
    Abort.
    Goal forall a b:Z, 
         2 * a * b = 30 -> (a + b) ^ 2 = a ^ 2 + b ^ 2 + 30.
    intros a b H; ring [H].
    Abort.


Error messages:


.. exn:: Not a valid ring equation.

  The conclusion of the goal is not provable in the corresponding ring theory.

.. exn:: Arguments of ring_simplify do not have all the same type.
  
  :tacn:`ring_simplify` cannot simplify terms of several rings at the same
  time. Invoke the tactic once per ring structure.

.. exn:: Cannot find a declared ring structure over @term.

  No ring has been declared for the type of the terms to be simplified.
  Use :cmd:`Add Ring` first.

.. exn:: Cannot find a declared ring structure for equality @term.

  Same as above in the case of the :tacn:`ring` tactic.

.. tacn:: ring_lookup @ltac_expr0 [ {* @one_term } ] {+ @one_term }
          protect_fv @string {? in @ident }

   For internal use only.

Adding a ring structure
----------------------------

Declaring a new ring consists in proving that a ring signature (a
carrier set, an equality, and ring operations: ``Ring_theory.ring_theory``
and ``Ring_theory.semi_ring_theory``) satisfies the ring axioms. Semi-
rings (rings without + inverse) are also supported. The equality can
be either Leibniz equality, or any relation declared as a setoid (see
:ref:`tactics-enabled-on-user-provided-relations`).
The definitions of ring and semiring (see module ``Ring_theory``) are:

.. rocqdoc::

    Record ring_theory : Prop := mk_rt {
      Radd_0_l    : forall x, 0 + x == x;
      Radd_sym    : forall x y, x + y == y + x;
      Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
      Rmul_1_l    : forall x, 1 * x == x;
      Rmul_sym    : forall x y, x * y == y * x;
      Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
      Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
      Rsub_def    : forall x y, x - y == x + -y;
      Ropp_def    : forall x, x + (- x) == 0
    }.
    
    Record semi_ring_theory : Prop := mk_srt {
      SRadd_0_l   : forall n, 0 + n == n;
      SRadd_sym   : forall n m, n + m == m + n ;
      SRadd_assoc : forall n m p, n + (m + p) == (n + m) + p;
      SRmul_1_l   : forall n, 1*n == n;
      SRmul_0_l   : forall n, 0*n == 0;
      SRmul_sym   : forall n m, n*m == m*n;
      SRmul_assoc : forall n m p, n*(m*p) == (n*m)*p;
      SRdistr_l   : forall n m p, (n + m)*p == n*p + m*p
    }.


This implementation of ``ring`` also features a notion of constant that
can be parameterized. This can be used to improve the handling of
closed expressions when operations are effective. It consists in
introducing a type of *coefficients* and an implementation of the ring
operations, and a morphism from the coefficient type to the ring
carrier type. The morphism needs not be injective, nor surjective.

As an example, one can consider the real numbers. The set of
coefficients could be the rational numbers, upon which the ring
operations can be implemented. The fact that there exists a morphism
is defined by the following properties:

.. rocqdoc::

    Record ring_morph : Prop := mkmorph {
      morph0    : [cO] == 0;
      morph1    : [cI] == 1;
      morph_add : forall x y, [x +! y] == [x]+[y];
      morph_sub : forall x y, [x -! y] == [x]-[y];
      morph_mul : forall x y, [x *! y] == [x]*[y];
      morph_opp : forall x, [-!x] == -[x];
      morph_eq  : forall x y, x?=!y = true -> [x] == [y]
    }.
    
    Record semi_morph : Prop := mkRmorph {
      Smorph0 : [cO] == 0;
      Smorph1 : [cI] == 1;
      Smorph_add : forall x y, [x +! y] == [x]+[y];
      Smorph_mul : forall x y, [x *! y] == [x]*[y];
      Smorph_eq  : forall x y, x?=!y = true -> [x] == [y]
    }.


where ``c0`` and ``cI`` denote the 0 and 1 of the coefficient set, ``+!``, ``*!``, ``-!``
are the implementations of the ring operations, ``==`` is the equality of
the coefficients, ``?+!`` is an implementation of this equality, and ``[x]``
is a notation for the image of ``x`` by the ring morphism.

Since |Z| is an initial ring (and |N| is an initial semiring), it can
always be considered as a set of coefficients. There are basically
three kinds of (semi-)rings:

abstract rings
  to be used when operations are not effective. The set
  of coefficients is |Z| (or |N| for semirings).

computational rings
  to be used when operations are effective. The
  set of coefficients is the ring itself. The user only has to provide
  an implementation for the equality.

customized ring
  for other cases. The user has to provide the
  coefficient set and the morphism.


This implementation of ring can also recognize simple power
expressions as ring expressions. A power function is specified by the
following property:

.. rocqtop:: in extra-stdlib

    From Stdlib Require Import Reals.
    Section POWER.
      Variable Cpow : Set.
      Variable Cp_phi : N -> Cpow.
      Variable rpow : R -> Cpow -> R.
    
      Record power_theory : Prop := mkpow_th {
        rpow_pow_N : forall r n, rpow r (Cp_phi n) = pow_N 1%R Rmult r n
      }.
    
    End POWER.


The syntax for adding a new ring is 

.. cmd:: Add Ring @ident : @one_term {? ( {+, @ring_mod } ) }

   .. insertprodn ring_mod ring_mod

   .. prodn::
      ring_mod ::= decidable @one_term
      | abstract
      | morphism @one_term
      | constants [ @ltac_expr ]
      | preprocess [ @ltac_expr ]
      | postprocess [ @ltac_expr ]
      | setoid @one_term @one_term
      | sign @one_term
      | power @one_term [ {+ @qualid } ]
      | power_tac @one_term [ @ltac_expr ]
      | div @one_term
      | closed [ {+ @qualid } ]

   The :n:`@ident` is used only for error messages. The
   :n:`@one_term` is a proof that the ring signature satisfies the (semi-)ring
   axioms. The optional list of modifiers is used to tailor the behavior
   of the tactic. Here are their effects:

   :n:`abstract`
      declares the ring as abstract. This is the default.

   :n:`decidable @one_term`
      declares the ring as computational. The expression
      :n:`@one_term` is the correctness proof of an equality test ``?=!``
      (which should be evaluable). Its type should be of the form
      ``forall x y, x ?=! y = true → x == y``.

   :n:`morphism @one_term`
      declares the ring as a customized one. The expression
      :n:`@one_term` is a proof that there exists a morphism between a set of
      coefficient and the ring carrier (see ``Ring_theory.ring_morph`` and
      ``Ring_theory.semi_morph``).

   :n:`setoid @one_term @one_term`
      forces the use of given setoid. The first
      :n:`@one_term` is a proof that the equality is indeed a setoid (see
      ``Setoid.Setoid_Theory``), and the second a proof that the
      ring operations are morphisms (see ``Ring_theory.ring_eq_ext`` and
      ``Ring_theory.sring_eq_ext``).
      This modifier needs not be used if the setoid and morphisms have been
      declared.

   :n:`constants [ @ltac_expr ]`
      specifies a tactic expression :n:`@ltac_expr` that, given a
      term, returns either an object of the coefficient set that is mapped
      to the expression via the morphism, or returns
      ``InitialRing.NotConstant``. The default behavior is to map only 0 and 1
      to their counterpart in the coefficient set. This is generally not
      desirable for nontrivial computational rings.

   :n:`preprocess [ @ltac_expr ]`
      specifies a tactic :n:`@ltac_expr` that is applied as a
      preliminary step for :tacn:`ring` and :tacn:`ring_simplify`.
      It can be used to
      transform a goal so that it is better recognized. For instance, ``S n``
      can be changed to ``plus 1 n``.  For :tacn:`ring_simplify`, the terms
      given as arguments are also modified by this tactic.

   :n:`postprocess [ @ltac_expr ]`
      specifies a tactic :n:`@ltac_expr` that is applied as a final
      step for :tacn:`ring_simplify`. For instance, it can be used to undo
      modifications of the preprocessor.

   :n:`power @one_term [ {+ @qualid } ]`
      to be documented

   :n:`power_tac @one_term @ltac_expr ]`
      allows :tacn:`ring` and :tacn:`ring_simplify` to recognize
      power expressions with a constant positive integer exponent (example:
      :math:`x^2` ). The term :n:`@one_term` is a proof that a given power function satisfies
      the specification of a power function (term has to be a proof of
      ``Ring_theory.power_theory``) and :n:`@tactic` specifies a tactic expression
      that, given a term, “abstracts” it into an object of type |N| whose
      interpretation via ``Cp_phi`` (the evaluation function of power
      coefficient) is the original term, or returns ``InitialRing.NotConstant``
      if not a constant coefficient (i.e. |Ltac| is the inverse function of
      ``Cp_phi``). See files ``plugins/ring/ZArithRing.v``
      and ``plugins/ring/RealField.v`` for examples. By default the tactic
      does not recognize power expressions as ring expressions.

   :n:`sign @one_term`
      allows :tacn:`ring_simplify` to use a minus operation when
      outputting its normal form, i.e writing ``x − y`` instead of ``x + (− y)``. The
      term :token:`term` is a proof that a given sign function indicates expressions
      that are signed (:token:`term` has to be a proof of ``Ring_theory.get_sign``). See
      ``plugins/ring/InitialRing.v`` for examples of sign function.

   :n:`div @one_term`
      allows :tacn:`ring` and :tacn:`ring_simplify` to use monomials with
      coefficients other than 1 in the rewriting. The term :n:`@one_term` is a proof
      that a given division function satisfies the specification of an
      euclidean division function (:n:`@one_term` has to be a proof of
      ``Ring_theory.div_theory``). For example, this function is called when
      trying to rewrite :math:`7x` by :math:`2x = z` to tell that :math:`7 = 3 \times 2 + 1`. See
      ``plugins/ring/InitialRing.v`` for examples of div function.

   :n:`closed [ {+ @qualid } ]`
      to be documented

Error messages:

.. exn:: Bad ring structure.

  The proof of the ring structure provided is not
  of the expected type.

.. exn:: Bad lemma for decidability of equality.

  The equality function
  provided in the case of a computational ring has not the expected
  type.

.. exn:: Ring operation should be declared as a morphism.

  A setoid associated with the carrier of the ring structure has been found,
  but the ring operation should be declared as morphism. See :ref:`tactics-enabled-on-user-provided-relations`.

How does it work?
----------------------

The code of ``ring`` is a good example of a tactic written using *reflection*.
What is reflection? Basically, using it means that a part of a tactic is written
in Gallina, Rocq's language of terms, rather than |Ltac| or OCaml. From the
philosophical point of view, reflection is using the ability of the Calculus of
Constructions to speak and reason about itself. For the ``ring`` tactic we used
Rocq as a programming language and also as a proof environment to build a tactic
and to prove its correctness.

The interested reader is strongly advised to have a look at the
file ``Ring_polynom.v``. Here a type for polynomials is defined:


.. rocqdoc::

    Inductive PExpr : Type :=
      | PEc : C -> PExpr
      | PEX : positive -> PExpr
      | PEadd : PExpr -> PExpr -> PExpr
      | PEsub : PExpr -> PExpr -> PExpr
      | PEmul : PExpr -> PExpr -> PExpr
      | PEopp : PExpr -> PExpr
      | PEpow : PExpr -> N -> PExpr.


Polynomials in normal form are defined as:


.. rocqdoc::

    Inductive Pol : Type :=
      | Pc : C -> Pol 
      | Pinj : positive -> Pol -> Pol                   
      | PX : Pol -> positive -> Pol -> Pol.


where ``Pinj n P`` denotes ``P`` in which :math:`V_i` is replaced by :math:`V_{i+n}` , 
and ``PX P n Q`` denotes :math:`P \otimes V_1^n \oplus Q'`, `Q'` being `Q` where :math:`V_i` is replaced by :math:`V_{i+1}`.

Variable maps are represented by lists of ring elements, and two
interpretation functions, one that maps a variables map and a
polynomial to an element of the concrete ring, and the second one that
does the same for normal forms:


.. rocqdoc::


    Definition PEeval : list R -> PExpr -> R := [...].
    Definition Pphi_dev : list R -> Pol -> R := [...].


A function to normalize polynomials is defined, and the big theorem is
its correctness w.r.t interpretation, that is:


.. rocqdoc::

    Definition norm : PExpr -> Pol := [...].
    Lemma Pphi_dev_ok :
       forall l pe npe, norm pe = npe -> PEeval l pe == Pphi_dev l npe.


So now, what is the scheme for a normalization proof? Let p be the
polynomial expression that the user wants to normalize. First a little
piece of ML code guesses the type of `p`, the ring theory `T` to use, an
abstract polynomial `ap` and a variables map `v` such that `p` is |bdi|-
equivalent to `(PEeval v ap)`. Then we replace it by `(Pphi_dev v (norm ap))`,
using the main correctness theorem and we reduce it to a
concrete expression `p’`, which is the concrete normal form of `p`. This is summarized in this diagram:

========= ======  ====
`p`        |ra|   |re|            
\          |eq|    \ 
`p’`       |la|   |le|
========= ======  ====

The user does not see the right part of the diagram. From outside, the
tactic behaves like a |bdi| simplification extended with rewriting rules
for associativity and commutativity. Basically, the proof is only the
application of the main correctness theorem to well-chosen arguments.

Dealing with fields
------------------------

.. tacn:: field {? [ {+ @one_term } ] }

   An extension of the :tacn:`ring` tactic that deals with rational
   expressions. Given a rational expression :math:`F = 0`. It first reduces the
   expression `F` to a common denominator :math:`N/D = 0` where `N` and `D`
   are two ring expressions. For example, if we take :math:`F = (1 − 1/x) x − x + 1`, this
   gives :math:`N = (x − 1) x − x^2 + x` and :math:`D = x`. It then calls ring to solve
   :math:`N = 0`.

   :n:`[ {+ @one_term } ]`
     If specified, the tactic decides the equality of two terms modulo
     field operations and the equalities defined
     by the :token:`one_term`\s. Each :token:`one_term` has to be a proof of some equality
     :g:`m = p`, where :g:`m` is a monomial (after “abstraction”), :g:`p` a polynomial
     and :g:`=` the corresponding equality of the field structure.

  .. note::

     Rewriting works with the equality  :g:`m = p` only if :g:`p` is a polynomial since
     rewriting is handled by the underlying ring tactic.

   Note that :n:`field` also generates nonzero conditions for all the
   denominators it encounters in the reduction. In our example, it
   generates the condition :math:`x \neq 0`. These conditions appear as one subgoal
   which is a conjunction if there are several denominators. Nonzero
   conditions are always polynomial expressions. For example when
   reducing the expression :math:`1/(1 + 1/x)`, two side conditions are
   generated: :math:`x \neq 0` and :math:`x + 1 \neq 0`. Factorized expressions are broken since
   a field is an integral domain, and when the equality test on
   coefficients is complete w.r.t. the equality of the target field,
   constants can be proven different from zero automatically.

   The tactic must be loaded by ``Require Import Field``. New field
   structures can be declared to the system with the ``Add Field`` command
   (see below). The field of real numbers is defined in module ``RealField``
   (in ``plugins/ring``). It is exported by module ``Rbase``, so
   that requiring ``Rbase`` or ``Reals`` is enough to use the field tactics on
   real numbers. Rational numbers in canonical form are also declared as
   a field in the module ``Qcanon``.


.. example::

  .. rocqtop:: all extra-stdlib

    From Stdlib Require Import Reals.
    Open Scope R_scope.
    Goal forall x,
           x <> 0 -> (1 - 1 / x) * x - x + 1 = 0.
    intros; field; auto.
    Abort.
    Goal forall x y, 
           y <> 0 -> y = x -> x / y = 1.
    intros x y H H1; field [H1]; auto.
    Abort.


.. example:: :tacn:`field` that generates side goals

   .. rocqtop:: reset all extra-stdlib

      From Stdlib Require Import Reals.
      Goal forall x y:R,
      (x * y > 0)%R ->
      (x * (1 / x + x / (x + y)))%R =
      ((- 1 / y) * y * (- x * (x / (x + y)) - 1))%R.

      intros; field.

.. tacn:: field_simplify {? [ {+ @one_term__eq } ] } {+ @one_term } {? in @ident }
 
   Performs the simplification in the conclusion of the
   goal, :math:`F_1 = F_2` becomes :math:`N_1 / D_1 = N_2 / D_2`. A normalization step
   (the same as the one for rings) is then applied to :math:`N_1`, :math:`D_1`, 
   :math:`N_2` and :math:`D_2`. This way, polynomials remain in factorized form during
   fraction simplification. This yields smaller expressions when
   reducing to the same denominator since common factors can be canceled.

   :n:`[ {+ @one_term__eq } ]`
     Do simplification in the conclusion of the goal using the equalities
     defined by these :token:`one_term`\s.

   :n:`{+ @one_term }`
     Terms to simplify in the conclusion.

   :n:`in @ident`
     If specified, substitute in the hypothesis :n:`@ident` instead of the conclusion.

.. tacn:: field_simplify_eq {? [ {+ @one_term } ] } {? in @ident }

   Performs the simplification in the conclusion of
   the goal, removing the denominator. :math:`F_1 = F_2` becomes :math:`N_1 D_2 = N_2 D_1`.

   :n:`[ {+ @one_term } ]`
     Do simplification in the conclusion of the goal using the equalities
     defined by these :token:`one_term`\s.

   :n:`in @ident`
     If specified, simplify in the hypothesis :n:`@ident` instead of the conclusion.

.. tacn:: field_lookup @ltac_expr [ {* @one_term } ] {+ @one_term }

   For internal use only.

Adding a new field structure
---------------------------------

Declaring a new field consists in proving that a field signature (a
carrier set, an equality, and field operations:
``Field_theory.field_theory`` and ``Field_theory.semi_field_theory``)
satisfies the field axioms. Semi-fields (fields without + inverse) are
also supported. The equality can be either Leibniz equality, or any
relation declared as a setoid (see :ref:`tactics-enabled-on-user-provided-relations`). The definition of
fields and semifields is:

.. rocqdoc::

    Record field_theory : Prop := mk_field {
      F_R : ring_theory rO rI radd rmul rsub ropp req;
      F_1_neq_0 : ~ 1 == 0;
      Fdiv_def : forall p q, p / q == p * / q;
      Finv_l : forall p, ~ p == 0 ->  / p * p == 1
    }.
    
    Record semi_field_theory : Prop := mk_sfield {
      SF_SR : semi_ring_theory rO rI radd rmul req;
      SF_1_neq_0 : ~ 1 == 0;
      SFdiv_def : forall p q, p / q == p * / q;
      SFinv_l : forall p, ~ p == 0 ->  / p * p == 1
    }.


The result of the normalization process is a fraction represented by
the following type:

.. rocqdoc::

    Record linear : Type := mk_linear {
      num : PExpr C;
      denum : PExpr C;
      condition : list (PExpr C)
    }.


where ``num`` and ``denum`` are the numerator and denominator; ``condition`` is a
list of expressions that have appeared as a denominator during the
normalization process. These expressions must be proven different from
zero for the correctness of the algorithm.

The syntax for adding a new field is 

.. cmd:: Add Field @ident : @one_term {? ( {+, @field_mod } ) }

   .. insertprodn field_mod field_mod

   .. prodn::
      field_mod ::= @ring_mod
      | completeness @one_term

   The :n:`@ident` is used only for error
   messages. :n:`@one_term` is a proof that the field signature satisfies the
   (semi-)field axioms. The optional list of modifiers is used to tailor
   the behavior of the tactic.

   Since field tactics are built upon ``ring``
   tactics, all modifiers of :cmd:`Add Ring` apply. There is only one
   specific modifier:

   completeness :n:`@one_term`
      allows the field tactic to prove automatically
      that the image of nonzero coefficients are mapped to nonzero
      elements of the field. :n:`@one_term` is a proof of
      :g:`forall x y, [x] == [y] ->  x ?=! y = true`,
      which is the completeness of equality on coefficients
      w.r.t. the field equality.

   When :cmd:`Add Field` is called, a call to :cmd:`Add Ring` is performed with
   all modifiers of the form :n:`@ring_mod`.  As a result, any previous ring
   declaration for the type is replaced by the one that uses the same modifiers
   as the :cmd:`Add Field` command.  In the case where it
   is desired to have different modifiers for the field and the ring structure,
   a new call to :cmd:`Add Ring` can be performed after this command, to set
   different values of certain modifiers.

.. cmd:: Print Fields
   :undocumented:

History of ring
--------------------

First Samuel Boutin designed the tactic ``ACDSimpl``. This tactic did lot
of rewriting. But the proofs terms generated by rewriting were too big
for Coq’s type checker. Let us see why:

.. rocqtop:: reset all extra-stdlib

  From Stdlib Require Import ZArith.
  Open Scope Z_scope.
  Goal forall x y z : Z, 
         x + 3 + y + y * z = x + 3 + y + z * y.
  intros; rewrite (Zmult_comm y z); reflexivity.
  Save foo.
  Print foo.

At each step of rewriting, the whole context is duplicated in the
proof term. Then, a tactic that does hundreds of rewriting generates
huge proof terms. Since ``ACDSimpl`` was too slow, Samuel Boutin rewrote
it using reflection (see :cite:`Bou97`). Later, it
was rewritten by Patrick Loiseleur: the new tactic does not any
more require ``ACDSimpl`` to compile and it makes use of |bdi|-reduction not
only to replace the rewriting steps, but also to achieve the
interleaving of computation and reasoning (see :ref:`discussion_reflection`). He also wrote
some ML code for the ``Add Ring`` command that allows registering new rings dynamically.

Proofs terms generated by ring are quite small, they are linear in the
number of :math:`\oplus` and :math:`\otimes` operations in the normalized terms. Type checking
those terms requires some time because it makes a large use of the
conversion rule, but memory requirements are much smaller.


.. _discussion_reflection:


Discussion
----------------


Efficiency is not the only motivation to use reflection here. ``ring``
also deals with constants, it rewrites for example the expression 
``34 + 2 * x − x + 12`` to the expected result ``x + 46``.
For the tactic ``ACDSimpl``, the only constants were 0 and 1. 
So the expression ``34 + 2 * (x − 1) + 12``
is interpreted as :math:`V_0 \oplus V_1 \otimes (V_2 \ominus 1) \oplus V_3`\ ,
with the variables mapping 
:math:`\{V_0 \mapsto 34; V_1 \mapsto 2; V_2 \mapsto x; V_3 \mapsto 12\}`\ . 
Then it is rewritten to ``34 − x + 2 * x + 12``, very far from the expected result. 
Here rewriting is not sufficient: you have to do some kind of reduction
(some kind of computation) to achieve the normalization.

The tactic ``ring`` is not only faster than the old one: by using
reflection, we get for free the integration of computation and reasoning
that would be very difficult to implement without it.

Is it the ultimate way to write tactics? The answer is: yes and no.
The ``ring`` tactic intensively uses the conversion rules of the Calculus of
Inductive Constructions, i.e. it replaces proofs by computations as much as possible.
It can be useful in all situations where a classical tactic generates huge proof
terms, like symbolic processing and tautologies. But there
are also tactics like ``auto`` or ``linear`` that do many complex computations,
using side-effects and backtracking, and generate a small proof term.
Clearly, it would be significantly less efficient to replace them by
tactics using reflection.

Another idea suggested by Benjamin Werner: reflection could be used to
couple an external tool (a rewriting program or a model checker)
with Rocq. We define (in Rocq) a type of terms, a type of *traces*, and
prove a correctness theorem that states that *replaying traces* is safe
with respect to some interpretation. Then we let the external tool do every
computation (using side-effects, backtracking, exception, or others
features that are not available in pure lambda calculus) to produce
the trace. Now we can check in Rocq that the trace has the expected
semantics by applying the correctness theorem.






.. rubric:: Footnotes
.. [#f1] based on previous work from Patrick Loiseleur and Samuel Boutin



