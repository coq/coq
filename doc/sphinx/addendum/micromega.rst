.. _ micromega:

Micromega: tactics for solving arithmetic goals over ordered rings
==================================================================

:Authors: Frédéric Besson and Evgeny Makarov

Short description of the tactics
--------------------------------

The Psatz module (``Require Import Psatz.``) gives access to several
tactics for solving arithmetic goals over :math:`\mathbb{Q}`,
:math:`\mathbb{R}`, and :math:`\mathbb{Z}` but also :g:`nat` and
:g:`N`.  It also possible to get the tactics for integers by a
``Require Import Lia``, rationals ``Require Import Lqa`` and reals
``Require Import Lra``.

+ :tacn:`lia` is a decision procedure for linear integer arithmetic;
+ :tacn:`nia` is an incomplete proof procedure for integer non-linear
  arithmetic;
+ :tacn:`lra` is a decision procedure for linear (real or rational) arithmetic;
+ :tacn:`nra` is an incomplete proof procedure for non-linear (real or
  rational) arithmetic;
+ :tacn:`psatz` ``D n`` where ``D`` is :math:`\mathbb{Z}` or :math:`\mathbb{Q}` or :math:`\mathbb{R}`, and
  ``n`` is an optional integer limiting the proof search depth,
  is an incomplete proof procedure for non-linear arithmetic.
  It is based on John Harrison’s HOL Light
  driver to the external prover `csdp` [#csdp]_. Note that the `csdp` driver is
  generating a *proof cache* which makes it possible to rerun scripts
  even without `csdp`.

.. flag:: Simplex

   This option (set by default) instructs the decision procedures to
   use the Simplex method for solving linear goals. If it is not set,
   the decision procedures are using Fourier elimination.

.. flag:: Lia Cache

   This option (set by default) instructs :tacn:`lia` to cache its results in the file `.lia.cache`

.. flag:: Nia Cache

   This option (set by default) instructs :tacn:`nia` to cache its results in the file `.nia.cache`

.. flag:: Nra Cache

   This option (set by default) instructs :tacn:`nra` to cache its results in the file `.nra.cache`


The tactics solve propositional formulas parameterized by atomic
arithmetic expressions interpreted over a domain :math:`D \in \{\mathbb{Z},\mathbb{Q},\mathbb{R}\}`.
The syntax of the formulas is the following:

 .. productionlist:: F
   F : A ∣ P ∣ True ∣ False ∣ F ∧ F ∣ F ∨ F ∣ F ↔ F ∣ F → F ∣ ¬ F
   A : p = p ∣ p > p ∣ p < p ∣ p ≥ p ∣ p ≤ p
   p : c ∣ x ∣ −p ∣ p − p ∣ p + p ∣ p × p ∣ p ^ n

where :math:`c` is a numeric constant, :math:`x \in D` is a numeric variable, the
operators :math:`−, +, ×` are respectively subtraction, addition, and product;
:math:`p ^ n` is exponentiation by a constant :math:`n`, :math:`P` is an arbitrary proposition.
For :math:`\mathbb{Q}`, equality is not Leibniz equality ``=`` but the equality of
rationals ``==``.

For :math:`\mathbb{Z}` (resp. :math:`\mathbb{Q}`), :math:`c` ranges over integer constants (resp. rational
constants). For :math:`\mathbb{R}`, the tactic recognizes as real constants the
following expressions:

::

   c ::= R0 | R1 | Rmul(c,c) | Rplus(c,c) | Rminus(c,c) | IZR z | IQR q | Rdiv(c,c) | Rinv c

where :math:`z` is a constant in :math:`\mathbb{Z}` and :math:`q` is a constant in :math:`\mathbb{Q}`.
This includes integer constants written using the decimal notation, *i.e.*, ``c%R``.


*Positivstellensatz* refutations
--------------------------------

The name `psatz` is an abbreviation for *positivstellensatz* – literally
"positivity theorem" – which generalizes Hilbert’s *nullstellensatz*. It
relies on the notion of Cone. Given a (finite) set of polynomials :math:`S`,
:math:`\mathit{Cone}(S)` is inductively defined as the smallest set of polynomials
closed under the following rules:

:math:`\begin{array}{l}
\dfrac{p \in S}{p \in \mathit{Cone}(S)} \quad
\dfrac{}{p^2 \in \mathit{Cone}(S)} \quad
\dfrac{p_1 \in \mathit{Cone}(S) \quad p_2 \in \mathit{Cone}(S) \quad
\Join \in \{+,*\}} {p_1 \Join p_2 \in \mathit{Cone}(S)}\\
\end{array}`

The following theorem provides a proof principle for checking that a
set of polynomial inequalities does not have solutions [#fnpsatz]_.

.. _psatz_thm:

**Theorem (Psatz)**. Let :math:`S` be a set of polynomials.
If :math:`-1` belongs to :math:`\mathit{Cone}(S)`, then the conjunction
:math:`\bigwedge_{p \in S} p\ge 0`  is unsatisfiable.
A proof based on this theorem is called a *positivstellensatz*
refutation. The tactics work as follows. Formulas are normalized into
conjunctive normal form :math:`\bigwedge_i C_i` where :math:`C_i` has the
general form :math:`(\bigwedge_{j\in S_i} p_j \Join 0) \to \mathit{False}` and
:math:`\Join \in \{>,\ge,=\}` for :math:`D\in \{\mathbb{Q},\mathbb{R}\}` and
:math:`\Join \in \{\ge, =\}` for :math:`\mathbb{Z}`.

For each conjunct :math:`C_i`, the tactic calls an oracle which searches for
:math:`-1` within the cone. Upon success, the oracle returns a *cone
expression* that is normalized by the :tacn:`ring` tactic (see :ref:`theringandfieldtacticfamilies`)
and checked to be :math:`-1`.

`lra`: a decision procedure for linear real and rational arithmetic
-------------------------------------------------------------------

.. tacn:: lra
   :name: lra

   This tactic is searching for *linear* refutations. As a result, this tactic explores a subset of the *Cone*
   defined as

   :math:`\mathit{LinCone}(S) =\left\{ \left. \sum_{p \in S} \alpha_p \times p~\right|~\alpha_p \mbox{ are positive constants} \right\}`

   The deductive power of :tacn:`lra` overlaps with the one of :tacn:`field`
   tactic *e.g.*, :math:`x = 10 * x / 10` is solved by :tacn:`lra`.

`lia`: a tactic for linear integer arithmetic
---------------------------------------------

.. tacn:: lia
   :name: lia

   This tactic solves linear goals over :g:`Z` by searching for *linear* refutations and cutting planes.
   :tacn:`lia` provides support for :g:`Z`, :g:`nat`, :g:`positive` and :g:`N` by pre-processing via the :tacn:`zify` tactic.


High level view of `lia`
~~~~~~~~~~~~~~~~~~~~~~~~

Over :math:`\mathbb{R}`, *positivstellensatz* refutations are a complete proof
principle [#mayfail]_. However, this is not the case over :math:`\mathbb{Z}`. Actually,
*positivstellensatz* refutations are not even sufficient to decide
linear *integer* arithmetic. The canonical example is :math:`2 * x = 1 -> \mathtt{False}`
which is a theorem of :math:`\mathbb{Z}` but not a theorem of :math:`{\mathbb{R}}`. To remedy this
weakness, the :tacn:`lia` tactic is using recursively a combination of:

+ linear *positivstellensatz* refutations;
+ cutting plane proofs;
+ case split.

Cutting plane proofs
~~~~~~~~~~~~~~~~~~~~~~

are a way to take into account the discreteness of :math:`\mathbb{Z}` by rounding up
(rational) constants up-to the closest integer.

.. _ceil_thm:

.. thm:: Bound on the ceiling function

   Let :math:`p` be an integer and :math:`c` a rational constant. Then
   :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.

For instance, from 2 x = 1 we can deduce

+ :math:`x \ge 1/2` whose cut plane is :math:`x \ge \lceil{1/2}\rceil = 1`;
+ :math:`x \le 1/2` whose cut plane is :math:`x \le \lfloor{1/2}\rfloor = 0`.

By combining these two facts (in normal form) :math:`x − 1 \ge 0` and
:math:`-x \ge 0`, we conclude by exhibiting a *positivstellensatz* refutation:
:math:`−1 \equiv x−1 + −x \in \mathit{Cone}({x−1,x})`.

Cutting plane proofs and linear *positivstellensatz* refutations are a
complete proof principle for integer linear arithmetic.

Case split
~~~~~~~~~~~

enumerates over the possible values of an expression.

.. _casesplit_thm:

**Theorem**. Let :math:`p` be an integer and :math:`c_1` and :math:`c_2`
integer constants. Then:

  :math:`c_1 \le p \le c_2 \Rightarrow \bigvee_{x \in [c_1,c_2]} p = x`

Our current oracle tries to find an expression :math:`e` with a small range
:math:`[c_1,c_2]`. We generate :math:`c_2 − c_1` subgoals which contexts are enriched
with an equation :math:`e = i` for :math:`i \in [c_1,c_2]` and recursively search for
a proof.

`nra`: a proof procedure for non-linear arithmetic
--------------------------------------------------

.. tacn:: nra
   :name: nra

   This tactic is an *experimental* proof procedure for non-linear
   arithmetic. The tactic performs a limited amount of non-linear
   reasoning before running the linear prover of :tacn:`lra`. This pre-processing
   does the following:


+ If the context contains an arithmetic expression of the form
  :math:`e[x^2]` where :math:`x` is a monomial, the context is enriched with
  :math:`x^2 \ge 0`;
+ For all pairs of hypotheses :math:`e_1 \ge 0`, :math:`e_2 \ge 0`, the context is
  enriched with :math:`e_1 \times e_2 \ge 0`.

After this pre-processing, the linear prover of :tacn:`lra` searches for a
proof by abstracting monomials by variables.

`nia`: a proof procedure for non-linear integer arithmetic
----------------------------------------------------------

.. tacn:: nia
   :name: nia

   This tactic is a proof procedure for non-linear integer arithmetic.
   It performs a pre-processing similar to :tacn:`nra`. The obtained goal is
   solved using the linear integer prover :tacn:`lia`.

`psatz`: a proof procedure for non-linear arithmetic
----------------------------------------------------

.. tacn:: psatz
   :name: psatz

   This tactic explores the *Cone* by increasing degrees – hence the
   depth parameter *n*. In theory, such a proof search is complete – if the
   goal is provable the search eventually stops. Unfortunately, the
   external oracle is using numeric (approximate) optimization techniques
   that might miss a refutation.

   To illustrate the working of the tactic, consider we wish to prove the
   following Coq goal:

.. needs csdp
.. coqdoc::

   Require Import ZArith Psatz.
   Open Scope Z_scope.
   Goal forall x, -x^2 >= 0 -> x - 1 >= 0 -> False.
   intro x.
   psatz Z 2.

As shown, such a goal is solved by ``intro x. psatz Z 2.``. The oracle returns the
cone expression :math:`2 \times (x-1) + (\mathbf{x-1}) \times (\mathbf{x−1}) + -x^2`
(polynomial hypotheses are printed in bold). By construction, this expression
belongs to :math:`\mathit{Cone}({−x^2,x -1})`. Moreover, by running :tacn:`ring` we
obtain :math:`-1`. By Theorem :ref:`Psatz <psatz_thm>`, the goal is valid.

Pre-processing of arithmetic goals
------------------------------------------

.. tacn:: zify
   :name: zify

   This tactic is internally called by :tacn:`lia` and :tacn:`nia` to support additional types e.g., :g:`nat`, :g:`positive` and :g:`N`.
   By requiring the module ``ZifyBool``, the boolean type :g:`bool` and some comparison operators are also supported.
   :tacn:`zify` can also be extended by rebinding the tactic `Zify.zify_post_hook` that is run immediately after :tacn:`zify`.

   + To support :g:`Z.div` and :g:`Z.modulo`: ``Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations``.
   + To support :g:`Z.quot` and :g:`Z.rem`: ``Ltac Zify.zify_post_hook ::= Z.quot_rem_to_equations``.
   + To support :g:`Z.div`, :g:`Z.modulo`, :g:`Z.quot`, and :g:`Z.rem`: ``Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations``.

.. tacn:: rify
   :name: rify

    Similarly to :tacn:`zify`, this tactic is internally called by :tacn:`lra` and :tacn:`nra` to support additional types and operations.
    :tacn:`rify` is enabled by requiring the module ``Rify_base``. Requiring the module ``Rify_power`` provides support for several power operators.

The following commands return information about the types and operators supported by the tactics :tacn:`zify` and :tacn:`rify`.
Currently, the only relevant values for :n:`@ident` are ``Z`` or ``R``.

.. cmd:: Show Tify InjTyp @ident
   :name: Show Tify InjTyp

   This command shows the list of types that can be injected into :n:`@ident`

.. cmd:: Show Tify BinOp @ident
   :name: Show Tify BinOp

   This command shows the list of binary operators that can be injected into :n:`@ident`

.. cmd:: Show Tify BinRel @ident
   :name: Show Tify BinRel

   This command shows the list of binary relations that can be injected into :n:`@ident`


.. cmd:: Show Tify UnOp @ident
   :name: Show Tify UnOp

   This command shows the list of unary operators that can be injected into :n:`@ident`

.. cmd:: Show Tify CstOp @ident
   :name: Show Tify CstOp

   This command shows the list of constants that can be injected into :n:`@ident`

.. cmd:: Show Tify Spec @ident
   :name: Show Tify Spec

   This command shows the list of operators over :n:`@ident` that are compiled using their specification e.g., :g:`Z.min`.

.. [#csdp] Sources and binaries can be found at https://projects.coin-or.org/Csdp
.. [#fnpsatz] Variants deal with equalities and strict inequalities.
.. [#mayfail] In practice, the oracle might fail to produce such a refutation.

.. comment in original TeX:
.. %% \paragraph{The {\tt sos} tactic} -- where {\tt sos} stands for \emph{sum of squares} -- tries to prove that a
.. %% single polynomial $p$ is positive by expressing it as a sum of squares \emph{i.e.,} $\sum_{i\in S} p_i^2$.
.. %% This amounts to searching for $p$ in the cone without generators \emph{i.e.}, $Cone(\{\})$.
