.. _omega:

Omega: a solver for quantifier-free problems in Presburger Arithmetic
=====================================================================

:Author: Pierre Crégut

Description of ``omega``
------------------------

.. tacn:: omega

   :tacn:`omega` is a tactic for solving goals in Presburger arithmetic,
   i.e. for proving formulas made of equations and inequalities over the
   type ``nat`` of natural numbers or the type ``Z`` of binary-encoded integers.
   Formulas on ``nat`` are automatically injected into ``Z``. The procedure
   may use any hypothesis of the current proof session to solve the goal.

   Multiplication is handled by :tacn:`omega` but only goals where at
   least one of the two multiplicands of products is a constant are
   solvable. This is the restriction meant by "Presburger arithmetic".

   If the tactic cannot solve the goal, it fails with an error message.
   In any case, the computation eventually stops.

.. tacv:: romega
   :name: romega

   .. deprecated:: 8.9

      Use :tacn:`lia` instead.

Arithmetical goals recognized by ``omega``
------------------------------------------

:tacn:`omega` applies only to quantifier-free formulas built from the connectives::

   /\  \/  ~  ->

on atomic formulas. Atomic formulas are built from the predicates::

   =  <  <=  >  >=

on ``nat`` or ``Z``. In expressions of type ``nat``, :tacn:`omega` recognizes::

   +  -  *  S  O  pred

and in expressions of type ``Z``, :tacn:`omega` recognizes numeral constants and::

   +  -  *  Z.succ Z.pred

All expressions of type ``nat`` or ``Z`` not built on these
operators are considered abstractly as if they
were arbitrary variables of type ``nat`` or ``Z``.

Messages from ``omega``
-----------------------

When :tacn:`omega` does not solve the goal, one of the following errors
is generated:

.. exn:: omega can't solve this system.

  This may happen if your goal is not quantifier-free (if it is
  universally quantified, try :tacn:`intros` first; if it contains
  existentials quantifiers too, :tacn:`omega` is not strong enough to solve your
  goal). This may happen also if your goal contains arithmetical
  operators not recognized by :tacn:`omega`. Finally, your goal may be simply
  not true!

.. exn:: omega: Not a quantifier-free goal.

  If your goal is universally quantified, you should first apply
  :tacn:`intro` as many times as needed.

.. exn:: omega: Unrecognized predicate or connective: @ident.
   :undocumented:

.. exn:: omega: Unrecognized atomic proposition: ...
   :undocumented:

.. exn:: omega: Can't solve a goal with proposition variables.
   :undocumented:

.. exn:: omega: Unrecognized proposition.
   :undocumented:

.. exn:: omega: Can't solve a goal with non-linear products.
   :undocumented:

.. exn:: omega: Can't solve a goal with equality on type ...
   :undocumented:


Using ``omega``
---------------

The ``omega`` tactic does not belong to the core system. It should be
loaded by

.. coqtop:: in

   Require Import Omega.

.. example::

  .. coqtop:: all

     Require Import Omega.

     Open Scope Z_scope.

     Goal forall m n:Z, 1 + 2 * m <> 2 * n.
     intros; omega.
     Abort.

     Goal forall z:Z, z > 0 -> 2 * z + 1 > z.
     intro; omega.
     Abort.


Options
-------

.. flag:: Stable Omega

   .. deprecated:: 8.5

   This deprecated option (on by default) is for compatibility with Coq pre 8.5. It
   resets internal name counters to make executions of :tacn:`omega` independent.

.. flag:: Omega UseLocalDefs

   This option (on by default) allows :tacn:`omega` to use the bodies of local
   variables.

.. flag:: Omega System

   This option (off by default) activate the printing of debug information

.. flag:: Omega Action

   This option (off by default) activate the printing of debug information

Technical data
--------------

Overview of the tactic
~~~~~~~~~~~~~~~~~~~~~~

 * The goal is negated twice and the first negation is introduced as a hypothesis.
 * Hypotheses are decomposed in simple equations or inequalities. Multiple
   goals may result from this phase.
 * Equations and inequalities over ``nat`` are translated over
   ``Z``, multiple goals may result from the translation of subtraction.
 * Equations and inequalities are normalized.
 * Goals are solved by the OMEGA decision procedure.
 * The script of the solution is replayed.

Overview of the OMEGA decision procedure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The OMEGA decision procedure involved in the :tacn:`omega` tactic uses
a small subset of the decision procedure presented in :cite:`TheOmegaPaper`
Here is an overview, refer to the original paper for more information.

 * Equations and inequalities are normalized by division by the GCD of their
   coefficients.
 * Equations are eliminated, using the Banerjee test to get a coefficient
   equal to one.
 * Note that each inequality cuts the Euclidean space in half.
 * Inequalities are solved by projecting on the hyperspace
   defined by cancelling one of the variables. They are partitioned
   according to the sign of the coefficient of the eliminated
   variable. Pairs of inequalities from different classes define a
   new edge in the projection.
 * Redundant inequalities are eliminated or merged in new
   equations that can be eliminated by the Banerjee test.
 * The last two steps are iterated until a contradiction is reached
   (success) or there is no more variable to eliminate (failure).

It may happen that there is a real solution and no integer one. The last
steps of the Omega procedure are not implemented, so the
decision procedure is only partial.

Bugs
----

 * The simplification procedure is very dumb and this results in
   many redundant cases to explore.

 * Much too slow.

 * Certainly other bugs! You can report them to https://coq.inria.fr/bugs/.
