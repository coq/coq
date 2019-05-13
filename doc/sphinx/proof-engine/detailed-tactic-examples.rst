.. _detailedexamplesoftactics:

Detailed examples of tactics
============================

This chapter presents detailed examples of certain tactics, to
illustrate their behavior.

.. _dependent-induction:

dependent induction
-------------------

The tactics ``dependent induction`` and ``dependent destruction`` are another
solution for inverting inductive predicate instances and potentially
doing induction at the same time. It is based on the ``BasicElim`` tactic
of Conor McBride which works by abstracting each argument of an
inductive instance by a variable and constraining it by equalities
afterwards. This way, the usual induction and destruct tactics can be
applied to the abstracted instance and after simplification of the
equalities we get the expected goals.

The abstracting tactic is called generalize_eqs and it takes as
argument a hypothesis to generalize. It uses the JMeq datatype
defined in Coq.Logic.JMeq, hence we need to require it before. For
example, revisiting the first example of the inversion documentation:

.. coqtop:: in reset

   Require Import Coq.Logic.JMeq.

   Inductive Le : nat -> nat -> Set :=
        | LeO : forall n:nat, Le 0 n
        | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

   Parameter P : nat -> nat -> Prop.

   Goal forall n m:nat, Le (S n) m -> P n m.

   intros n m H.

.. coqtop:: all

   generalize_eqs H.

The index ``S n`` gets abstracted by a variable here, but a corresponding
equality is added under the abstract instance so that no information
is actually lost. The goal is now almost amenable to do induction or
case analysis. One should indeed first move ``n`` into the goal to
strengthen it before doing induction, or ``n`` will be fixed in the
inductive hypotheses (this does not matter for case analysis). As a
rule of thumb, all the variables that appear inside constructors in
the indices of the hypothesis should be generalized. This is exactly
what the ``generalize_eqs_vars`` variant does:

.. coqtop:: all abort

   generalize_eqs_vars H.
   induction H.

As the hypothesis itself did not appear in the goal, we did not need
to use an heterogeneous equality to relate the new hypothesis to the
old one (which just disappeared here). However, the tactic works just
as well in this case, e.g.:

.. coqtop:: none

   Require Import Coq.Program.Equality.

.. coqtop:: in

   Parameter Q : forall (n m : nat), Le n m -> Prop.
   Goal forall n m (p : Le (S n) m), Q (S n) m p.

.. coqtop:: all

   intros n m p.
   generalize_eqs_vars p.

One drawback of this approach is that in the branches one will have to
substitute the equalities back into the instance to get the right
assumptions. Sometimes injection of constructors will also be needed
to recover the needed equalities. Also, some subgoals should be
directly solved because of inconsistent contexts arising from the
constraints on indexes. The nice thing is that we can make a tactic
based on discriminate, injection and variants of substitution to
automatically do such simplifications (which may involve the axiom K).
This is what the ``simplify_dep_elim`` tactic from ``Coq.Program.Equality``
does. For example, we might simplify the previous goals considerably:

.. coqtop:: all abort

   induction p ; simplify_dep_elim.

The higher-order tactic ``do_depind`` defined in ``Coq.Program.Equality``
takes a tactic and combines the building blocks we have seen with it:
generalizing by equalities calling the given tactic with the
generalized induction hypothesis as argument and cleaning the subgoals
with respect to equalities. Its most important instantiations
are ``dependent induction`` and ``dependent destruction`` that do induction or
simply case analysis on the generalized hypothesis. For example we can
redo what we’ve done manually with dependent destruction:

.. coqtop:: in

   Lemma ex : forall n m:nat, Le (S n) m -> P n m.

.. coqtop:: in

   intros n m H.

.. coqtop:: all abort

   dependent destruction H.

This gives essentially the same result as inversion. Now if the
destructed hypothesis actually appeared in the goal, the tactic would
still be able to invert it, contrary to dependent inversion. Consider
the following example on vectors:

.. coqtop:: in

   Set Implicit Arguments.

.. coqtop:: in

   Parameter A : Set.

.. coqtop:: in

   Inductive vector : nat -> Type :=
            | vnil : vector 0
            | vcons : A -> forall n, vector n -> vector (S n).

.. coqtop:: in

   Goal forall n, forall v : vector (S n),
            exists v' : vector n, exists a : A, v = vcons a v'.

.. coqtop:: in

   intros n v.

.. coqtop:: all

   dependent destruction v.

In this case, the ``v`` variable can be replaced in the goal by the
generalized hypothesis only when it has a type of the form ``vector (S n)``,
that is only in the second case of the destruct. The first one is
dismissed because ``S n <> 0``.


A larger example
~~~~~~~~~~~~~~~~

Let’s see how the technique works with induction on inductive
predicates on a real example. We will develop an example application
to the theory of simply-typed lambda-calculus formalized in a
dependently-typed style:

.. coqtop:: in reset

   Inductive type : Type :=
            | base : type
            | arrow : type -> type -> type.

.. coqtop:: in

   Notation " t --> t' " := (arrow t t') (at level 20, t' at next level).

.. coqtop:: in

   Inductive ctx : Type :=
            | empty : ctx
            | snoc : ctx -> type -> ctx.

.. coqtop:: in

   Notation " G , tau " := (snoc G tau) (at level 20, tau at next level).

.. coqtop:: in

   Fixpoint conc (G D : ctx) : ctx :=
            match D with
            | empty => G
            | snoc D' x => snoc (conc G D') x
            end.

.. coqtop:: in

   Notation " G ; D " := (conc G D) (at level 20).

.. coqtop:: in

   Inductive term : ctx -> type -> Type :=
            | ax : forall G tau, term (G, tau) tau
            | weak : forall G tau,
                       term G tau -> forall tau', term (G, tau') tau
            | abs : forall G tau tau',
                      term (G , tau) tau' -> term G (tau --> tau')
            | app : forall G tau tau',
                      term G (tau --> tau') -> term G tau -> term G tau'.

We have defined types and contexts which are snoc-lists of types. We
also have a ``conc`` operation that concatenates two contexts. The ``term``
datatype represents in fact the possible typing derivations of the
calculus, which are isomorphic to the well-typed terms, hence the
name. A term is either an application of:


+ the axiom rule to type a reference to the first variable in a
  context
+ the weakening rule to type an object in a larger context
+ the abstraction or lambda rule to type a function
+ the application to type an application of a function to an argument


Once we have this datatype we want to do proofs on it, like weakening:

.. coqtop:: in abort

   Lemma weakening : forall G D tau, term (G ; D) tau -> 
                     forall tau', term (G , tau' ; D) tau.

The problem here is that we can’t just use induction on the typing
derivation because it will forget about the ``G ; D`` constraint appearing
in the instance. A solution would be to rewrite the goal as:

.. coqtop:: in abort

   Lemma weakening' : forall G' tau, term G' tau ->
                      forall G D, (G ; D) = G' ->
                      forall tau', term (G, tau' ; D) tau.

With this proper separation of the index from the instance and the
right induction loading (putting ``G`` and ``D`` after the inducted-on
hypothesis), the proof will go through, but it is a very tedious
process. One is also forced to make a wrapper lemma to get back the
more natural statement. The ``dependent induction`` tactic alleviates this
trouble by doing all of this plumbing of generalizing and substituting
back automatically. Indeed we can simply write:

.. coqtop:: in

   Require Import Coq.Program.Tactics.
   Require Import Coq.Program.Equality.

.. coqtop:: in

   Lemma weakening : forall G D tau, term (G ; D) tau ->
                     forall tau', term (G , tau' ; D) tau.

.. coqtop:: in

   Proof with simpl in * ; simpl_depind ; auto.

.. coqtop:: in

   intros G D tau H. dependent induction H generalizing G D ; intros.

This call to dependent induction has an additional arguments which is
a list of variables appearing in the instance that should be
generalized in the goal, so that they can vary in the induction
hypotheses. By default, all variables appearing inside constructors
(except in a parameter position) of the instantiated hypothesis will
be generalized automatically but one can always give the list
explicitly.

.. coqtop:: all

   Show.

The ``simpl_depind`` tactic includes an automatic tactic that tries to
simplify equalities appearing at the beginning of induction
hypotheses, generally using trivial applications of ``reflexivity``. In
cases where the equality is not between constructor forms though, one
must help the automation by giving some arguments, using the
``specialize`` tactic for example.

.. coqtop:: in

   destruct D... apply weak; apply ax. apply ax.

.. coqtop:: in

   destruct D...

.. coqtop:: all

   Show.

.. coqtop:: all

   specialize (IHterm G0 empty eq_refl).

Once the induction hypothesis has been narrowed to the right equality,
it can be used directly.

.. coqtop:: all

   apply weak, IHterm.

Now concluding this subgoal is easy.

.. coqtop:: in

   constructor; apply IHterm; reflexivity.

.. seealso::
   The :tacn:`induction`, :tacn:`case`, and :tacn:`inversion` tactics.


autorewrite
-----------

Here are two examples of ``autorewrite`` use. The first one ( *Ackermann
function*) shows actually a quite basic use where there is no
conditional rewriting. The second one ( *Mac Carthy function*)
involves conditional rewritings and shows how to deal with them using
the optional tactic of the ``Hint Rewrite`` command.


.. example:: Ackermann function

   .. coqtop:: in reset

      Require Import Arith.

   .. coqtop:: in

      Parameter Ack : nat -> nat -> nat.

   .. coqtop:: in

      Axiom Ack0 : forall m:nat, Ack 0 m = S m.
      Axiom Ack1 : forall n:nat, Ack (S n) 0 = Ack n 1.
      Axiom Ack2 : forall n m:nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

   .. coqtop:: in

      Hint Rewrite Ack0 Ack1 Ack2 : base0.

   .. coqtop:: all

      Lemma ResAck0 : Ack 3 2 = 29.

   .. coqtop:: all

      autorewrite with base0 using try reflexivity.

.. example:: MacCarthy function

   .. coqtop:: in reset

      Require Import Omega.

   .. coqtop:: in

      Parameter g : nat -> nat -> nat.

   .. coqtop:: in

      Axiom g0 : forall m:nat, g 0 m = m.
      Axiom g1 : forall n m:nat, (n > 0) -> (m > 100) -> g n m = g (pred n) (m - 10).
      Axiom g2 : forall n m:nat, (n > 0) -> (m <= 100) -> g n m = g (S n) (m + 11).

   .. coqtop:: in

      Hint Rewrite g0 g1 g2 using omega : base1.

   .. coqtop:: in

      Lemma Resg0 : g 1 110 = 100.

   .. coqtop:: out

      Show.

   .. coqtop:: all

      autorewrite with base1 using reflexivity || simpl.

   .. coqtop:: none

      Qed.

   .. coqtop:: all

      Lemma Resg1 : g 1 95 = 91.

   .. coqtop:: all

      autorewrite with base1 using reflexivity || simpl.

   .. coqtop:: none

      Qed.
