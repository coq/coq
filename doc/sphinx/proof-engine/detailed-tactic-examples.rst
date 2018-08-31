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

   Variable P : nat -> nat -> Prop.

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

.. coqtop:: all

   generalize_eqs_vars H.
   induction H.

As the hypothesis itself did not appear in the goal, we did not need
to use an heterogeneous equality to relate the new hypothesis to the
old one (which just disappeared here). However, the tactic works just
as well in this case, e.g.:

.. coqtop:: none

   Abort.

.. coqtop:: in

   Variable Q : forall (n m : nat), Le n m -> Prop.
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

.. coqtop:: all

   Require Import Coq.Program.Equality.

.. coqtop:: all

   induction p ; simplify_dep_elim.

The higher-order tactic ``do_depind`` defined in ``Coq.Program.Equality``
takes a tactic and combines the building blocks we have seen with it:
generalizing by equalities calling the given tactic with the
generalized induction hypothesis as argument and cleaning the subgoals
with respect to equalities. Its most important instantiations
are ``dependent induction`` and ``dependent destruction`` that do induction or
simply case analysis on the generalized hypothesis. For example we can
redo what we’ve done manually with dependent destruction:

.. coqtop:: none

   Abort.

.. coqtop:: in

   Lemma ex : forall n m:nat, Le (S n) m -> P n m.

.. coqtop:: in

   intros n m H.

.. coqtop:: all

   dependent destruction H.

This gives essentially the same result as inversion. Now if the
destructed hypothesis actually appeared in the goal, the tactic would
still be able to invert it, contrary to dependent inversion. Consider
the following example on vectors:

.. coqtop:: none

   Abort.

.. coqtop:: in

   Set Implicit Arguments.

.. coqtop:: in

   Variable A : Set.

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

.. coqtop:: in

   Lemma weakening : forall G D tau, term (G ; D) tau -> 
                     forall tau', term (G , tau' ; D) tau.

.. coqtop:: none

   Abort.

The problem here is that we can’t just use induction on the typing
derivation because it will forget about the ``G ; D`` constraint appearing
in the instance. A solution would be to rewrite the goal as:

.. coqtop:: in

   Lemma weakening' : forall G' tau, term G' tau ->
                      forall G D, (G ; D) = G' ->
                      forall tau', term (G, tau' ; D) tau.

.. coqtop:: none

   Abort.

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

      Variable Ack : nat -> nat -> nat.

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

      Variable g : nat -> nat -> nat.

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

.. _quote:

quote
-----

The tactic ``quote`` allows using Barendregt’s so-called 2-level approach
without writing any ML code. Suppose you have a language ``L`` of
'abstract terms' and a type ``A`` of 'concrete terms' and a function ``f : L -> A``.
If ``L`` is a simple inductive datatype and ``f`` a simple fixpoint,
``quote f`` will replace the head of current goal by a convertible term of
the form ``(f t)``. ``L`` must have a constructor of type: ``A -> L``.

Here is an example:

.. coqtop:: in reset

   Require Import Quote.

.. coqtop:: all

   Parameters A B C : Prop.

.. coqtop:: all

   Inductive formula : Type :=
            | f_and : formula -> formula -> formula (* binary constructor *)
            | f_or : formula -> formula -> formula
            | f_not : formula -> formula (* unary constructor *)
            | f_true : formula (* 0-ary constructor *)
            | f_const : Prop -> formula (* constructor for constants *).

.. coqtop:: all

   Fixpoint interp_f (f:formula) : Prop :=
            match f with
            | f_and f1 f2 => interp_f f1 /\ interp_f f2
            | f_or f1 f2 => interp_f f1 \/ interp_f f2
            | f_not f1 => ~ interp_f f1
            | f_true => True
            | f_const c => c
            end.

.. coqtop:: all

   Goal A /\ (A \/ True) /\ ~ B /\ (A <-> A).

.. coqtop:: all

   quote interp_f.

The algorithm to perform this inversion is: try to match the term with
right-hand sides expression of ``f``. If there is a match, apply the
corresponding left-hand side and call yourself recursively on sub-
terms. If there is no match, we are at a leaf: return the
corresponding constructor (here ``f_const``) applied to the term.

When ``quote`` is not able to perform inversion properly, it will error out with
:exn:`quote: not a simple fixpoint`.


Introducing variables map
~~~~~~~~~~~~~~~~~~~~~~~~~

The normal use of quote is to make proofs by reflection: one defines a
function ``simplify : formula -> formula`` and proves a theorem
``simplify_ok: (f:formula)(interp_f (simplify f)) -> (interp_f f)``. Then,
one can simplify formulas by doing:

.. coqtop:: in

       quote interp_f.
       apply simplify_ok.
       compute.

But there is a problem with leafs: in the example above one cannot
write a function that implements, for example, the logical
simplifications :math:`A \wedge A \rightarrow A` or :math:`A \wedge
\lnot A \rightarrow \mathrm{False}`. This is because ``Prop`` is
impredicative.

It is better to use that type of formulas:

.. coqtop:: in reset

   Require Import Quote.

.. coqtop:: in

   Parameters A B C : Prop.

.. coqtop:: all

   Inductive formula : Set :=
            | f_and : formula -> formula -> formula
            | f_or : formula -> formula -> formula
            | f_not : formula -> formula
            | f_true : formula
            | f_atom : index -> formula.

``index`` is defined in module ``Quote``. Equality on that type is
decidable so we are able to simplify :math:`A \wedge A` into :math:`A`
at the abstract level.

When there are variables, there are bindings, and ``quote`` also
provides a type ``(varmap A)`` of bindings from index to any set
``A``, and a function ``varmap_find`` to search in such maps. The
interpretation function also has another argument, a variables map:

.. coqtop:: all

   Fixpoint interp_f (vm:varmap Prop) (f:formula) {struct f} : Prop :=
            match f with
            | f_and f1 f2 => interp_f vm f1 /\ interp_f vm f2
            | f_or f1 f2 => interp_f vm f1 \/ interp_f vm f2
            | f_not f1 => ~ interp_f vm f1
            | f_true => True
            | f_atom i => varmap_find True i vm
            end.

``quote`` handles this second case properly:

.. coqtop:: all

   Goal A /\ (B \/ A) /\ (A \/ ~ B).

.. coqtop:: all

   quote interp_f.

It builds ``vm`` and ``t`` such that ``(f vm t)`` is convertible with the
conclusion of current goal.


Combining variables and constants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One can have both variables and constants in abstracts terms; for
example, this is the case for the :tacn:`ring` tactic. Then one must provide to
``quote`` a list of *constructors of constants*. For example, if the list
is ``[O S]`` then closed natural numbers will be considered as constants
and other terms as variables.

.. coqtop:: in reset

   Require Import Quote.

.. coqtop:: in

   Parameters A B C : Prop.

.. coqtop:: in

   Inductive formula : Type :=
            | f_and : formula -> formula -> formula
            | f_or : formula -> formula -> formula
            | f_not : formula -> formula
            | f_true : formula
            | f_const : Prop -> formula (* constructor for constants *)
            | f_atom : index -> formula.

.. coqtop:: in

   Fixpoint interp_f (vm:varmap Prop) (f:formula) {struct f} : Prop :=
            match f with
            | f_and f1 f2 => interp_f vm f1 /\ interp_f vm f2
            | f_or f1 f2 => interp_f vm f1 \/ interp_f vm f2
            | f_not f1 => ~ interp_f vm f1
            | f_true => True
            | f_const c => c
            | f_atom i => varmap_find True i vm
            end.

.. coqtop:: in

   Goal A /\ (A \/ True) /\ ~ B /\ (C <-> C).

.. coqtop:: all

   quote interp_f [ A B ].


.. coqtop:: all

   Undo.

.. coqtop:: all

   quote interp_f [ B C iff ].

.. warning::
   Since functional inversion is undecidable in the general case,
   don’t expect miracles from it!

.. tacv:: quote @ident in @term using @tactic

   ``tactic`` must be a functional tactic (starting with ``fun x =>``) and
   will be called with the quoted version of term according to ``ident``.

.. tacv:: quote @ident [{+ @ident}] in @term using @tactic          

   Same as above, but will use the additional ``ident`` list to chose
   which subterms are constants (see above).

.. seealso::
   Comments from the source file ``plugins/quote/quote.ml``

.. seealso::
   The :tacn:`ring` tactic.


Using the tactic language
---------------------------


About the cardinality of the set of natural numbers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The first example which shows how to use pattern matching over the
proof context is a proof of the fact that natural numbers have more
than two elements. This can be done as follows:

.. coqtop:: in reset

   Lemma card_nat :
     ~ exists x : nat, exists y : nat, forall z:nat, x = z \/ y = z.
   Proof.

.. coqtop:: in

   red; intros (x, (y, Hy)).

.. coqtop:: in

   elim (Hy 0); elim (Hy 1); elim (Hy 2); intros;

   match goal with
       | _ : ?a = ?b, _ : ?a = ?c |- _ =>
           cut (b = c); [ discriminate | transitivity a; auto ]
   end.

.. coqtop:: in

   Qed.

We can notice that all the (very similar) cases coming from the three
eliminations (with three distinct natural numbers) are successfully
solved by a match goal structure and, in particular, with only one
pattern (use of non-linear matching).


Permutations of lists
~~~~~~~~~~~~~~~~~~~~~~~~~~~

A more complex example is the problem of permutations of
lists. The aim is to show that a list is a permutation of
another list.

.. coqtop:: in reset

   Section Sort.

.. coqtop:: in

   Variable A : Set.

.. coqtop:: in

   Inductive perm : list A -> list A -> Prop :=
       | perm_refl : forall l, perm l l
       | perm_cons : forall a l0 l1, perm l0 l1 -> perm (a :: l0) (a :: l1)
       | perm_append : forall a l, perm (a :: l) (l ++ a :: nil)
       | perm_trans : forall l0 l1 l2, perm l0 l1 -> perm l1 l2 -> perm l0 l2.

.. coqtop:: in

   End Sort.

First, we define the permutation predicate as shown above.

.. coqtop:: none

   Require Import List.


.. coqtop:: in

   Ltac perm_aux n :=
   match goal with
       | |- (perm _ ?l ?l) => apply perm_refl
       | |- (perm _ (?a :: ?l1) (?a :: ?l2)) =>
           let newn := eval compute in (length l1) in
               (apply perm_cons; perm_aux newn)
       | |- (perm ?A (?a :: ?l1) ?l2) =>
           match eval compute in n with
               | 1 => fail
               | _ =>
                   let l1' := constr:(l1 ++ a :: nil) in
                       (apply (perm_trans A (a :: l1) l1' l2);
                       [ apply perm_append | compute; perm_aux (pred n) ])
           end
   end.

Next we define an auxiliary tactic ``perm_aux`` which takes an argument
used to control the recursion depth. This tactic behaves as follows. If
the lists are identical (i.e. convertible), it concludes. Otherwise, if
the lists have identical heads, it proceeds to look at their tails.
Finally, if the lists have different heads, it rotates the first list by
putting its head at the end if the new head hasn't been the head previously. To check this, we keep track of the
number of performed rotations using the argument ``n``. We do this by
decrementing ``n`` each time we perform a rotation. It works because
for a list of length ``n`` we can make exactly ``n - 1`` rotations
to generate at most ``n`` distinct lists. Notice that we use the natural
numbers of Coq for the rotation counter. From :ref:`ltac-syntax` we know
that it is possible to use the usual natural numbers, but they are only
used as arguments for primitive tactics and they cannot be handled, so,
in particular, we cannot make computations with them. Thus the natural
choice is to use Coq data structures so that Coq makes the computations
(reductions) by ``eval compute in`` and we can get the terms back by match.

.. coqtop:: in

   Ltac solve_perm :=
   match goal with
       | |- (perm _ ?l1 ?l2) =>
           match eval compute in (length l1 = length l2) with
               | (?n = ?n) => perm_aux n
           end
   end.

The main tactic is ``solve_perm``. It computes the lengths of the two lists
and uses them as arguments to call ``perm_aux`` if the lengths are equal (if they
aren't, the lists cannot be permutations of each other). Using this tactic we
can now prove lemmas as follows:

.. coqtop:: in

   Lemma solve_perm_ex1 :
     perm nat (1 :: 2 :: 3 :: nil) (3 :: 2 :: 1 :: nil).
   Proof. solve_perm. Qed.

.. coqtop:: in

   Lemma solve_perm_ex2 :
     perm nat
       (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil)
         (0 :: 2 :: 4 :: 6 :: 8 :: 9 :: 7 :: 5 :: 3 :: 1 :: nil).
   Proof. solve_perm. Qed.

Deciding intuitionistic propositional logic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Pattern matching on goals allows a powerful backtracking when returning tactic
values. An interesting application is the problem of deciding intuitionistic
propositional logic. Considering the contraction-free sequent calculi LJT* of
Roy Dyckhoff :cite:`Dyc92`, it is quite natural to code such a tactic using the
tactic language as shown below.

.. coqtop:: in reset

   Ltac basic :=
   match goal with
       | |- True => trivial
       | _ : False |- _ => contradiction
       | _ : ?A |- ?A => assumption
   end.

.. coqtop:: in

   Ltac simplify :=
   repeat (intros;
       match goal with
           | H : ~ _ |- _ => red in H
           | H : _ /\ _ |- _ =>
               elim H; do 2 intro; clear H
           | H : _ \/ _ |- _ =>
               elim H; intro; clear H
           | H : ?A /\ ?B -> ?C |- _ =>
               cut (A -> B -> C);
                   [ intro | intros; apply H; split; assumption ]
           | H: ?A \/ ?B -> ?C |- _ =>
               cut (B -> C);
                   [ cut (A -> C);
                       [ intros; clear H
                       | intro; apply H; left; assumption ]
                   | intro; apply H; right; assumption ]
           | H0 : ?A -> ?B, H1 : ?A |- _ =>
               cut B; [ intro; clear H0 | apply H0; assumption ]
           | |- _ /\ _ => split
           | |- ~ _ => red
       end).

.. coqtop:: in

   Ltac my_tauto :=
     simplify; basic ||
     match goal with
         | H : (?A -> ?B) -> ?C |- _ =>
             cut (B -> C);
                 [ intro; cut (A -> B);
                     [ intro; cut C;
                         [ intro; clear H | apply H; assumption ]
                     | clear H ]
                 | intro; apply H; intro; assumption ]; my_tauto
         | H : ~ ?A -> ?B |- _ =>
             cut (False -> B);
                 [ intro; cut (A -> False);
                     [ intro; cut B;
                         [ intro; clear H | apply H; assumption ]
                     | clear H ]
                 | intro; apply H; red; intro; assumption ]; my_tauto
         | |- _ \/ _ => (left; my_tauto) || (right; my_tauto)
     end.

The tactic ``basic`` tries to reason using simple rules involving truth, falsity
and available assumptions. The tactic ``simplify`` applies all the reversible
rules of Dyckhoff’s system. Finally, the tactic ``my_tauto`` (the main
tactic to be called) simplifies with ``simplify``, tries to conclude with
``basic`` and tries several paths using the backtracking rules (one of the
four Dyckhoff’s rules for the left implication to get rid of the contraction
and the right ``or``).

Having defined ``my_tauto``, we can prove tautologies like these:

.. coqtop:: in

   Lemma my_tauto_ex1 :
     forall A B : Prop, A /\ B -> A \/ B.
   Proof. my_tauto. Qed.

.. coqtop:: in

   Lemma my_tauto_ex2 :
     forall A B : Prop, (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.
   Proof. my_tauto. Qed.


Deciding type isomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~

A more tricky problem is to decide equalities between types modulo
isomorphisms. Here, we choose to use the isomorphisms of the simply
typed λ-calculus with Cartesian product and unit type (see, for
example, :cite:`RC95`). The axioms of this λ-calculus are given below.

.. coqtop:: in reset

   Open Scope type_scope.

.. coqtop:: in

   Section Iso_axioms.

.. coqtop:: in

   Variables A B C : Set.

.. coqtop:: in

   Axiom Com : A * B = B * A.

   Axiom Ass : A * (B * C) = A * B * C.

   Axiom Cur : (A * B -> C) = (A -> B -> C).

   Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).

   Axiom P_unit : A * unit = A.

   Axiom AR_unit : (A -> unit) = unit.

   Axiom AL_unit : (unit -> A) = A.

.. coqtop:: in

   Lemma Cons : B = C -> A * B = A * C.

   Proof.

   intro Heq; rewrite Heq; reflexivity.

   Qed.

.. coqtop:: in

   End Iso_axioms.

.. coqtop:: in

   Ltac simplify_type ty :=
   match ty with
       | ?A * ?B * ?C =>
           rewrite <- (Ass A B C); try simplify_type_eq
       | ?A * ?B -> ?C =>
           rewrite (Cur A B C); try simplify_type_eq
       | ?A -> ?B * ?C =>
           rewrite (Dis A B C); try simplify_type_eq
       | ?A * unit =>
           rewrite (P_unit A); try simplify_type_eq
       | unit * ?B =>
           rewrite (Com unit B); try simplify_type_eq
       | ?A -> unit =>
           rewrite (AR_unit A); try simplify_type_eq
       | unit -> ?B =>
           rewrite (AL_unit B); try simplify_type_eq
       | ?A * ?B =>
           (simplify_type A; try simplify_type_eq) ||
           (simplify_type B; try simplify_type_eq)
       | ?A -> ?B =>
           (simplify_type A; try simplify_type_eq) ||
           (simplify_type B; try simplify_type_eq)
   end
   with simplify_type_eq :=
   match goal with
       | |- ?A = ?B => try simplify_type A; try simplify_type B
   end.

.. coqtop:: in

   Ltac len trm :=
   match trm with
       | _ * ?B => let succ := len B in constr:(S succ)
       | _ => constr:(1)
   end.

.. coqtop:: in

   Ltac assoc := repeat rewrite <- Ass.

.. coqtop:: in

   Ltac solve_type_eq n :=
   match goal with
       | |- ?A = ?A => reflexivity
       | |- ?A * ?B = ?A * ?C =>
           apply Cons; let newn := len B in solve_type_eq newn
       | |- ?A * ?B = ?C =>
           match eval compute in n with
               | 1 => fail
               | _ =>
                   pattern (A * B) at 1; rewrite Com; assoc; solve_type_eq (pred n)
           end
   end.

.. coqtop:: in

   Ltac compare_structure :=
   match goal with
       | |- ?A = ?B =>
           let l1 := len A
           with l2 := len B in
               match eval compute in (l1 = l2) with
                   | ?n = ?n => solve_type_eq n
               end
   end.

.. coqtop:: in

   Ltac solve_iso := simplify_type_eq; compare_structure.

The tactic to judge equalities modulo this axiomatization is shown above.
The algorithm is quite simple. First types are simplified using axioms that
can be oriented (this is done by ``simplify_type`` and ``simplify_type_eq``).
The normal forms are sequences of Cartesian products without Cartesian product
in the left component. These normal forms are then compared modulo permutation
of the components by the tactic ``compare_structure``. If they have the same
lengths, the tactic ``solve_type_eq`` attempts to prove that the types are equal.
The main tactic that puts all these components together is called ``solve_iso``.

Here are examples of what can be solved by ``solve_iso``.

.. coqtop:: in

   Lemma solve_iso_ex1 :
     forall A B : Set, A * unit * B = B * (unit * A).
   Proof.
     intros; solve_iso.
   Qed.

.. coqtop:: in

   Lemma solve_iso_ex2 :
     forall A B C : Set,
       (A * unit -> B * (C * unit)) =
       (A * unit -> (C -> unit) * C) * (unit -> A -> B).
   Proof.
     intros; solve_iso.
   Qed.
