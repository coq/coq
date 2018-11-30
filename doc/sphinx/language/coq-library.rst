.. _thecoqlibrary:

The |Coq| library
=================

.. index::
   single: Theories


The |Coq| library is structured into two parts:

  * **The initial library**: it contains elementary logical notions and
    data-types. It constitutes the basic state of the system directly
    available when running |Coq|;

  * **The standard library**: general-purpose libraries containing various
    developments of |Coq| axiomatizations about sets, lists, sorting,
    arithmetic, etc. This library comes with the system and its modules
    are directly accessible through the ``Require`` command (see
    Section :ref:`compiled-files`);

In addition, user-provided libraries or developments are provided by
|Coq| users' community. These libraries and developments are available
for download at http://coq.inria.fr (see
Section :ref:`userscontributions`).

This chapter briefly reviews the |Coq| libraries whose contents can
also be browsed at http://coq.inria.fr/stdlib.




The basic library
-----------------

This section lists the basic notions and results which are directly
available in the standard |Coq| system. Most of these constructions
are defined in the ``Prelude`` module in directory ``theories/Init``
at the |Coq| root directory; this includes the modules
``Notations``,
``Logic``,
``Datatypes``,
``Specif``,
``Peano``,
``Wf`` and 
``Tactics``.
Module ``Logic_Type`` also makes it in the initial state.

.. _init-notations:

Notations
~~~~~~~~~

This module defines the parsing and pretty-printing of many symbols
(infixes, prefixes, etc.). However, it does not assign a meaning to
these notations. The purpose of this is to define and fix once for all
the precedence and associativity of very common notations. The main
notations fixed in the initial state are :

================  ============  ===============
Notation          Precedence    Associativity
================  ============  ===============
``_ -> _``        99            right
``_ <-> _``       95            no
``_ \/ _``        85            right
``_ /\ _``        80            right
``~ _``           75            right
``_ = _``         70            no
``_ = _ = _``     70            no
``_ = _ :> _``    70            no
``_ <> _``        70            no
``_ <> _ :> _``   70            no
``_ < _``         70            no
``_ > _``         70            no
``_ <= _``        70            no
``_ >= _``        70            no
``_ < _ < _``     70            no
``_ < _ <= _``    70            no
``_ <= _ < _``    70            no
``_ <= _ <= _``   70            no
``_ + _``         50            left
``_ || _``        50            left
``_ - _``         50            left
``_ * _``         40            left
``_      _``      40            left
``_ / _``         40            left
``- _``           35            right
``/ _``           35            right
``_ ^ _``         30            right
================  ============  ===============

.. _coq-library-logic:

Logic
~~~~~

The basic library of |Coq| comes with the definitions of standard
(intuitionistic) logical connectives (they are defined as inductive
constructions). They are equipped with an appealing syntax enriching the
subclass :token:`form` of the syntactic class :token:`term`. The syntax of
:token:`form` is shown below:

.. /!\ Please keep the blanks in the lines below, experimentally they produce
   a nice last column. Or even better, find a proper way to do this!

.. productionlist::
   form :   True                                           (True)
        : | False                                          (False)
        : | ~ `form`                                         (not)
        : | `form` /\ `form`                                   (and)
        : | `form` \/ `form`                                   (or)
        : | `form` -> `form`                                   (primitive implication)
        : | `form` <-> `form`                                  (iff)
        : | forall `ident` : `type`, `form`                      (primitive for all)
        : | exists `ident` [: `specif`], `form`                  (ex)
        : | exists2 `ident` [: `specif`], `form` & `form`          (ex2)
        : | `term` = `term`                                    (eq)
        : | `term` = `term` :> `specif`                          (eq)

.. note::

  Implication is not defined but primitive (it is a non-dependent
  product of a proposition over another proposition). There is also a
  primitive universal quantification (it is a dependent product over a
  proposition). The primitive universal quantification allows both
  first-order and higher-order quantification.

Propositional Connectives
+++++++++++++++++++++++++

.. index::
  single: Connectives
  single: True (term)
  single: I (term)
  single: False (term)
  single: not (term)
  single: and (term)
  single: conj (term)
  single: proj1 (term)
  single: proj2 (term)
  single: or (term)
  single: or_introl (term)
  single: or_intror (term)
  single: iff (term)
  single: IF_then_else (term)

First, we find propositional calculus connectives:

.. coqtop:: in

  Inductive True : Prop := I.
  Inductive False :  Prop := .
  Definition not (A: Prop) := A -> False.
  Inductive and (A B:Prop) : Prop := conj (_:A) (_:B).
  Section Projections.
   Variables A B : Prop.
   Theorem proj1 : A /\ B -> A.
   Theorem proj2 : A /\ B -> B.
  End Projections.
  Inductive or (A B:Prop) : Prop :=
  | or_introl (_:A)
  | or_intror (_:B).
  Definition iff (P Q:Prop) := (P -> Q) /\ (Q -> P).
  Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Quantifiers
+++++++++++

.. index::
  single: Quantifiers
  single: all (term)
  single: ex (term)
  single: exists (term)
  single: ex_intro (term)
  single: ex2 (term)
  single: exists2 (term)
  single: ex_intro2 (term)

Then we find first-order quantifiers:

.. coqtop:: in
  
   Definition all (A:Set) (P:A -> Prop) := forall x:A, P x.
   Inductive ex (A: Set) (P:A -> Prop) : Prop :=
    ex_intro (x:A) (_:P x).
   Inductive ex2 (A:Set) (P Q:A -> Prop) : Prop :=
    ex_intro2 (x:A) (_:P x) (_:Q x).

The following abbreviations are allowed:

======================   =======================================
``exists x:A, P``        ``ex A (fun x:A => P)``
``exists x, P``          ``ex _ (fun x => P)``
``exists2 x:A, P & Q``   ``ex2 A (fun x:A => P) (fun x:A => Q)``
``exists2 x, P & Q``     ``ex2 _ (fun x => P) (fun x => Q)``
======================   =======================================

The type annotation ``:A`` can be omitted when ``A`` can be
synthesized by the system.

.. _coq-equality:

Equality
++++++++

.. index::
  single: Equality
  single: eq (term)
  single: eq_refl (term)

Then, we find equality, defined as an inductive relation. That is,
given a type ``A`` and an ``x`` of type ``A``, the
predicate :g:`(eq A x)` is the smallest one which contains ``x``.
This definition, due to Christine Paulin-Mohring, is equivalent to
define ``eq`` as the smallest reflexive relation, and it is also
equivalent to Leibniz' equality.

.. coqtop:: in

  Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : eq A x x.

Lemmas
++++++

Finally, a few easy lemmas are provided.

.. index::
  single: absurd (term)
  single: eq_sym (term)
  single: eq_trans (term)
  single: f_equal (term)
  single: sym_not_eq (term)
  single: eq_ind_r (term)
  single: eq_rec_r (term)
  single: eq_rect (term)
  single: eq_rect_r (term)

.. coqtop:: in

  Theorem absurd : forall A C:Prop, A -> ~ A -> C.
  Section equality.
  Variables A B : Type.
  Variable f : A -> B.
  Variables x y z : A.
  Theorem eq_sym : x = y -> y = x.
  Theorem eq_trans : x = y -> y = z -> x = z.
  Theorem f_equal : x = y -> f x = f y.
  Theorem not_eq_sym : x <> y -> y <> x.
  End equality.
  Definition eq_ind_r :
   forall (A:Type) (x:A) (P:A->Prop), P x -> forall y:A, y = x -> P y.
  Definition eq_rec_r :
   forall (A:Type) (x:A) (P:A->Set), P x -> forall y:A, y = x -> P y.
  Definition eq_rect_r :
   forall (A:Type) (x:A) (P:A->Type), P x -> forall y:A, y = x -> P y.
  Hint Immediate eq_sym not_eq_sym : core.

.. index::
  single: f_equal2 ... f_equal5 (term)

The theorem ``f_equal`` is extended to functions with two to five
arguments. The theorem are names ``f_equal2``, ``f_equal3``, 
``f_equal4`` and ``f_equal5``.
For instance ``f_equal3`` is defined the following way.

.. coqtop:: in
  
  Theorem f_equal3 :
   forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B)
     (x1 y1:A1) (x2 y2:A2) (x3 y3:A3),
     x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.

.. _datatypes:

Datatypes
~~~~~~~~~

.. index::
   single: Datatypes

In the basic library, we find in ``Datatypes.v`` the definition
of the basic data-types of programming,
defined as inductive constructions over the sort ``Set``. Some of
them come with a special syntax shown below (this syntax table is common with
the next section :ref:`specification`):

.. productionlist::
   specif :  `specif` * `specif`                           (prod)
          : | `specif` + `specif`                          (sum)
          : | `specif` + { `specif` }                      (sumor)
          : | { `specif` } + { `specif` }                  (sumbool)
          : | { `ident` : `specif` | `form` }              (sig)
          : | { `ident` : `specif` | `form` & `form` }       (sig2)
          : | { `ident` : `specif` & `specif` }             (sigT)
          : | { `ident` : `specif` & `specif` & `specif` }    (sigT2)
  term : (`term`, `term`)                               (pair)


Programming
+++++++++++

.. index::
  single: Programming
  single: unit (term)
  single: tt (term)
  single: bool (term)
  single: true (term)
  single: false (term)
  single: nat (term)
  single: O (term)
  single: S (term)
  single: option (term)
  single: Some (term)
  single: None (term)
  single: identity (term)
  single: refl_identity (term)

.. coqtop:: in

  Inductive unit : Set := tt.
  Inductive bool : Set := true | false.
  Inductive nat : Set := O | S (n:nat).
  Inductive option (A:Set) : Set := Some (_:A) | None.
  Inductive identity (A:Type) (a:A) : A -> Type :=
    refl_identity : identity A a a.

Note that zero is the letter ``O``, and *not* the numeral ``0``.

The predicate ``identity`` is logically 
equivalent to equality but it lives in sort ``Type``.
It is mainly maintained for compatibility.

We then define the disjoint sum of ``A+B`` of two sets ``A`` and
``B``, and their product ``A*B``.

.. index::
  single: sum (term)
  single: A+B (term)
  single: + (term)
  single: inl (term)
  single: inr (term)
  single: prod (term)
  single: A*B (term)
  single: * (term)
  single: pair (term)
  single: fst (term)
  single: snd (term)

.. coqtop:: in

  Inductive sum (A B:Set) : Set := inl (_:A) | inr (_:B).
  Inductive prod (A B:Set) : Set := pair (_:A) (_:B).
  Section projections.
  Variables A B : Set.
  Definition fst (H: prod A B) := match H with
                                | pair _ _ x y => x
                                end.
  Definition snd (H: prod A B) := match H with
                                | pair _ _ x y => y
                                end.
  End projections.

Some operations on ``bool`` are also provided: ``andb`` (with
infix notation ``&&``), ``orb`` (with
infix notation ``||``), ``xorb``, ``implb`` and ``negb``.

.. _specification:

Specification
~~~~~~~~~~~~~

The following notions defined in module ``Specif.v`` allow to build new data-types and specifications. 
They are available with the syntax shown in the previous section :ref:`datatypes`.

For instance, given :g:`A:Type` and :g:`P:A->Prop`, the construct
:g:`{x:A | P x}` (in abstract syntax :g:`(sig A P)`) is a
``Type``. We may build elements of this set as :g:`(exist x p)`
whenever we have a witness :g:`x:A` with its justification
:g:`p:P x`.

From such a :g:`(exist x p)` we may in turn extract its witness
:g:`x:A` (using an elimination construct such as ``match``) but
*not* its justification, which stays hidden, like in an abstract
data-type. In technical terms, one says that ``sig`` is a *weak
(dependent) sum*.  A variant ``sig2`` with two predicates is also
provided.

.. index::
   single: {x:A | P x} (term)
   single: sig (term)
   single: exist (term)
   single: sig2 (term)
   single: exist2 (term)

.. coqtop:: in

  Inductive sig (A:Set) (P:A -> Prop) : Set := exist (x:A) (_:P x).
  Inductive sig2 (A:Set) (P Q:A -> Prop) : Set := 
    exist2 (x:A) (_:P x) (_:Q x).

A *strong (dependent) sum* :g:`{x:A & P x}` may be also defined,
when the predicate ``P`` is now defined as a 
constructor of types in ``Type``.

.. index::
   single: {x:A & P x} (term)
   single: sigT (term)
   single: existT (term)
   single: sigT2 (term)
   single: existT2 (term)
   single: projT1 (term)
   single: projT2 (term)

.. coqtop:: in

  Inductive sigT (A:Type) (P:A -> Type) : Type := existT (x:A) (_:P x).
  Section Projections2.
  Variable A : Type.
  Variable P : A -> Type.
  Definition projT1 (H:sigT A P) := let (x, h) := H in x.
  Definition projT2 (H:sigT A P) :=
   match H return P (projT1 H) with
    existT _ _ x h => h
   end.
  End Projections2.
  Inductive sigT2 (A: Type) (P Q:A -> Type) : Type :=
    existT2 (x:A) (_:P x) (_:Q x).

A related non-dependent construct is the constructive sum
:g:`{A}+{B}` of two propositions ``A`` and ``B``.

.. index::
  single: sumbool (term)
  single: left (term)
  single: right (term)
  single: {A}+{B} (term)

.. coqtop:: in

  Inductive sumbool (A B:Prop) : Set := left (_:A) | right (_:B).

This ``sumbool`` construct may be used as a kind of indexed boolean
data-type. An intermediate between ``sumbool`` and ``sum`` is
the mixed ``sumor`` which combines :g:`A:Set` and :g:`B:Prop`
in the construction :g:`A+{B}` in ``Set``.

.. index::
  single: sumor (term)
  single: inleft (term)
  single: inright (term)
  single: A+{B} (term)

.. coqtop:: in

  Inductive sumor (A:Set) (B:Prop) : Set :=
  | inleft (_:A)
  | inright (_:B).

We may define variants of the axiom of choice, like in Martin-Löf's
Intuitionistic Type Theory.

.. index::
  single: Choice (term)
  single: Choice2 (term)
  single: bool_choice (term)

.. coqtop:: in

  Lemma Choice :
   forall (S S':Set) (R:S -> S' -> Prop),
    (forall x:S, {y : S' | R x y}) ->
    {f : S -> S' | forall z:S, R z (f z)}.
  Lemma Choice2 :
   forall (S S':Set) (R:S -> S' -> Set),
    (forall x:S, {y : S' &  R x y}) ->
     {f : S -> S' &  forall z:S, R z (f z)}.
  Lemma bool_choice :
   forall (S:Set) (R1 R2:S -> Prop),
    (forall x:S, {R1 x} + {R2 x}) ->
    {f : S -> bool |
     forall x:S, f x = true /\ R1 x \/ f x = false /\ R2 x}.

The next construct builds a sum between a data-type :g:`A:Type` and
an exceptional value encoding errors:

.. index::
  single: Exc (term)
  single: value (term)
  single: error (term)

.. coqtop:: in

  Definition Exc := option.
  Definition value := Some.
  Definition error := None.

This module ends with theorems, relating the sorts ``Set`` or
``Type`` and ``Prop`` in a way which is consistent with the
realizability interpretation.

.. index::
  single: False_rect (term)
  single: False_rec (term)
  single: eq_rect (term)
  single: absurd_set (term)
  single: and_rect (term)

.. coqtop:: in

  Definition except := False_rec.
  Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
  Theorem and_rect2 :
   forall (A B:Prop) (P:Type), (A -> B -> P) -> A /\ B -> P.


Basic Arithmetics
~~~~~~~~~~~~~~~~~

The basic library includes a few elementary properties of natural
numbers, together with the definitions of predecessor, addition and
multiplication, in module ``Peano.v``. It also
provides a scope ``nat_scope`` gathering standard notations for
common operations (``+``, ``*``) and a decimal notation for
numbers, allowing for instance to write ``3`` for :g:`S (S (S O)))`. This also works on
the left hand side of a ``match`` expression (see for example
section :tacn:`refine`). This scope is opened by default.

.. example::

  The following example is not part of the standard library, but it
  shows the usage of the notations:

  .. coqtop:: in

    Fixpoint even (n:nat) : bool :=
     match n with
     | 0 => true
     | 1 => false
     | S (S n) => even n
     end.

.. index::
  single: eq_S (term)
  single: pred (term)
  single: pred_Sn (term)
  single: eq_add_S (term)
  single: not_eq_S (term)
  single: IsSucc (term)
  single: O_S (term)
  single: n_Sn (term)
  single: plus (term)
  single: plus_n_O (term)
  single: plus_n_Sm (term)
  single: mult (term)
  single: mult_n_O (term)
  single: mult_n_Sm (term)

Now comes the content of module ``Peano``:

.. coqtop:: in
  
  Theorem eq_S : forall x y:nat, x = y -> S x = S y.
  Definition pred (n:nat) : nat :=
   match n with
   | 0 => 0
   | S u => u
   end.
  Theorem pred_Sn : forall m:nat, m = pred (S m).
  Theorem eq_add_S : forall n m:nat, S n = S m -> n = m.
  Hint Immediate eq_add_S : core.
  Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
  Definition IsSucc (n:nat) : Prop :=
   match n with
   | 0 => False
   | S p => True
   end.
  Theorem O_S : forall n:nat, 0 <> S n.
  Theorem n_Sn : forall n:nat, n <> S n.
  Fixpoint plus (n m:nat) {struct n} : nat :=
   match n with
   | 0 => m
   | S p => S (p + m)
   end
  where "n + m" := (plus n m) : nat_scope.
  Lemma plus_n_O : forall n:nat, n = n + 0.
  Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
  Fixpoint mult (n m:nat) {struct n} : nat :=
   match n with
   | 0 => 0
   | S p => m + p * m
   end
  where "n * m" := (mult n m) : nat_scope.
  Lemma mult_n_O : forall n:nat, 0 = n * 0.
  Lemma mult_n_Sm : forall n m:nat, n * m + n = n * (S m).


Finally, it gives the definition of the usual orderings ``le``,
``lt``, ``ge`` and ``gt``.

.. index::
  single: le (term)
  single: le_n (term)
  single: le_S (term)
  single: lt (term)
  single: ge (term)
  single: gt (term)

.. coqtop:: in

  Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m:nat, n <= m -> n <= (S m).
  where "n <= m" := (le n m) : nat_scope.
  Definition lt (n m:nat) := S n <= m.
  Definition ge (n m:nat) := m <= n.
  Definition gt (n m:nat) := m < n.

Properties of these relations are not initially known, but may be
required by the user from modules ``Le`` and ``Lt``.  Finally,
``Peano`` gives some lemmas allowing pattern matching, and a double
induction principle.

.. index::
  single: nat_case (term)
  single: nat_double_ind (term)

.. coqtop:: in

  Theorem nat_case :
   forall (n:nat) (P:nat -> Prop), 
   P 0 -> (forall m:nat, P (S m)) -> P n.
  Theorem nat_double_ind :
   forall R:nat -> nat -> Prop,
    (forall n:nat, R 0 n) ->
    (forall n:nat, R (S n) 0) ->
    (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.


Well-founded recursion
~~~~~~~~~~~~~~~~~~~~~~

The basic library contains the basics of well-founded recursion and 
well-founded induction, in module ``Wf.v``.

.. index::
   single: Well foundedness
   single: Recursion
   single: Well founded induction
   single: Acc (term)
   single: Acc_inv (term)
   single: Acc_rect (term)
   single: well_founded (term)

.. coqtop:: in

  Section Well_founded.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Inductive Acc (x:A) : Prop :=
    Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.
  Lemma Acc_inv x : Acc x -> forall y:A, R y x -> Acc y.
  Definition well_founded := forall a:A, Acc a.
  Hypothesis Rwf : well_founded.
  Theorem well_founded_induction :
   forall P:A -> Set,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
  Theorem well_founded_ind :
   forall P:A -> Prop,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.

The automatically generated scheme ``Acc_rect`` 
can be used to define functions by fixpoints using
well-founded relations to justify termination. Assuming
extensionality of the functional used for the recursive call, the
fixpoint equation can be proved.

.. index::
  single: Fix_F (term)
  single: fix_eq (term)
  single: Fix_F_inv (term)
  single: Fix_F_eq (term)

.. coqtop:: in

  Section FixPoint.
  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.
  Fixpoint Fix_F (x:A) (r:Acc x) {struct r} : P x :=
    F x (fun (y:A) (p:R y x) => Fix_F y (Acc_inv x r y p)).
  Definition Fix (x:A) := Fix_F x (Rwf x).
  Hypothesis F_ext :
    forall (x:A) (f g:forall y:A, R y x -> P y),
      (forall (y:A) (p:R y x), f y p = g y p) -> F x f = F x g.
  Lemma Fix_F_eq :
   forall (x:A) (r:Acc x),
     F x (fun (y:A) (p:R y x) => Fix_F y (Acc_inv x r y p)) = Fix_F x r.
  Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F x r = Fix_F x s.
  Lemma fix_eq : forall x:A, Fix x = F x (fun (y:A) (p:R y x) => Fix y).
  End FixPoint.
  End Well_founded.

Accessing the Type level
~~~~~~~~~~~~~~~~~~~~~~~~

The standard library includes ``Type`` level definitions of counterparts of some
logic concepts and basic lemmas about them.

The module ``Datatypes`` defines ``identity``, which is the ``Type`` level counterpart
of equality:

.. index::
   single: identity (term)

.. coqtop:: in

   Inductive identity (A:Type) (a:A) : A -> Type :=
     identity_refl : identity a a.

Some properties of ``identity`` are proved in the module ``Logic_Type``, which also
provides the definition of ``Type`` level negation:

.. index::
  single: notT (term)

.. coqtop:: in

  Definition notT (A:Type) := A -> False.

Tactics
~~~~~~~

A few tactics defined at the user level are provided in the initial
state, in module ``Tactics.v``. They are listed at
http://coq.inria.fr/stdlib, in paragraph ``Init``, link ``Tactics``.


The standard library
--------------------

Survey
~~~~~~

The rest of the standard library is structured into the following 
subdirectories:

  * **Logic** : Classical logic and dependent equality
  * **Arith** : Basic Peano arithmetic
  * **PArith** : Basic positive integer arithmetic
  * **NArith** : Basic binary natural number arithmetic
  * **ZArith** : Basic relative integer arithmetic
  * **Numbers** : Various approaches to natural, integer and cyclic numbers (currently axiomatically and on top of 2^31 binary words)
  * **Bool** : Booleans (basic functions and results)
  * **Lists** : Monomorphic and polymorphic lists (basic functions and results), Streams (infinite sequences defined with co-inductive types) 
  * **Sets** : Sets (classical, constructive, finite, infinite, power set, etc.) 
  * **FSets** : Specification and implementations of finite sets and finite maps (by lists and by AVL trees)
  * **Reals** : Axiomatization of real numbers (classical, basic functions, integer part, fractional part, limit, derivative, Cauchy series, power series and results,...)
  * **Relations** : Relations (definitions and basic results)
  * **Sorting** : Sorted list (basic definitions and heapsort correctness)
  * **Strings** : 8-bits characters and strings
  * **Wellfounded** : Well-founded relations (basic results)


These directories belong to the initial load path of the system, and
the modules they provide are compiled at installation time. So they
are directly accessible with the command ``Require`` (see
Section :ref:`compiled-files`).

The different modules of the |Coq| standard library are documented
online at http://coq.inria.fr/stdlib.

Peano’s arithmetic (nat)
~~~~~~~~~~~~~~~~~~~~~~~~

.. index::
   single: Peano's arithmetic
   single: nat_scope

While in the initial state, many operations and predicates of Peano's
arithmetic are defined, further operations and results belong to other
modules. For instance, the decidability of the basic predicates are
defined here. This is provided by requiring the module ``Arith``.

The following table describes the notations available in scope
``nat_scope`` :

===============   ===================
Notation          Interpretation
===============   ===================
``_ < _``         ``lt``
``_ <= _``        ``le``
``_ > _``         ``gt``
``_ >= _``        ``ge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ + _``         ``plus``
``_ - _``         ``minus``
``_ * _``         ``mult``
===============   ===================


Notations for integer arithmetics
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. index::
  single: Arithmetical notations
  single: + (term)
  single: * (term)
  single: - (term)
  singel: / (term)
  single: <= (term)
  single: >= (term)
  single: < (term)
  single: > (term)
  single: ?= (term)
  single: mod (term)


The following table describes the syntax of expressions
for integer arithmetics. It is provided by requiring and opening the module ``ZArith`` and opening scope ``Z_scope``.
It specifies how notations are interpreted and, when not
already reserved, the precedence and associativity.

===============   ====================  ==========  =============
Notation          Interpretation        Precedence  Associativity
===============   ====================  ==========  =============
``_ < _``         ``Z.lt``
``_ <= _``        ``Z.le``
``_ > _``         ``Z.gt``
``_ >= _``        ``Z.ge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ ?= _``        ``Z.compare``         70          no
``_ + _``         ``Z.add``
``_ - _``         ``Z.sub``
``_ * _``         ``Z.mul``
``_ / _``         ``Z.div``
``_ mod _``       ``Z.modulo``          40          no
``- _``           ``Z.opp``
``_ ^ _``         ``Z.pow``
===============   ====================  ==========  =============


.. example::

  .. coqtop:: all reset

    Require Import ZArith.
    Check (2 + 3)%Z.
    Open Scope Z_scope.
    Check 2 + 3.


Real numbers library
~~~~~~~~~~~~~~~~~~~~

Notations for real numbers
++++++++++++++++++++++++++

This is provided by requiring and opening the module ``Reals`` and
opening scope ``R_scope``. This set of notations is very similar to
the notation for integer arithmetics. The inverse function was added.

===============   ===================
Notation          Interpretation
===============   ===================
``_ < _``         ``Rlt``
``_ <= _``        ``Rle``
``_ > _``         ``Rgt``
``_ >= _``        ``Rge``
``x < y < z``     ``x < y /\ y < z``
``x < y <= z``    ``x < y /\ y <= z``
``x <= y < z``    ``x <= y /\ y < z``
``x <= y <= z``   ``x <= y /\ y <= z``
``_ + _``         ``Rplus``
``_ - _``         ``Rminus``
``_ * _``         ``Rmult``
``_ / _``         ``Rdiv``
``- _``           ``Ropp``
``/ _``           ``Rinv``
``_ ^ _``         ``pow``
===============   ===================

.. example::

  .. coqtop:: all reset

    Require Import Reals.
    Check  (2 + 3)%R.
    Open Scope R_scope.
    Check 2 + 3.

Some tactics for real numbers
+++++++++++++++++++++++++++++

In addition to the powerful ``ring``, ``field`` and ``lra``
tactics (see Chapter :ref:`tactics`), there are also:

.. tacn:: discrR
  :name: discrR
  
  Proves that two real integer constants are different.

.. example::

  .. coqtop:: all reset

    Require Import DiscrR.
    Open Scope R_scope.
    Goal 5 <> 0.
    discrR.

.. tacn:: split_Rabs
  :name: split_Rabs

  Allows unfolding the ``Rabs`` constant and splits corresponding conjunctions.

.. example::

  .. coqtop:: all reset

    Require Import Reals.
    Open Scope R_scope.
    Goal forall x:R, x <= Rabs x.
    intro; split_Rabs.

.. tacn:: split_Rmult
  :name: split_Rmult
 
  Splits a condition that a product is non null into subgoals
  corresponding to the condition on each operand of the product.

.. example::

  .. coqtop:: all reset

    Require Import Reals.
    Open Scope R_scope.
    Goal forall x y z:R, x * y * z <> 0.
    intros; split_Rmult.

These tactics has been written with the tactic language |Ltac|
described in Chapter :ref:`ltac`.

List library
~~~~~~~~~~~~

.. index::
  single: Notations for lists
  single: length (term)
  single: head (term)
  single: tail (term)
  single: app (term)
  single: rev (term)
  single: nth (term)
  single: map (term)
  single: flat_map (term)
  single: fold_left (term)
  single: fold_right (term)

Some elementary operations on polymorphic lists are defined here. 
They can be accessed by requiring module ``List``.

It defines the following notions:

  * ``length``
  * ``head`` : first element (with default)
  * ``tail`` : all but first element
  * ``app`` : concatenation
  * ``rev`` : reverse
  * ``nth`` : accessing n-th element (with default)
  * ``map`` : applying a function
  * ``flat_map`` : applying a function returning lists
  * ``fold_left`` : iterator (from head to tail)
  * ``fold_right`` : iterator (from tail to head)

The following table shows notations available when opening scope ``list_scope``.

==========  ==============  ==========  =============
Notation    Interpretation  Precedence  Associativity
==========  ==============  ==========  =============
``_ ++ _``  ``app``         60          right
``_ :: _``  ``cons``        60          right
==========  ==============  ==========  =============

.. _userscontributions:

Users’ contributions
--------------------

Numerous users' contributions have been collected and are available at
URL http://coq.inria.fr/opam/www/.  On this web page, you have a list
of all contributions with informations (author, institution, quick
description, etc.) and the possibility to download them one by one.
You will also find informations on how to submit a new
contribution.
