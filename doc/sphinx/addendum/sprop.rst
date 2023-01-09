.. _sprop:

SProp (proof irrelevant propositions)
=====================================

.. warning::

   The status of strict propositions is experimental.

   In particular, conversion checking through bytecode or native code
   compilation currently does not understand proof irrelevance.

This section describes the extension of Coq with definitionally
proof irrelevant propositions (types in the sort :math:`\SProp`, also
known as strict propositions) as described in
:cite:`Gilbert:POPL2019`.

Use of |SProp| may be disabled by passing ``-disallow-sprop`` to the
Coq program or by turning the :flag:`Allow StrictProp` flag off.

.. flag:: Allow StrictProp

   This :term:`flag` enables or disables the use of |SProp|.  It is enabled by default.
   The command-line flag ``-disallow-sprop`` disables |SProp| at
   startup.

   .. exn:: SProp is disallowed because the "Allow StrictProp" flag is off.
      :undocumented:

Some of the definitions described in this document are available
through ``Coq.Logic.StrictProp``, which see.

Basic constructs
----------------

The purpose of :math:`\SProp` is to provide types where all elements
are convertible:

.. coqtop:: all

   Theorem irrelevance (A : SProp) (P : A -> Prop) : forall x : A, P x -> forall y : A, P y.
   Proof.
   intros * Hx *.
   exact Hx.
   Qed.

Since we have definitional :ref:`eta-expansion-sect` for
functions, the property of being a type of definitionally irrelevant
values is impredicative, and so is :math:`\SProp`:

.. coqtop:: all

   Check fun (A:Type) (B:A -> SProp) => (forall x:A, B x) : SProp.

In order to keep conversion tractable, cumulativity for :math:`\SProp`
is forbidden, unless the :flag:`Cumulative StrictProp` flag is turned
on:

.. coqtop:: all

   Fail Check (fun (A:SProp) => A : Type).
   Set Cumulative StrictProp.
   Check (fun (A:SProp) => A : Type).

.. coqtop:: none

   Unset Cumulative StrictProp.

We can explicitly lift strict propositions into the relevant world by
using a wrapping inductive type. The inductive stops definitional
proof irrelevance from escaping.

.. coqtop:: in

   Inductive Box (A:SProp) : Prop := box : A -> Box A.
   Arguments box {_} _.

.. coqtop:: all

   Fail Check fun (A:SProp) (x y : Box A) => eq_refl : x = y.

.. doesn't get merged with the above if coqdoc
.. coqtop:: in

   Definition box_irrelevant (A:SProp) (x y : Box A) : x = y
     := match x, y with box x, box y => eq_refl end.

In the other direction, we can use impredicativity to "squash" a
relevant type, making an irrelevant approximation.

.. coqdoc::

  Definition iSquash (A:Type) : SProp
    := forall P : SProp, (A -> P) -> P.
  Definition isquash A : A -> iSquash A
    := fun a P f => f a.
  Definition iSquash_sind A (P : iSquash A -> SProp) (H : forall x : A, P (isquash A x))
    : forall x : iSquash A, P x
    := fun x => x (P x) (H : A -> P x).

Or more conveniently (but equivalently)

.. coqdoc::

  Inductive Squash (A:Type) : SProp := squash : A -> Squash A.

Most inductives types defined in :math:`\SProp` are squashed types,
i.e. they can only be eliminated to construct proofs of other strict
propositions. Empty types are the only exception.

.. coqtop:: in

   Inductive sEmpty : SProp := .

.. coqtop:: all

   Check sEmpty_rect.

.. note::

   Eliminators to strict propositions are called ``foo_sind``, in the
   same way that eliminators to propositions are called ``foo_ind``.

Primitive records in :math:`\SProp` are allowed when fields are strict
propositions, for instance:

.. coqtop:: in

   Set Primitive Projections.
   Record sProd (A B : SProp) : SProp := { sfst : A; ssnd : B }.

On the other hand, to avoid having definitionally irrelevant types in
non-:math:`\SProp` sorts (through record η-extensionality), primitive
records in relevant sorts must have at least one relevant field.

.. coqtop:: all

   Set Warnings "+non-primitive-record".
   Fail Record rBox (A:SProp) : Prop := rbox { runbox : A }.

.. coqdoc::

   Record ssig (A:Type) (P:A -> SProp) : Type := { spr1 : A; spr2 : P spr1 }.

Note that ``rBox`` works as an emulated record, which is equivalent to
the Box inductive.

Encodings for strict propositions
---------------------------------

The elimination for unit types can be encoded by a trivial function
thanks to proof irrelevance:

.. coqdoc::

   Inductive sUnit : SProp := stt.
   Definition sUnit_rect (P:sUnit->Type) (v:P stt) (x:sUnit) : P x := v.

By using empty and unit types as base values, we can encode other
strict propositions. For instance:

.. coqdoc::

  Definition is_true (b:bool) : SProp := if b then sUnit else sEmpty.

  Definition is_true_eq_true b : is_true b -> true = b
    := match b with
       | true => fun _ => eq_refl
       | false => sEmpty_ind _
       end.

  Definition eq_true_is_true b (H:true=b) : is_true b
    := match H in _ = x return is_true x with eq_refl => stt end.

Definitional UIP
----------------

.. flag:: Definitional UIP

   This :term:`flag`, off by default, allows the declaration of non-squashed
   inductive types with 1 constructor which takes no argument in
   |SProp|. Since this includes equality types, it provides
   definitional uniqueness of identity proofs.

   Because squashing is a universe restriction, unsetting
   :flag:`Universe Checking` is stronger than setting
   :flag:`Definitional UIP`.

Definitional UIP involves a special reduction rule through which
reduction depends on conversion. Consider the following code:

.. coqtop:: in

   Set Definitional UIP.

   Inductive seq {A} (a:A) : A -> SProp :=
     srefl : seq a a.

   Axiom e : seq 0 0.
   Definition hidden_arrow := match e return Set with srefl _ => nat -> nat end.

   Check (fun (f : hidden_arrow) (x:nat) => (f : nat -> nat) x).

By the usual reduction rules :g:`hidden_arrow` is a stuck match, but
by proof irrelevance :g:`e` is convertible to :g:`srefl 0` and then by
congruence :g:`hidden_arrow` is convertible to `nat -> nat`.

The special reduction reduces any match on a type which uses
definitional UIP when the indices are convertible to those of the
constructor. For `seq`, this means a match on a value of type `seq x
y` reduces if and only if `x` and `y` are convertible.

Such matches are indicated in the printed representation by inserting
a cast around the discriminee:

.. coqtop:: out

   Print hidden_arrow.

Non Termination with UIP
++++++++++++++++++++++++

The special reduction rule of UIP combined with an impredicative sort
breaks termination of reduction
:cite:`abel19:failur_normal_impred_type_theor`:

.. coqtop:: all

   Axiom all_eq : forall (P Q:Prop), P -> Q -> seq P Q.

   Definition transport (P Q:Prop) (x:P) (y:Q) : Q
   := match all_eq P Q x y with srefl _ => x end.

   Definition top : Prop := forall P : Prop, P -> P.

   Definition c : top :=
     fun P p =>
     transport
     (top -> top)
     P
     (fun x : top => x (top -> top) (fun x => x) x)
     p.

   Fail Timeout 1 Eval lazy in c (top -> top) (fun x => x) c.

The term :g:`c (top -> top) (fun x => x) c` infinitely reduces to itself.

Issues with non-cumulativity
----------------------------

During normal term elaboration, we don't always know that a type is a
strict proposition early enough. For instance:

.. coqdoc::

   Definition constant_0 : ?[T] -> nat := fun _ : sUnit => 0.

While checking the type of the constant, we only know that ``?[T]``
must inhabit some sort. Putting it in some floating universe ``u``
would disallow instantiating it by ``sUnit : SProp``.

In order to make the system usable without having to annotate every
instance of :math:`\SProp`, we consider :math:`\SProp` to be a subtype
of every universe during elaboration (i.e. outside the kernel). Then
once we have a fully elaborated term it is sent to the kernel which
will check that we didn't actually need cumulativity of :math:`\SProp`
(in the example above, ``u`` doesn't appear in the final term).

This means that some errors will be delayed until ``Qed``:

.. coqtop:: in

   Lemma foo : Prop.
   Proof. pose (fun A : SProp => A : Type); exact True.

.. coqtop:: all

   Fail Qed.

.. coqtop:: in

   Abort.

.. flag:: Elaboration StrictProp Cumulativity

   Unset this :term:`flag` (it is on by default) to be strict with regard to
   :math:`\SProp` cumulativity during elaboration.

The implementation of proof irrelevance uses inferred "relevance"
marks on binders to determine which variables are irrelevant. Together
with non-cumulativity this allows us to avoid retyping during
conversion.

.. warn:: Bad relevance

  This is a developer warning, disabled by default. It is emitted by
  the kernel when it is passed a term with incorrect relevance marks.
  To avoid conversion issues you may wish to use
  it to find when your tactics are producing incorrect marks.

.. flag:: Cumulative StrictProp

   Set this :term:`flag` (it is off by default) to make the kernel accept
   cumulativity between |SProp| and other universes. This makes
   typechecking incomplete.
