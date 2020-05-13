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
make type checking undecidable.

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
