Coinductive types and corecursive functions
=============================================

.. _coinductive-types:

Coinductive types
------------------

The objects of an inductive type are well-founded with respect to the
constructors of the type. In other words, such objects contain only a
*finite* number of constructors. Coinductive types arise from relaxing
this condition, and admitting types whose objects contain an infinity of
constructors. Infinite objects are introduced by a non-ending (but
effective) process of construction, defined in terms of the constructors
of the type.

More information on coinductive definitions can be found in
:cite:`Gimenez95b,Gim98,GimCas05`.

.. cmd:: CoInductive @inductive_definition {* with @inductive_definition }
         CoInductive @record_definition {* with @record_definition }

   This command introduces a coinductive type.
   The syntax of the command is the same as the command :cmd:`Inductive`.
   No principle of induction is derived from the definition of a coinductive
   type, since such principles only make sense for inductive types.
   For coinductive types, the only elimination principle is case analysis.

   This command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(template)`, :attr:`universes(cumulative)`,
   :attr:`private(matching)`, :attr:`bypass_check(universes)`,
   :attr:`bypass_check(positivity)` and :attr:`using` attributes.

   When record syntax is used, this command also supports the
   :attr:`projections(primitive)` :term:`attribute`.

.. example::

   The type of infinite sequences of natural numbers, usually called streams,
   is an example of a coinductive type.

   .. rocqtop:: in

      CoInductive Stream : Set := Seq : nat -> Stream -> Stream.

   The usual destructors on streams :g:`hd:Stream->nat` and :g:`tl:Str->Str`
   can be defined as follows:

   .. rocqtop:: in

      Definition hd (x:Stream) := let (a,s) := x in a.
      Definition tl (x:Stream) := let (a,s) := x in s.

Definitions of coinductive predicates and blocks of mutually
coinductive definitions are also allowed.

.. example::

   The extensional equality on streams is an example of a coinductive type:

   .. rocqtop:: in

      CoInductive EqSt : Stream -> Stream -> Prop :=
        eqst : forall s1 s2:Stream,
                 hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

   In order to prove the extensional equality of two streams :g:`s1` and :g:`s2`
   we have to construct an infinite proof of equality, that is, an infinite
   object of type :g:`(EqSt s1 s2)`. We will see how to introduce infinite
   objects in Section :ref:`cofixpoint`.

Caveat
~~~~~~

The ability to define coinductive types by constructors, hereafter called
*positive coinductive types*, is known to break subject reduction. The story is
a bit long: this is due to dependent pattern-matching which implies
propositional η-equality, which itself would require full η-conversion for
subject reduction to hold, but full η-conversion is not acceptable as it would
make type checking undecidable.

Since the introduction of primitive records in Coq 8.5, an alternative
presentation is available, called *negative coinductive types*. This consists
in defining a coinductive type as a primitive record type through its
projections. Such a technique is akin to the *copattern* style that can be
found in e.g. Agda, and preserves subject reduction.

The above example can be rewritten in the following way.

.. rocqtop:: none

   Reset Stream.

.. rocqtop:: all

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

.. rocqtop:: all

   Axiom Stream_eta : forall s: Stream, s = Seq (hd s) (tl s).

More generally, as in the case of positive coinductive types, it is consistent
to further identify extensional equality of coinductive types with propositional
equality:

.. rocqtop:: all

   Axiom Stream_ext : forall (s1 s2: Stream), EqSt s1 s2 -> s1 = s2.

As of Coq 8.9, it is now advised to use negative coinductive types rather than
their positive counterparts.

.. seealso::
   :ref:`primitive_projections` for more information about negative
   records and primitive projections.

.. index::
   single: cofix

Co-recursive functions: cofix
-----------------------------

.. insertprodn term_cofix cofix_body

.. prodn::
   term_cofix ::= let cofix @cofix_body in @term
   | cofix @cofix_body {? {+ with @cofix_body } for @ident }
   cofix_body ::= @ident {* @binder } {? : @type } := @term

The expression
":n:`cofix @ident__1 @binder__1 : @type__1 with … with @ident__n @binder__n : @type__n for @ident__i`"
denotes the :math:`i`-th component of a block of terms defined by a mutual guarded
corecursion. It is the local counterpart of the :cmd:`CoFixpoint` command. When
:math:`n=1`, the ":n:`for @ident__i`" clause is omitted.

.. _cofixpoint:

Top-level definitions of corecursive functions
-----------------------------------------------

.. cmd:: CoFixpoint @cofix_definition {* with @cofix_definition }

   .. insertprodn cofix_definition cofix_definition

   .. prodn::
      cofix_definition ::= @ident_decl {* @binder } {? : @type } {? := @term } {? @decl_notations }

   This command introduces a method for constructing an infinite object of a
   coinductive type. For example, the stream containing all natural numbers can
   be introduced by applying the following method to the number :g:`O` (see
   Section :ref:`coinductive-types` for the definition of :g:`Stream`, :g:`hd`
   and :g:`tl`):

   .. rocqtop:: all

      CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).

   Unlike recursive definitions, there is no decreasing argument in a
   corecursive definition. To be admissible, a method of construction must
   provide at least one extra constructor of the infinite object for each
   iteration. A syntactical guard condition is imposed on corecursive
   definitions in order to ensure this: each recursive call in the
   definition must be protected by at least one constructor, and only by
   constructors. That is the case in the former definition, where the single
   recursive call of :g:`from` is guarded by an application of :g:`Seq`.
   On the contrary, the following recursive function does not satisfy the
   guard condition:

   .. rocqtop:: all

      Fail CoFixpoint filter (p:nat -> bool) (s:Stream) : Stream :=
        if p (hd s) then Seq (hd s) (filter p (tl s)) else filter p (tl s).

   The elimination of corecursive definition is done lazily, i.e. the
   definition is expanded only when it occurs at the head of an application
   which is the argument of a case analysis expression. In any other
   context, it is considered as a canonical expression which is completely
   evaluated. We can test this using the command :cmd:`Eval`, which computes
   the normal forms of a term:

   .. rocqtop:: all

      Eval compute in (from 0).
      Eval compute in (hd (from 0)).
      Eval compute in (tl (from 0)).

   As in the :cmd:`Fixpoint` command, the :n:`with` clause allows simultaneously
   defining several mutual cofixpoints.

   If :n:`@term` is omitted, :n:`@type` is required and Rocq enters proof mode.
   This can be used to define a term incrementally, in particular by relying on the :tacn:`refine` tactic.
   In this case, the proof should be terminated with :cmd:`Defined` in order to define a :term:`constant`
   for which the computational behavior is relevant.  See :ref:`proof-editing-mode`.
