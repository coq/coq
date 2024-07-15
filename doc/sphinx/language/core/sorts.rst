.. index::
   single: Set (sort)
   single: SProp
   single: Prop
   single: Type

.. _sorts:

Sorts
~~~~~~~~~~~

.. insertprodn sort universe_expr

.. prodn::
   sort ::= Set
   | Prop
   | SProp
   | Type
   | Type @%{ _ %}
   | Type @%{ {? @qualid %| } @universe %}
   universe ::= max ( {+, @universe_expr } )
   | _
   | @universe_expr
   universe_expr ::= @universe_name {? + @natural }

The types of types are called :gdef:`sorts <sort>`.

All sorts have a type and there is an infinite well-founded typing
hierarchy of sorts whose base sorts are :math:`\SProp`, :math:`\Prop`
and :math:`\Set`.

The sort :math:`\Prop` intends to be the type of logical propositions. If :math:`M` is a
logical proposition then it denotes the class of terms representing
proofs of :math:`M`. An object :math:`m` belonging to :math:`M`
witnesses the fact that :math:`M` is
provable. An object of type :math:`\Prop` is called a :gdef:`proposition`.
We denote propositions by :n:`@form`.
This constitutes a semantic subclass of the syntactic class :n:`@term`.

The sort :math:`\SProp` is like :math:`\Prop` but the propositions in
:math:`\SProp` are known to have irrelevant proofs (all proofs are
equal). Objects of type :math:`\SProp` are called
:gdef:`strict propositions <strict proposition>`.
See :ref:`sprop` for information about using
:math:`\SProp`, and :cite:`Gilbert:POPL2019` for meta theoretical
considerations.

The sort :math:`\Set` intends to be the type of small sets. This includes data
types such as booleans and naturals, but also products, subsets, and
function types over these data types.
We denote specifications (program types) by :n:`@specif`.
This constitutes a semantic subclass of the syntactic class :n:`@term`.

:math:`\SProp`, :math:`\Prop` and :math:`\Set` themselves can be manipulated as ordinary terms.
Consequently they also have a type. Because assuming simply that :math:`\Set`
has type :math:`\Set` leads to an inconsistent theory :cite:`Coq86`, the language of
|Cic| has infinitely many sorts. There are, in addition to the base sorts,
a hierarchy of universes :math:`\Type(i)` for any integer :math:`i ≥ 1`.

Like :math:`\Set`, all of the sorts :math:`\Type(i)` contain small sets such as
booleans, natural numbers, as well as products, subsets and function
types over small sets. But, unlike :math:`\Set`, they also contain large sets,
namely the sorts :math:`\Set` and :math:`\Type(j)` for :math:`j<i`, and all products, subsets
and function types over these sorts.

Formally, we call :math:`\Sort` the set of sorts which is defined by:

.. math::

   \Sort \equiv \{\SProp,\Prop,\Set,\Type(i)\;|\; i~∈ ℕ\}

Their properties, such as :math:`\Prop:\Type(1)`, :math:`\Set:\Type(1)`, and
:math:`\Type(i):\Type(i+1)`, are described in :ref:`subtyping-rules`.

**Algebraic universes** In practice, the Type hierarchy is
implemented using algebraic universes,
which appear in the syntax :n:`Type@{@universe}`.
An :gdef:`algebraic universe` :math:`u` is either a variable,
a successor of an algebraic universe (an expression :math:`u+1`),
an upper bound of algebraic universes (an expression :math:`\max(u_1 ,...,u_n )`),
or the base universe :math:`\Set`.

A graph of constraints between the universe variables is maintained
globally. To ensure the existence of a mapping of the universes to the
positive integers, the graph of constraints must remain acyclic.
Typing expressions that violate the acyclicity of the graph of
constraints results in a :exn:`Universe inconsistency` error.

The user does not have to mention explicitly the universe :math:`u` when
referring to the universe `Type@{u}`. One only writes `Type`. The system
itself generates for each instance of `Type` a new variable for the
universe and checks that the constraints between these indexes can be
solved. From the user point of view we consequently have :math:`\Type:\Type`. We
shall make precise in the typing rules the constraints between the
indices.

The syntax :n:`Type@{@qualid | @universe}` is used with
:ref:`polymorphicuniverses` when quantifying over all sorts including
:math:`\Prop` and :math:`\SProp`.

.. seealso:: :ref:`printing-universes`, :ref:`explicit-universes`.
