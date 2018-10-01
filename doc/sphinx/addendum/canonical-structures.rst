.. _canonicalstructures:

Canonical Structures
======================

:Authors: Assia Mahboubi and Enrico Tassi

This chapter explains the basics of canonical structures and how they can be used
to overload notations and build a hierarchy of algebraic structures. The
examples are taken from :cite:`CSwcu`. We invite the interested reader to refer
to this paper for all the details that are omitted here for brevity. The
interested reader shall also find in :cite:`CSlessadhoc` a detailed description
of another, complementary, use of canonical structures: advanced proof search.
This latter papers also presents many techniques one can employ to tune the
inference of canonical structures.


Notation overloading
-------------------------

We build an infix notation == for a comparison predicate. Such
notation will be overloaded, and its meaning will depend on the types
of the terms that are compared.

.. coqtop:: all
  
  Module EQ.
    Record class (T : Type) := Class { cmp : T -> T -> Prop }.
    Structure type := Pack { obj : Type; class_of : class obj }.
    Definition op (e : type) : obj e -> obj e -> Prop :=
      let 'Pack _ (Class _ the_cmp) := e in the_cmp.
    Check op.
    Arguments op {e} x y : simpl never.
    Arguments Class {T} cmp.
    Module theory.
      Notation "x == y" := (op x y) (at level 70).
    End theory.
  End EQ.

We use Coq modules as namespaces. This allows us to follow the same
pattern and naming convention for the rest of the chapter. The base
namespace contains the definitions of the algebraic structure. To
keep the example small, the algebraic structure ``EQ.type`` we are
defining is very simplistic, and characterizes terms on which a binary
relation is defined, without requiring such relation to validate any
property. The inner theory module contains the overloaded notation ``==``
and will eventually contain lemmas holding all the instances of the
algebraic structure (in this case there are no lemmas).

Note that in practice the user may want to declare ``EQ.obj`` as a
coercion, but we will not do that here.

The following line tests that, when we assume a type ``e`` that is in
theEQ class, we can relate two of its objects with ``==``.

.. coqtop:: all
  
  Import EQ.theory.
  Check forall (e : EQ.type) (a b : EQ.obj e), a == b.

Still, no concrete type is in the ``EQ`` class.

.. coqtop:: all

  Fail Check 3 == 3.

We amend that by equipping ``nat`` with a comparison relation.

.. coqtop:: all
  
   Definition nat_eq (x y : nat) := Nat.compare x y = Eq.
   Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.
   Canonical Structure nat_EQty : EQ.type := EQ.Pack nat nat_EQcl.
   Check 3 == 3.
   Eval compute in 3 == 4.

This last test shows that |Coq| is now not only able to type check ``3 == 3``,
but also that the infix relation was bound to the ``nat_eq`` relation.
This relation is selected whenever ``==`` is used on terms of type nat.
This can be read in the line declaring the canonical structure
``nat_EQty``, where the first argument to ``Pack`` is the key and its second
argument a group of canonical values associated to the key. In this
case we associate to nat only one canonical value (since its class,
``nat_EQcl`` has just one member). The use of the projection ``op`` requires
its argument to be in the class ``EQ``, and uses such a member (function)
to actually compare its arguments.

Similarly, we could equip any other type with a comparison relation,
and use the ``==`` notation on terms of this type.


Derived Canonical Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We know how to use ``== `` on base types, like ``nat``, ``bool``, ``Z``. Here we show
how to deal with type constructors, i.e. how to make the following
example work:


.. coqtop:: all

  Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

The error message is telling that |Coq| has no idea on how to compare
pairs of objects. The following construction is telling Coq exactly
how to do that.

.. coqtop:: all

  Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj e2) :=
    fst x == fst y /\ snd x == snd y.
  
  Definition pair_EQcl e1 e2 := EQ.Class (pair_eq e1 e2).

  Canonical Structure pair_EQty (e1 e2 : EQ.type) : EQ.type :=
      EQ.Pack (EQ.obj e1 * EQ.obj e2) (pair_EQcl e1 e2).

  Check forall (e : EQ.type) (a b : EQ.obj e), (a, b) == (a, b).

  Check forall n m : nat, (3, 4) == (n, m).

Thanks to the ``pair_EQty`` declaration, |Coq| is able to build a comparison
relation for pairs whenever it is able to build a comparison relation
for each component of the pair. The declaration associates to the key ``*``
(the type constructor of pairs) the canonical comparison
relation ``pair_eq`` whenever the type constructor ``*`` is applied to two
types being themselves in the ``EQ`` class.

Hierarchy of structures
----------------------------

To get to an interesting example we need another base class to be
available. We choose the class of types that are equipped with an
order relation, to which we associate the infix ``<=`` notation.

.. coqtop:: all

  Module LE.

    Record class T := Class { cmp : T -> T -> Prop }.

    Structure type := Pack { obj : Type; class_of : class obj }.

    Definition op (e : type) : obj e -> obj e -> Prop :=
      let 'Pack _ (Class _ f) := e in f.

    Arguments op {_} x y : simpl never.

    Arguments Class {T} cmp.
  
    Module theory.

      Notation "x <= y" := (op x y) (at level 70).

    End theory.

  End LE.

As before we register a canonical ``LE`` class for ``nat``.

.. coqtop:: all

  Import LE.theory.

  Definition nat_le x y := Nat.compare x y <> Gt.

  Definition nat_LEcl : LE.class nat := LE.Class nat_le.

  Canonical Structure nat_LEty : LE.type := LE.Pack nat nat_LEcl.

And we enable |Coq| to relate pair of terms with ``<=``.

.. coqtop:: all

  Definition pair_le e1 e2 (x y : LE.obj e1 * LE.obj e2) :=
     fst x <= fst y /\ snd x <= snd y.

  Definition pair_LEcl e1 e2 := LE.Class (pair_le e1 e2).

  Canonical Structure pair_LEty (e1 e2 : LE.type) : LE.type :=
     LE.Pack (LE.obj e1 * LE.obj e2) (pair_LEcl e1 e2).

  Check (3,4,5) <= (3,4,5).

At the current stage we can use ``==`` and ``<=`` on concrete types, like
tuples of natural numbers, but we can’t develop an algebraic theory
over the types that are equipped with both relations.

.. coqtop:: all

  Check 2 <= 3 /\ 2 == 2.

  Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <= x -> x == y.

  Fail Check forall (e : LE.type) (x y : LE.obj e), x <= y -> y <= x -> x == y.

We need to define a new class that inherits from both ``EQ`` and ``LE``.


.. coqtop:: all

  Module LEQ.

    Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop) :=
      Mixin { compat : forall x y : EQ.obj e, le x y /\ le y x <-> x == y }.
    
    Record class T := Class {
                        EQ_class : EQ.class T;
                        LE_class : LE.class T;
                        extra : mixin (EQ.Pack T EQ_class) (LE.cmp T LE_class) }.

    Structure type := _Pack { obj : Type; class_of : class obj }.

    Arguments Mixin {e le} _.

    Arguments Class {T} _ _ _.

The mixin component of the ``LEQ`` class contains all the extra content we
are adding to ``EQ`` and ``LE``. In particular it contains the requirement
that the two relations we are combining are compatible.

Unfortunately there is still an obstacle to developing the algebraic
theory of this new class.

.. coqtop:: all

    Module theory.

    Fail Check forall (le : type) (n m : obj le), n <= m -> n <= m -> n == m.


The problem is that the two classes ``LE`` and ``LEQ`` are not yet related by
a subclass relation. In other words |Coq| does not see that an object of
the ``LEQ`` class is also an object of the ``LE`` class.

The following two constructions tell |Coq| how to canonically build the
``LE.type`` and ``EQ.type`` structure given an ``LEQ.type`` structure on the same
type.

.. coqtop:: all

    Definition to_EQ (e : type) : EQ.type :=
       EQ.Pack (obj e) (EQ_class _ (class_of e)).

    Canonical Structure to_EQ.

    Definition to_LE (e : type) : LE.type :=
       LE.Pack (obj e) (LE_class _ (class_of e)).
 
    Canonical Structure to_LE.

We can now formulate out first theorem on the objects of the ``LEQ``
structure.

.. coqtop:: all

     Lemma lele_eq (e : type) (x y : obj e) : x <= y -> y <= x -> x == y.

     now intros; apply (compat _ _ (extra _ (class_of e)) x y); split. 

     Qed.

     Arguments lele_eq {e} x y _ _.

     End theory.

  End LEQ.

  Import LEQ.theory.

  Check lele_eq.

Of course one would like to apply results proved in the algebraic
setting to any concrete instate of the algebraic structure.

.. coqtop:: all

  Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.

  Fail apply (lele_eq n m). 

  Abort.

  Example test_algebraic2 (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
       n <= m -> m <= n -> n == m.

  Fail apply (lele_eq n m). 

  Abort.

Again one has to tell |Coq| that the type ``nat`` is in the ``LEQ`` class, and
how the type constructor ``*`` interacts with the ``LEQ`` class. In the
following proofs are omitted for brevity.

.. coqtop:: all

  Lemma nat_LEQ_compat (n m : nat) : n <= m /\ m <= n <-> n == m.

  Admitted.

  Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.

  Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
     n <= m /\ m <= n <-> n == m.

  Admitted.

  Definition pair_LEQmx l1 l2 := LEQ.Mixin (pair_LEQ_compat l1 l2).

The following script registers an ``LEQ`` class for ``nat`` and for the type
constructor ``*``. It also tests that they work as expected.

Unfortunately, these declarations are very verbose. In the following
subsection we show how to make them more compact.

.. coqtop:: all

  Module Add_instance_attempt.

    Canonical Structure nat_LEQty : LEQ.type :=
      LEQ._Pack nat (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).

    Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
      LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
        (LEQ.Class
           (EQ.class_of (pair_EQty (to_EQ l1) (to_EQ l2)))
           (LE.class_of (pair_LEty (to_LE l1) (to_LE l2)))
           (pair_LEQmx l1 l2)).

     Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.

     now apply (lele_eq n m). 

     Qed.

     Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n -> n == m.

     now apply (lele_eq n m). Qed.
  
  End Add_instance_attempt.

Note that no direct proof of ``n <= m -> m <= n -> n == m`` is provided by
the user for ``n`` and m of type ``nat * nat``. What the user provides is a
proof of this statement for ``n`` and ``m`` of type ``nat`` and a proof that the
pair constructor preserves this property. The combination of these two
facts is a simple form of proof search that |Coq| performs automatically
while inferring canonical structures.

Compact declaration of Canonical Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need some infrastructure for that.

.. coqtop:: all

  Require Import Strings.String.

  Module infrastructure.

    Inductive phantom {T : Type} (t : T) : Type := Phantom.

    Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) :=
      phantom t1 -> phantom t2.

    Definition id {T} {t : T} (x : phantom t) := x.

    Notation "[find v | t1 ~ t2 ] p" := (fun v (_ : unify t1 t2 None) => p)
      (at level 50, v ident, only parsing).

    Notation "[find v | t1 ~ t2 | s ] p" := (fun v (_ : unify t1 t2 (Some s)) => p)
      (at level 50, v ident, only parsing).

    Notation "'Error : t : s" := (unify _ t (Some s))
      (at level 50, format "''Error' : t : s").

    Open Scope string_scope.

  End infrastructure.

To explain the notation ``[find v | t1 ~ t2]`` let us pick one of its
instances: ``[find e | EQ.obj e ~ T | "is not an EQ.type" ]``. It should be
read as: “find a class e such that its objects have type T or fail
with message "T is not an EQ.type"”.

The other utilities are used to ask |Coq| to solve a specific unification
problem, that will in turn require the inference of some canonical structures.
They are explained in more details in :cite:`CSwcu`.

We now have all we need to create a compact “packager” to declare
instances of the ``LEQ`` class.

.. coqtop:: all

  Import infrastructure.

  Definition packager T e0 le0 (m0 : LEQ.mixin e0 le0) :=
    [find e | EQ.obj e ~ T | "is not an EQ.type" ]
    [find o | LE.obj o ~ T | "is not an LE.type" ]
    [find ce | EQ.class_of e ~ ce ]
    [find co | LE.class_of o ~ co ]
    [find m | m ~ m0 | "is not the right mixin" ]
    LEQ._Pack T (LEQ.Class ce co m).

   Notation Pack T m := (packager T _ _ m _ id _ id _ id _ id _ id).

The object ``Pack`` takes a type ``T`` (the key) and a mixin ``m``. It infers all
the other pieces of the class ``LEQ`` and declares them as canonical
values associated to the ``T`` key. All in all, the only new piece of
information we add in the ``LEQ`` class is the mixin, all the rest is
already canonical for ``T`` and hence can be inferred by |Coq|.

``Pack`` is a notation, hence it is not type checked at the time of its
declaration. It will be type checked when it is used, an in that case ``T`` is
going to be a concrete type. The odd arguments ``_`` and ``id`` we pass to the
packager represent respectively the classes to be inferred (like ``e``, ``o``,
etc) and a token (``id``) to force their inference. Again, for all the details
the reader can refer to :cite:`CSwcu`.

The declaration of canonical instances can now be way more compact:

.. coqtop:: all

  Canonical Structure nat_LEQty := Eval hnf in Pack nat nat_LEQmx.
  
  Canonical Structure pair_LEQty (l1 l2 : LEQ.type) :=
     Eval hnf in Pack (LEQ.obj l1 * LEQ.obj l2) (pair_LEQmx l1 l2).

Error messages are also quite intelligible (if one skips to the end of
the message).

.. coqtop:: all

  Fail Canonical Structure err := Eval hnf in Pack bool nat_LEQmx.

