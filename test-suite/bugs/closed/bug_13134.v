Set Implicit Arguments.
Set Primitive Projections.
Record prod (A B:Type) : Type := pair { fst : A ; snd : B }.
Infix "*" := prod : type_scope.
Add Printing Let prod.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.
Record Category := { object :> Type; morphism : object -> object -> Type }.
Record Functor (C D : Category) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d) }.
Arguments morphism_of {_ _} _ {_ _}.

Axiom functor_eq
  : forall {C D} (F G : Functor C D),
    (forall s d (m : morphism C s d),
        existT _ (_, _) (morphism_of F m) = existT _ (_, _) (morphism_of G m) :> { sd & morphism D (fst sd) (snd sd) })
    -> F = G.
