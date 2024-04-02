

Module Export Datatypes.

Set Implicit Arguments.
Local Set Primitive Projections.

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

End Datatypes.


Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Record PreCategory :=
  Build_PreCategory {
      object :> Type;
      morphism : object -> object -> Type;
      identity : forall x, morphism x x;
    }.

Bind Scope category_scope with PreCategory.
Arguments identity {!C%_category} / x%_object : rename.

Local Open Scope morphism_scope.

Section prod.
  Variables C D : PreCategory.

  Definition prod : PreCategory := (@Build_PreCategory
              (C * D)%type
              (fun s d => (morphism C (fst s) (fst d)
                           * morphism D (snd s) (snd d))%type)
              (fun x => (identity (fst x), identity (snd x)))).

End prod.

Local Infix "*" := prod : category_scope.
Delimit Scope functor_scope with functor.

Section Functor.
  Variables C D : PreCategory.

  Record Functor :=
    {
      object_of :> C -> D;
      morphism_of : forall s d, morphism C s d
                                -> morphism D (object_of s) (object_of d);
      identity_of : forall x, morphism_of _ _ (identity x)
                              = identity (object_of x)
    }.
End Functor.
Arguments morphism_of [C%_category] [D%_category] F%_functor [s%_object d%_object] m%_morphism : rename, simpl nomatch.

Parameter C1 C2 D : PreCategory.

Parameter F : Functor (C1 * C2) D.

Lemma foo (c1:C1) (x : object C2)
  : @morphism_of _ _ F
      (@pair (object C1) (object C2) c1 x)
      (@pair (object C1) (object C2) c1 x)
      (identity c1, identity x)
    = identity (F (c1, x)).
Proof.
  rewrite identity_of.
  reflexivity.
Qed.
