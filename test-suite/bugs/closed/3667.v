
Set Primitive Projections.
Axiom ap10 : forall {A B} {f g:A->B} (h:f=g) x, f x = g x.
Axiom IsHSet : Type -> Type.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d) }.
Set Implicit Arguments.
Record NaturalTransformation C D (F G : Functor C D) :=
  { components_of :> forall c, morphism D (F c) (G c);
    commutes : forall s d (m : morphism C s d), components_of s = components_of s }.
Definition set_cat : PreCategory.
  exact ((@Build_PreCategory hSet
                             (fun x y => x -> y))).
Defined.
Goal forall (A : PreCategory) (F : Functor A set_cat)
            (a : A) (x : F a) (nt :NaturalTransformation F F), x = x.
  intros. 
  pose (fun c d m => ap10 (commutes nt c d m)).


