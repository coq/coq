Module FirstIssue.
  Set Implicit Arguments.

  Record Cat (obj : Type) := {}.

  Record Functor objC (C : Cat objC) objD (D : Cat objD) :=
    {
      ObjectOf' : objC -> objD
    }.

  Definition TypeCat : Cat Type. constructor. Defined.
  Definition PropCat : Cat Prop. constructor. Defined.

  Definition FunctorFrom_Type2Prop objC (C : Cat objC) (F : Functor TypeCat C) : Functor PropCat C.
    Set Printing All.
    Set Printing Universes.
    Check F. (* F : @Functor Type (* Top.1201 *) TypeCat objC C *)
    exact (Build_Functor PropCat C (ObjectOf' F)).
    Show Proof. (* (fun (objC : Type (* Top.1194 *)) (C : Cat objC)
   (F : @Functor Prop TypeCat objC C) =>
 @Build_Functor Prop PropCat objC C
   (@ObjectOf' Prop TypeCat objC C F)) *)
  Defined.
  (* Error: Illegal application (Type Error):
The term "Functor" of type
 "forall (objC : Type (* Top.1194 *)) (_ : Cat objC)
    (objD : Type (* Top.1194 *)) (_ : Cat objD),
  Type (* Top.1194 *)"
cannot be applied to the terms
 "Prop" : "Type (* (Set)+1 *)"
 "TypeCat" : "Cat Type (* Top.1201 *)"
 "objC" : "Type (* Top.1194 *)"
 "C" : "Cat objC"
The 2nd term has type "Cat Type (* Top.1201 *)"
which should be coercible to "Cat Prop". *)
End FirstIssue.

Module SecondIssue.
  Set Implicit Arguments.

  Set Printing Universes.

  Polymorphic Record Cat (obj : Type) :=
    {
      Object :> _ := obj;
      Morphism' : obj -> obj -> Type
    }.

  Polymorphic Record Functor objC (C : Cat objC) objD (D : Cat objD) :=
    {
      ObjectOf' : objC -> objD;
      MorphismOf' : forall s d, C.(Morphism') s d -> D.(Morphism') (ObjectOf' s) (ObjectOf' d)
    }.

  Definition SetCat : Cat Set := @Build_Cat Set (fun x y => x -> y).
  Definition PropCat : Cat Prop := @Build_Cat Prop (fun x y => x -> y).

  Set Printing All.

  Definition FunctorFrom_Set2Prop objC (C : Cat objC) (F : Functor SetCat C) : Functor PropCat C.
    exact (Build_Functor PropCat C
                         (ObjectOf' F)
                         (MorphismOf' F)
          ).
  Defined. (* Error: Illegal application (Type Error):
The term "Build_Functor (* Top.748 Prop Top.808 Top.809 *)" of type
 "forall (objC : Type (* Top.748 *)) (C : Cat (* Top.748 Prop *) objC)
    (objD : Type (* Top.808 *)) (D : Cat (* Top.808 Top.809 *) objD)
    (ObjectOf' : forall _ : objC, objD)
    (_ : forall (s d : objC) (_ : @Morphism' (* Top.748 Prop *) objC C s d),
         @Morphism' (* Top.808 Top.809 *) objD D (ObjectOf' s) (ObjectOf' d)),
  @Functor (* Top.748 Prop Top.808 Top.809 *) objC C objD D"
cannot be applied to the terms
 "Prop" : "Type (* (Set)+1 *)"
 "PropCat" : "Cat (* Top.748 Prop *) Prop"
 "objC" : "Type (* Top.808 *)"
 "C" : "Cat (* Top.808 Top.809 *) objC"
 "fun x : Prop =>
  @ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F x"
   : "forall _ : Prop, objC"
 "@MorphismOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F"
   : "forall (s d : Set) (_ : @Morphism' (* Top.744 Prop *) Set SetCat s d),
      @Morphism' (* Top.808 Top.809 *) objC C
        (@ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F s)
        (@ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F d)"
The 6th term has type
 "forall (s d : Set) (_ : @Morphism' (* Top.744 Prop *) Set SetCat s d),
  @Morphism' (* Top.808 Top.809 *) objC C
    (@ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F s)
    (@ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F d)"
which should be coercible to
 "forall (s d : Prop) (_ : @Morphism' (* Top.748 Prop *) Prop PropCat s d),
  @Morphism' (* Top.808 Top.809 *) objC C
    ((fun x : Prop =>
      @ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F x) s)
    ((fun x : Prop =>
      @ObjectOf' (* Top.744 Prop Top.808 Top.809 *) Set SetCat objC C F x) d)".
            *)
End SecondIssue.
