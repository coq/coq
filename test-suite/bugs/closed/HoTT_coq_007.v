Unset Strict Universe Declaration.
Require Import TestSuite.admit.
Module Comment1.
  Set Implicit Arguments.

  Polymorphic Record Category (obj : Type) :=
    {
      Morphism : obj -> obj -> Type;
      Identity : forall o, Morphism o o
    }.

  Polymorphic Record Functor objC (C :Category objC) objD (D : Category objD) :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FIdentityOf : forall o, MorphismOf _ _ (C.(Identity) o) = D.(Identity) (ObjectOf o)
    }.

  Create HintDb functor discriminated.

  Hint Rewrite @FIdentityOf : functor.

  Polymorphic Definition ComposeFunctors objC C objD D objE E (G : @Functor objD D objE E) (F : @Functor objC C objD D) : Functor C E.
  refine {| ObjectOf := (fun c => G (F c));
            MorphismOf := (fun _ _ m => G.(MorphismOf) _ _ (F.(MorphismOf) _ _ m))
         |};
    intros; autorewrite with functor; reflexivity.
  Defined.

  Definition Cat0 : Category@{i j} Empty_set.
    refine {|
        Morphism := fun s d : Empty_set => s = d;
        Identity := fun o : Empty_set => eq_refl
      |};
    admit.
  Defined.

  Set Printing All.
  Set Printing Universes.

  Lemma foo objC (C : @Category objC) (C0 : Category (Functor Cat0 C)) (x : Functor Cat0 Cat0) 
  : forall (y : Functor C0 Cat0) z, (ComposeFunctors y z = x). 
    intro. intro.
    unfold ComposeFunctors.     
  Abort.
End Comment1.

Module Comment2.
  Set Implicit Arguments.

  Polymorphic Record Category (obj : Type) :=
    {
      Morphism : obj -> obj -> Type;

      Identity : forall o, Morphism o o;
      Compose : forall s d d2, Morphism d d2 -> Morphism s d -> Morphism s d2;

      LeftIdentity : forall a b (f : Morphism a b), Compose (Identity b) f = f
    }.

  Polymorphic Record Functor objC (C : Category objC) objD (D : Category objD) :=
    {
      ObjectOf : objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
    }.

  Create HintDb morphism discriminated.

  Polymorphic Hint Resolve @LeftIdentity : morphism.

  Polymorphic Definition ProductCategory objC (C : Category objC) objD (D : Category objD) : @Category (objC * objD)%type.
  refine {|
      Morphism := (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type);
      Identity := (fun o => (Identity _ (fst o), Identity _ (snd o)));
      Compose := (fun (s d d2 : (objC * objD)%type) m2 m1 => (C.(Compose) _ _ _ (fst m2) (fst m1), D.(Compose) _ _ _ (snd m2) (snd m1)))
    |};
    intros; apply injective_projections; simpl; auto with morphism. (* Replacing [auto with morphism] with [apply @LeftIdentity] removes the error *)
  Defined.

  Polymorphic Definition Cat0 : Category Empty_set.
  refine {|
      Morphism := fun s d : Empty_set => s = d;
      Identity := fun o : Empty_set => eq_refl;
      Compose := fun s d d2 m0 m1 => eq_trans m1 m0
    |};
    admit.
  Defined.

  Set Printing All.
  Set Printing Universes.
  Polymorphic Definition ProductLaw0Functor (objC : Type) (C : Category objC) : Functor (ProductCategory C Cat0) Cat0.
  refine (Build_Functor (ProductCategory C Cat0) Cat0 _ _). (* Toplevel input, characters 15-71:
Error: Refiner was given an argument
 "prod (* Top.2289 Top.2289 *) objC Empty_set" of type
"Type (* Top.2289 *)" instead of "Set". *)
  Abort.
  Polymorphic Definition ProductLaw0Functor (objC : Type) (C : Category objC) : Functor (ProductCategory C Cat0) Cat0.
  econstructor. (* Toplevel input, characters 0-12:
Error: No applicable tactic.
                 *)
  Abort.
End Comment2.


Module Comment3.
  Polymorphic Lemma foo {obj : Type} : 1 = 1.
  trivial.
  Qed.

  Polymorphic Hint Resolve foo. (* success *)
  Polymorphic Hint Rewrite @foo. (* Success *)
  Polymorphic Hint Resolve @foo. (* Error: @foo is a term and cannot be made a polymorphic hint, only global references can be polymorphic hints. *)
  Fail Polymorphic Hint Rewrite foo. (* Error: Cannot infer the implicit parameter obj of foo. *)
End Comment3.
