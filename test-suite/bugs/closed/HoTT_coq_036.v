Unset Strict Universe Declaration.
Module Version1.
  Set Implicit Arguments.
  Set Universe Polymorphism.
  Generalizable All Variables.

  Record SpecializedCategory (obj : Type) :=
    {
      Object :> _ := obj
    }.

  Record > Category :=
    {
      CObject : Type;
      UnderlyingCategory :> @SpecializedCategory CObject
    }.

  Record SpecializedFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :=
    {
      ObjectOf :> objC -> objD
    }.

  Definition Functor (C D : Category) := SpecializedFunctor C D.

  Parameter TerminalCategory : SpecializedCategory unit.

  Definition focus A (_ : A) := True.

  Definition CommaCategory_Object (A : Category) (S : Functor TerminalCategory A) : Type.
    assert (Hf : focus ((S tt) = (S tt))) by constructor.
    let C1 := constr:(CObject) in
    let C2 := constr:(fun C => @Object (CObject C) C) in
    unify C1 C2; idtac C1 C2. Show Universes.
    progress change @CObject with (fun C => @Object (CObject C) C) in *. 
    simpl in *.
    match type of Hf with
      | focus ?V => exact V
    end.
  Defined.

  Definition Build_SliceCategory (A : Category) (F : Functor TerminalCategory A) := @Build_SpecializedCategory (CommaCategory_Object F).
  Parameter SetCat : @SpecializedCategory Set.

  Set Printing Universes.
  Check (fun (A : Category) (F : Functor TerminalCategory A) => @Build_SpecializedCategory (CommaCategory_Object F)) SetCat.
  (* (fun (A : Category (* Top.68 *))
   (F : Functor (* Set Top.68 *) TerminalCategory A) =>
 {|  |}) SetCat (* Top.68 *)
     : forall
         F : Functor (* Set Top.68 *) TerminalCategory SetCat (* Top.68 *),
       let Object := CommaCategory_Object (* Top.68 Top.69 Top.68 *) F in
       SpecializedCategory (* Top.69 *)
         (CommaCategory_Object (* Top.68 Top.69 Top.68 *) F) *)
  Check @Build_SliceCategory SetCat. (* Toplevel input, characters 0-34:
Error: Universe inconsistency (cannot enforce Top.51 <= Set because Set
< Top.51). *)
End Version1.

Module Version2.
  Set Implicit Arguments.
  Set Universe Polymorphism.

  Record SpecializedCategory (obj : Type) :=
    {
      Object : _ := obj
    }.

  Record > Category :=
    {
      CObject : Type;
      UnderlyingCategory :> @SpecializedCategory CObject
    }.

  Parameter TerminalCategory : SpecializedCategory unit.

  Definition focus A (_ : A) := True.
  Parameter ObjectOf' : forall (objC : Type) (C : SpecializedCategory objC)
                               (objD : Type) (D : SpecializedCategory objD), Prop.
  Definition CommaCategory_Object (A : Category) : Type.
    assert (Hf : focus (@ObjectOf' _ (@Build_Category unit TerminalCategory) _ A)) by constructor.
    progress change CObject with (fun C => @Object (CObject C) C) in *;
      simpl in *.
    match type of Hf with
      | focus ?V => exact V
    end.
  Defined.

  Definition Build_SliceCategory := @CommaCategory_Object.
  Parameter SetCat : @SpecializedCategory Set.

  Set Printing Universes.
  Check @Build_SliceCategory SetCat.
End Version2.

Module OtherBug.
  Set Implicit Arguments.
  Set Universe Polymorphism.

  Record SpecializedCategory (obj : Type) :=
    {
      Object : _ := obj
    }.

  Record > Category :=
    {
      CObject : Type;
      UnderlyingCategory :> @SpecializedCategory CObject
    }.

  Parameter TerminalCategory : SpecializedCategory unit.

  Definition focus A (_ : A) := True.

  Parameter ObjectOf' : forall (objC : Type) (C : SpecializedCategory objC)
                               (objD : Type) (D : SpecializedCategory objD), Prop.
  Definition CommaCategory_Object (A : Category@{i}) : Type.
    assert (Hf : focus (@ObjectOf' _ (@Build_Category unit TerminalCategory) _ A)) by constructor.
    progress change CObject with (fun C => @Object (CObject C) C) in *;
      simpl in *.
    match type of Hf with
      | focus ?V => exact V
    end.
  Defined.

  Parameter SetCat : @SpecializedCategory Set.

  Set Printing Universes.
  Definition Build_SliceCategory := @CommaCategory_Object.
  Check @CommaCategory_Object SetCat.
  (* CommaCategory_Object (* Top.43 Top.44 Top.43 *) SetCat (* Top.43 *)
     : Type (* Top.44 *) *)
  Check @Build_SliceCategory SetCat.
  (* Toplevel input, characters 0-34:
Error: Universe inconsistency (cannot enforce Top.36 <= Set because Set
< Top.36). *)
End OtherBug.
