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
  unify C1 C2.
  progress change CObject with (fun C => @Object (CObject C) C) in *.
  simpl in *.
  let V := match type of Hf with
             | focus ?V => constr:(V)
           end
  in exact V.
(* Toplevel input, characters 89-96:
Error: Illegal application:
The term "ObjectOf" of type
 "forall (objC : Set) (C : SpecializedCategory objC)
    (objD : Type) (D : SpecializedCategory objD),
  SpecializedFunctor C D -> objC -> objD"
cannot be applied to the terms
 "Object TerminalCategory" : "Type"
 "TerminalCategory" : "SpecializedCategory unit"
 "Object A" : "Type"
 "UnderlyingCategory A" : "SpecializedCategory (CObject A)"
 "S" : "Functor TerminalCategory A"
 "tt" : "unit"
The 1st term has type "Type" which should be coercible to
"Set". *)
Defined.
