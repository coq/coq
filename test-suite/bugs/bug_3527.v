Set Implicit Arguments.
Record Category := { obj :> Type ; hom :> obj -> obj -> Type }.
Record > PackagedHom (C : Category) := { x : C ; y : C ; unpackage :> C x y }.
Module Export FMap.
  Record Functor (C D : Category) := { fobj : C -> D ; map : forall x y, C x y -> D (fobj x) (fobj y) }.
End FMap.
Definition mapT1 {C D} (F : Functor C D) := forall x y, C x y -> D (fobj F x) (fobj F y).
Definition mapT2 {C D} (F : Functor C D) := forall m : PackagedHom C, D (fobj F m.(x)) (fobj F m.(y)).
Definition annoying_helper {C D F} (map : @ mapT1 C D F) : @ mapT2 C D F := fun m => map _ _ m.
Coercion annoying_helper : mapT1 >-> mapT2.
Identity Coercion unfold_mapT2 : mapT2 >-> Funclass.
Module Type mapT.
  Definition map {C D} (F : Functor C D) : mapT1 F := map F.
End mapT.
Module MapCoercion (T : mapT).
  Coercion T.map : Functor >-> mapT1.
End MapCoercion.
Module Export FunctorMapCoercion := MapCoercion FMap.
Section foo.
  Context C D (F : Functor C D) x y (m : C x y).
  Set Printing All.
  Check F _. (* @ annoying_helper (@ map C D F) ?48
     : forall F0 : Functor (@ map C D F) ?48,
       @ mapT1 (@ map C D F) ?48 F0 -> @ mapT2 (@ map C D F) ?48 F0 *)
  Definition foo k := F k.
End foo.
