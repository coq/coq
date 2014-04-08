(* Checking that the type inference algoithme does not commit to an
   equality over sorts when only a subtyping constraint is around *)

Parameter A : Set.
Parameter B : A -> Set.
Parameter F : Set -> Prop. 
Check (F (forall x, B x)).

