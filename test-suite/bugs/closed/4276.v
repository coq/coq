Set Primitive Projections.

Record box (T U : Type) (x := T) := wrap { unwrap : T }.
Definition mybox : box True False := wrap _ _ I.
Definition unwrap' := @unwrap.

Definition bad' : True := mybox.(unwrap _ _). 

Fail Definition bad : False := unwrap _ _ mybox.

(* Closed under the global context *)
