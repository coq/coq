(* Used in Import.v to test the locality flag *)

Definition f (A:Type) (a:A) := a.

Local Arguments f [A]%_type_scope _%_type_scope.

(* Used in ImportedCoercion.v to test the locality flag *)

Local Coercion g (b:bool) := if b then 0 else 1.
