(* Used in Import.v to test the locality flag *)

Definition f (A:Type) (a:A) := a.

Local Arguments Scope f [type_scope type_scope].
Local Implicit Arguments f [A].

(* Used in ImportedCoercion.v to test the locality flag *)

Local Coercion g (b:bool) := if b then 0 else 1.
