Set Typeclasses Strict Resolution.
Class Contr (A : Type) := { center : A }.
Definition foo {A} `{Contr A} : A.
Proof.
  apply center.
  Undo.
  (* Ensure the constraints are solved indepentently, otherwise a frozen ?A 
  makes a search for Contr ?A fail when finishing to apply (fun x => x) *)
  apply (fun x => x), center. 

(* Toplevel input, characters 7-17:
Error:
Unable to satisfy the following constraints:
In environment:
A : Type
H : Contr A

?A : "Type"
?Contr : "Contr ?X8"

 *)