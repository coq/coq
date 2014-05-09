Set Universe Polymorphism.
Section foo.
  Let U := Type.
  Let U' : Type.
  Proof.
    let U' := constr:(Type) in
    let U_le_U' := constr:(fun x : U => (x : U')) in
    exact U'.
  Defined.
  Inductive t : U' := .
End foo.
(* Toplevel input, characters 15-23:
Error: No such section variable or assumption: U'. *)
