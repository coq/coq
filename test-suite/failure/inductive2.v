(* A check that sort-polymorphic product is not set too low *)

Inductive prod (A B:Type) : Type := pair : A -> B -> prod A B.
Check (fun (A:Prop) (B:Type) => (prod A B : Prop)).
