Require Import Arith List.
Import Orders.

Module Adr.
 Include NatOrderedType.Nat_as_OT.
 Definition nat2t (i: nat) : t := i.
End Adr.

Inductive expr :=  Const: Adr.t -> expr.

Inductive control := Go: expr ->  control.

Definition program :=  (Adr.t * (control))%type.

Fail Definition myprog : program := (Adr.nat2t 0,   Go (Adr.nat2t 0) ).