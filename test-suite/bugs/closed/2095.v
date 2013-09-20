(* Classes and sections *)

Section OPT.
  Variable A: Type.

  Inductive MyOption: Type :=
  | MyNone: MyOption
  | MySome: A -> MyOption.

  Class Opt: Type := {
    f_opt: A -> MyOption
  }.
End OPT.

Definition f_nat (n: nat):  MyOption nat := MySome _ n.

Instance Nat_Opt: Opt nat := {
  f_opt := f_nat
}.
