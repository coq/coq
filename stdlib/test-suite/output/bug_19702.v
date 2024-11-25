From Stdlib Require Import Utf8.

Axiom T : nat -> Type.
Axiom default : forall n, T n.

Definition f1 {n1} n2 (w : T n2) := default n1.
About f1.
(*
f1 : ∀ n1 n2 : nat, T n2 → T n1 // wrong

f1 is not universe polymorphic
Arguments f1 {n1}%nat_scope n2%nat_scope w // correct
f1 is transparent
Expands to: Constant Top.f1
*)


Arguments f1 {_} [_].
About f1.
(*
f1 : ∀ [n1 n2 : nat], T n2 → T n1 // wrong

f1 is not universe polymorphic
Arguments f1 {n1}%nat_scope [n2]%nat_scope w // correct
f1 is transparent
Expands to: Constant Top.f1
*)

Arguments f1 {_ _}.
About f1.
