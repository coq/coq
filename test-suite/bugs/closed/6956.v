(** Used to trigger an anomaly with VM compilation *)

Set Universe Polymorphism.

Inductive t A : nat -> Type :=
| nil : t A 0
| cons : forall (h : A) (n : nat), t A n -> t A (S n).

Definition case0 {A} (P : t A 0 -> Type) (H : P (nil A)) v : P v :=
match v with
| nil _ => H
| _ => fun devil => False_ind (@IDProp) devil
end.
