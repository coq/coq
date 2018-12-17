Register unit as core.IDProp.type.
Register tt as core.IDProp.idProp.


Inductive vec (A : Type) : nat -> Type :=
| nil : vec A 0
| cons : forall n : nat, A -> vec A n -> vec A (S n).

Definition hd (A : Type) (n : nat) (v : vec A (S n)) : A :=
match v in (vec _ (S n)) return A with
| cons _ _ h _ => h
end. (* assertion failure in evarconv *)
