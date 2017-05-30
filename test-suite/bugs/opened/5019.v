Require Import Coq.ZArith.ZArith.
Goal forall (T0 : Z -> Type) (k : nat) d (P : T0 (Z.of_nat (S k)) -> Prop), P d.
  clear; intros.
  Fail Timeout 1 zify.
