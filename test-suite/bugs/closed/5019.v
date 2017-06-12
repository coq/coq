Require Import Coq.ZArith.ZArith.
Goal forall (T0 : Z -> Type) (k : nat) d (P : T0 (Z.of_nat (S k)) -> Prop), P d.
  clear; intros.
  Timeout 1 zify. (* used to loop forever; should take < 0.01 s *)
Admitted.
