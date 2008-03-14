Require Import BinPos.

Definition P := (fun x : positive => x = xH).

Goal forall (p q : positive), P q -> q = p -> P p.
intros; congruence.
Qed.



