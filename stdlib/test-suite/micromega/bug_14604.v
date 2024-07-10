From Stdlib Require Import ZArith Lia.

(* mul z n = Z.of_nat n * z *)
Fixpoint mul (x:Z) (n : nat) : Z :=
match n with
| O => 0%Z
| S n => mul x n + 1 * x%Z
end.

Lemma test: forall z : Z, (0 <= z)%Z -> (0 <= mul z 100)%Z.
Proof.
cbn -[Z.mul Z.add].
intros.
Timeout 2 lia.
Qed.
