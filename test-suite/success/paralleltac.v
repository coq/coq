Lemma test_nofail_like_all1 :
  True /\ False.
Proof.
split.
all: trivial.
Admitted.

Lemma test_nofail_like_all2 :
  True /\ False.
Proof.
split.
par: trivial.
Admitted.

Fixpoint fib n := match n with
  | O => 1
  | S m => match m with
    | O => 1
    | S o => fib o + fib m end end.
Ltac sleep n :=
  try (assert (fib n = S (fib n)) by reflexivity).
(* Tune that depending on your PC *)
Let time := 18.

Axiom P : nat -> Prop.
Axiom P_triv : Type -> forall x, P x.
Ltac solve_P :=
  match goal with |- P (S ?X) =>
    sleep time; exact (P_triv Type _)
  end.

Lemma test_old x : P (S x) /\ P (S x) /\ P (S x) /\ P (S x).
Proof.
repeat split.
idtac "T1: linear".
Time all: solve [solve_P].
Qed.

Lemma test_ok x : P (S x) /\ P (S x) /\ P (S x) /\ P (S x).
Proof.
repeat split.
idtac "T2: parallel".
Time par: solve [solve_P].
Qed.

Lemma test_fail x : P (S x) /\ P x /\ P (S x) /\ P (S x).
Proof.
repeat split.
idtac "T3: linear failure".
Fail Time all: solve solve_P.
all: solve [apply (P_triv Type)].
Qed.

Lemma test_fail2 x : P (S x) /\ P x /\ P (S x) /\ P (S x).
Proof.
repeat split.
idtac "T4: parallel failure".
Fail Time par: solve [solve_P].
all: solve [apply (P_triv Type)].
Qed.
