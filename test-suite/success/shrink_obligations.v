Require Program.

Obligation Tactic := idtac.

Set Shrink Obligations.

Program Definition foo (m : nat) (p := S m) (n : nat) (q := S n) : unit :=
let bar : {r | n < r} := _ in
let qux : {r | p < r} := _ in
let quz : m = n -> True := _ in
tt.
Next Obligation.
intros m p n q.
exists (S n); constructor.
Qed.
Next Obligation.
intros m p n q.
exists (S (S m)); constructor.
Qed.
Next Obligation.
intros m p n q ? ? H.
destruct H.
constructor.
Qed.

Check (foo_obligation_1 : forall n, {r | n < r}).
Check (foo_obligation_2 : forall m, {r | (S m) < r}).
Check (foo_obligation_3 : forall m n, m = n -> True).
