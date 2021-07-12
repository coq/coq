(* no falsity elimination *)
Goal False -> (True = False).
Proof. Fail congruence. Admitted.

(* unfold not; assumption *)
Goal False -> not True.
Proof. congruence. Qed.

(* unfold not; discriminate *)
Goal not (true = false).
Proof. congruence. Qed.

(* bug #3549 *)
Definition mytrue := true.
Goal ~ (mytrue = false).
Proof. Fail congruence. Admitted.

Goal mytrue = true.
Proof. Fail congruence. Admitted.

Fixpoint stupid (n : nat) : unit :=
match n with
| 0 => tt
| S n =>
  let () := stupid n in
  let () := stupid n in
  tt
end.

(* do not try to unify 23 with stupid 23 *)
Goal 23 = 23 -> stupid 23 = stupid 23.
Proof. Timeout 5 Time congruence. Qed.

Inductive Fin : nat -> Set :=
| F1 : forall n : nat, Fin (S n)
| FS : forall n : nat, Fin n -> Fin (S n).

Goal forall n (f : Fin n), FS n f = F1 n -> False.
Proof. intros n f H. congruence. Qed.

Axiom P : Prop.
Axiom R : Prop.
Axiom R' : Prop.

Goal (not P) -> not P.
Proof. congruence. Qed.

Goal (P -> False) -> P -> False.
Proof. congruence. Qed.

(* generalization of the above two goals *)
Goal (P -> R) -> P -> R.
Proof. Fail congruence. Admitted.

Goal (not (true = true)) -> False.
Proof. congruence. Qed.

Goal (not (true = true)) -> P.
Proof. congruence. Qed.

Definition Q := True -> P.

(* bug #5394 *)
Goal Q -> Q.
Proof. congruence. Qed.

Goal Q -> (Q = R) -> R.
Proof. congruence. Qed.

(* unfortunately, common usecase *)
Goal P -> Q.
Proof. congruence. Qed.

Goal (P = R' -> R = R') -> (P = R') -> R = R'.
Proof. Fail congruence. Admitted.

(* bug *)
Goal R -> (R = not P) -> not P.
Proof. congruence. Qed.

Definition per_unit := forall u, match u with tt => True end.

(* bug #5394 *)
Goal per_unit -> per_unit.
Proof. congruence. Qed.
