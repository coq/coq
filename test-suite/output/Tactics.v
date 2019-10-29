(* Test printing of Tactic Notation *)

Tactic Notation "a" constr(x) := apply x.
Tactic Notation "e" constr(x) := exact x.

Ltac f H := split; [a H|e H].
Print Ltac f.

(* Test printing of match context *)
(* Used to fail after translator removal (see BZ#1070) *)

Ltac g := match goal with |- context [if ?X then _ else _ ] => case X end.
Print Ltac g.

(* Test an error message (BZ#5390) *)
Lemma myid (P : Prop) : P <-> P.
Proof. split; auto. Qed.

Goal True -> (True /\ True) -> True.
Proof.
intros H.
Fail intros [H%myid ?].
Fail destruct 1 as [H%myid ?].
Abort.


(* Test that assert_succeeds only runs a tactic once *)
Ltac should_not_loop := idtac + should_not_loop.
Goal True.
  assert_succeeds should_not_loop.
  assert_succeeds (idtac "a" + idtac "b"). (* should only output "a" *)
Abort.
