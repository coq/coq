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

(* Test custom entries in Ltac *)
Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "< x >" := x (in custom myconstr, at level 3, x custom anotherconstr at level 10).
Notation "# x" := (Some x) (in custom anotherconstr, at level 8, x constr at level 9).
Tactic Notation "f" myconstr(c) := idtac c.
Goal True.
f <#True>.
Abort.
