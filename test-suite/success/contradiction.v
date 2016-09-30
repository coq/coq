(* Some tests for contradiction *)

Lemma L1 : forall A B : Prop, A -> ~A -> B.
Proof.
intros; contradiction.
Qed.

Lemma L2 : forall A B : Prop, ~A -> A -> B.
Proof.
intros; contradiction.
Qed.

Lemma L3 : forall A : Prop, ~True -> A.
Proof.
intros; contradiction.
Qed.

Lemma L4 : forall A : Prop, forall x : nat, ~x=x -> A.
Proof.
intros; contradiction.
Qed.

Lemma L5 : forall A : Prop, forall x y : nat, ~x=y -> x=y -> A.
Proof.
intros; contradiction.
Qed.

Lemma L6 : forall A : Prop, forall x y : nat, x=y -> ~x=y -> A.
Proof.
intros; contradiction.
Qed.

