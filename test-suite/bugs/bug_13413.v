Goal forall (A B : Prop) (H : A -> B), A -> A -> B.
intros A B H ?%H H0.
exact H1.
Qed.

Goal forall (A B : Prop) (H : A -> B), A -> A -> B.
intros A B H ?H%H H0.
exact H1.
Qed.

Goal forall (A B : Prop) (H : A -> B), A -> A -> B.
intros A B H J%H H0.
exact J.
Qed.

Set Mangle Names.
Goal forall (A B : Prop) (H : A -> B), A -> A -> B.
intros A B H ?%H _0.
assumption.
Qed.
