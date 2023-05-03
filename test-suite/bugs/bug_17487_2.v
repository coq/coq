(* Potpourri of inconsistencies between intros [] and destruct and fringe behaviours w.r.t. dependent metas *)

Goal forall (f : nat -> bool), True.
Proof.
intros [].
+ match goal with [ |- nat ] => exact 0 end.
+ match goal with [ |- True ] => exact I end.
+ match goal with [ |- True ] => exact I end.
Qed.

Goal forall (f : nat -> bool), True.
Proof.
intros f; destruct f.
+ match goal with [ |- nat ] => exact 0 end.
+ match goal with [ |- True ] => exact I end.
+ match goal with [ |- True ] => exact I end.
Qed.


Goal forall (f : nat -> bool), f = f.
Proof.
Fail intros [].
Abort.

Goal forall (f : nat -> bool), f = f.
Proof.
intros f; destruct f.
+ match goal with [ |- nat ] => exact 0 end.
+ match goal with [ |- f = f ] => reflexivity end.
+ match goal with [ |- f = f ] => reflexivity end.
Qed.


Goal forall (f : forall n : nat, 0 = n), True.
Proof.
Fail intros [].
Abort.

Goal forall (f : forall n : nat, 0 = n), True.
Proof.
Fail intros f; destruct f.
Abort.


Goal forall (f : forall n : nat, 0 = n), f = f.
Proof.
Fail intros [].
Abort.

Goal forall (f : forall n : nat, 0 = n), f = f.
Proof.
Fail intros f; destruct f.
Abort.


Goal forall (f : forall n : nat, n = 0), True.
Proof.
Fail intros [].
Abort.

Goal forall (f : forall n : nat, n = 0), True.
Proof.
Fail intros f; destruct f.
Abort.
