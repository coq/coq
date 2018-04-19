(* Thinning introduction hypothesis must be done after all introductions *)
(* Submitted by Guillaume Melquiond (BZ#1000) *)

Goal forall A, A -> True.
intros _ _.
Abort.

(* This did not work until March 2013, because of underlying "red" *)
Goal (fun x => True -> True) 0.
intro H.
Abort.

(* This should still work, with "intro" calling "hnf" *)
Goal (fun f => True -> f 0 = f 0) (fun x => x).
intro H.
match goal with [ |- 0 = 0 ] => reflexivity end.
Abort.

(* Somewhat related: This did not work until March 2013 *)
Goal (fun f => f 0 = f 0) (fun x => x).
hnf.
match goal with [ |- 0 = 0 ] => reflexivity end.
Abort.

(* Fixing behavior of "*" and "**" in branches, so that they do not
   introduce more than what the branch expects them to introduce at most *)
Goal forall n p, n + p = 0.
intros [|*]; intro p.
Abort.

(* Check non-interference of "_" with name generation *)
Goal True -> True -> True.
intros _ ?.
exact H.
Qed.

(* A short test about introduction pattern pat%c *)
Goal (True -> 0=0) -> True /\ False -> 0=0.
intros H (H1%H,_).
exact H1.
Qed.

(* A test about bugs in 8.5beta2 *)
Goal (True -> 0=0) -> True /\ False -> False -> 0=0.
intros H H0 H1.
destruct H0 as (a%H,_).
(* Check that H0 is removed (was bugged in 8.5beta2) *)
Fail clear H0.
(* Check position of newly created hypotheses when using pat%c (was
   left at top in 8.5beta2) *)
match goal with H:_ |- _ => clear H end. (* clear H1:False *)
match goal with H:_ |- _ => exact H end. (* check that next hyp shows 0=0 *)
Qed.

Goal (True -> 0=0) -> True -> 0=0.
intros H H1%H.
exact H1.
Qed.

Goal forall n, n = S n -> 0=0.
intros n H%n_Sn.
destruct H.
Qed.

(* Another check about generated names and cleared hypotheses with
   pat%c patterns *)
Goal (True -> 0=0 /\ 1=1) -> True -> 0=0.
intros H (H1,?)%H.
change (1=1) in H0.
exact H1.
Qed.

(* Checking iterated pat%c1...%cn introduction patterns and side conditions *)

Goal forall A B C D:Prop, (A -> B -> C) -> (C -> D) -> B -> A -> D.
intros * H H0 H1.
intros H2%H%H0.
- exact H2.
- exact H1.
Qed.

(* Bug found by Enrico *)

Goal forall x : nat, True.
intros y%(fun x => x).
Abort.

(* Fixing a bug in the order of side conditions of a "->" step *)

Goal (True -> 1=0) -> 1=1.
intros ->.
- reflexivity.
- exact I.
Qed.

Goal forall x, (True -> x=0) -> 0=x.
intros x ->.
- reflexivity.
- exact I.
Qed.

(* Fixing a bug when destructing a type with let-ins in the constructor *)

Inductive I := C : let x:=1 in x=1 -> I.
Goal I -> True.
intros [x H]. (* Was failing in 8.5 *)
Abort.

(* Ensuring that the (pat1,...,patn) intropatterns has the expected size, up
   to skipping let-ins *)

Goal I -> 1=1.
intros (H).  (* This skips x *)
exact H.
Qed.

Goal I -> 1=1.
Fail intros (x,H,H').
Fail intros [|].
intros (x,H).
exact H.
Qed.

Goal Acc le 0 -> True.
Fail induction 1 as (n,H). (* Induction hypothesis is missing *)
induction 1 as (n,H,IH).
exact Logic.I.
Qed.

(* Make "intro"/"intros" progress on existential variables *)

Module Evar.

Goal exists (A:Prop), A.
eexists.
unshelve (intro x).
- exact nat.
- exact (x=x).
- auto.
Qed.

Goal exists (A:Prop), A.
eexists.
unshelve (intros x).
- exact nat.
- exact (x=x).
- auto.
Qed.

Definition d := ltac:(intro x; exact (x*x)).

Definition d' : nat -> _ := ltac:(intros;exact 0).

End Evar.
