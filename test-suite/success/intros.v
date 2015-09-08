(* Thinning introduction hypothesis must be done after all introductions *)
(* Submitted by Guillaume Melquiond (bug #1000) *)

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

(* A short test about introduction pattern pat/c *)
Goal (True -> 0=0) -> True /\ False -> 0=0.
intros H (H1/H,_).
exact H1.
Qed.

(* A test about bugs in 8.5beta2 *)
Goal (True -> 0=0) -> True /\ False -> False -> 0=0.
intros H H0 H1.
destruct H0 as (a/H,_).
(* Check that H0 is removed (was bugged in 8.5beta2) *)
Fail clear H0.
(* Check position of newly created hypotheses when using pat/c (was
   left at top in 8.5beta2) *)
match goal with H:_ |- _ => clear H end. (* clear H1:False *)
match goal with H:_ |- _ => exact H end. (* check that next hyp shows 0=0 *)
Qed.

Goal (True -> 0=0) -> True -> 0=0.
intros H H1/H.
exact H1.
Qed.

Goal forall n, n = S n -> 0=0.
intros n H/n_Sn.
destruct H.
Qed.
