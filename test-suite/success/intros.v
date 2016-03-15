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
