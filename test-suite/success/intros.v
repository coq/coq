(* Thinning introduction hypothesis must be done after all introductions *)
(* Submitted by Guillaume Melquiond (bug #1000) *)

Goal forall A, A -> True.
intros _ _.


