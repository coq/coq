(* Until revision 10221, rewriting in hypotheses of the form
   "(fun x => phi(x)) t" with "t" not rewritable used to behave as a
   beta-normalization tactic instead of raising the expected message
   "nothing to rewrite" *)

Goal forall b, S b = O -> (fun a => 0 = (S a)) b -> True.
  intros b H H0.
  Fail rewrite H in H0.
