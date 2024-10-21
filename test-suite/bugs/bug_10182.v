Require Import TestSuite.arith.

Goal
  forall A m pf1 pf2
         (H : (fun _ : False => A) = (fun _ : False => A)),
    match Nat.nlt_0_r m pf1 with end = match Nat.nlt_0_r m pf2 with end :> A.
Proof.
 intros.
 Fail rewrite H.
Abort.
