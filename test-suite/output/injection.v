(* Test error messages *)

Goal forall x, (x,0) = (0, S x) -> x = 0.
Fail intros x H; injection H as [= H'] H''.
Fail intros x H; injection H as H' [= H''].
intros x H; injection H as [= H' H''].
exact H'.
Qed.
