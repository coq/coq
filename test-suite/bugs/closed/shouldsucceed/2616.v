(* Testing ill-typed rewrite which used to succeed in 8.3 *)
Goal 
  forall (N : nat -> Prop) (g : nat -> sig N) (IN : forall a : sig N, a = g 0), 
    N 0 -> False.
Proof.
intros.
Fail rewrite IN in H.
