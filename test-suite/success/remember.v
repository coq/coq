(* Testing remember and co *)

Lemma A : forall (P: forall X, X -> Prop), P nat 0 -> P nat 0.
intros.
Fail remember nat as X.
Fail remember nat as X in H. (* This line used to succeed in 8.3 *)
Fail remember nat as X in |- *.
Abort.
