(* Testing remember and co *)

Lemma A : forall (P: forall X, X -> Prop), P nat 0 -> P nat 0.
intros.
Fail remember nat as X.
Fail remember nat as X in H. (* This line used to succeed in 8.3 *)
Fail remember nat as X.
Abort.

(* Testing Ltac interpretation of remember (was not working up to r16181) *)

Goal (1 + 2 + 3 = 6).
let name := fresh "fresh" in
remember (1 + 2) as x eqn:name.
rewrite fresh.
Abort.

(* An example which was working in 8.4 but failing in 8.5 and 8.5pl1 *)
                  
Module A.
Axiom N : nat.
End A.
Module B.
Include A.
End B.
Goal id A.N = B.N.
reflexivity.
Qed.           
                
