
Lemma test
      (R : nat -> Prop)
      (_ : True)
      (G : R 0)
      (M : (exists n : nat, 0 = n) /\ True)
  : True.
Proof.
  destruct M as [[n K] _].
  rewrite K in G.
  exact I.
Qed.

Print test.
(* Used to be:
Anomaly "Uncaught exception Not_found."
Please report at http://coq.inria.fr/bugs/.
*)


Lemma test1
      (_ : True)
      (R : nat -> Prop)
      (G : R 0)
      (M : (exists n : nat, 0 = n) /\ True)
  : True.
Proof.
  destruct M as [[n K] _].
  rewrite K in G.
  exact I.
Qed.

Print test1.
(*  Used to be:
Anomaly "Uncaught exception Retyping.RetypeError(0)."
Please report at http://coq.inria.fr/bugs/.
*)
