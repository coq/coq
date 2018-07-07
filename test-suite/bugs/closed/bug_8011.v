Goal forall a b : nat, forall (X:a = b), True.
  intros.
  Fail let T := constr:(a = b) in
    destruct X;
      pose (fun Y:T => ltac:(destruct Y; exact I) : True);
    exact I.
(* was: Anomaly "variable b unbound." Please report at http://coq.inria.fr/bugs/. *)
Abort.

Goal forall a b : nat, forall (X:a = b), True.
  intros.
  Fail let T := constr:(a = b) in
    destruct X;
      pose (fun Y:T => ltac:(induction Y; exact I) : True);
    exact I.
(* Was: Anomaly "variable b unbound." Please report at http://coq.inria.fr/bugs/. *)
Abort.

Goal forall a b : nat, True.
intros.
Fail let T := constr:(a = b) in clear b; pose (fun Y:T => Y).
(* was not failing but building a wrong context *)
Abort.
