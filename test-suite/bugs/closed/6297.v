Set Printing Universes.

(* Error: Anomaly "Uncaught exception "Anomaly: Incorrect universe Set
   declared for inductive type, inferred level is max(Prop, Set+1)."."
   Please report at http://coq.inria.fr/bugs/. *)
Fail Record LTS: Set :=
  lts { St: Set;
        init: St }.
