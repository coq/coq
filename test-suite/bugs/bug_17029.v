Require Import Setoid.

Definition mydef (A B : Type) := True.

Goal (forall A B : Type, mydef A B) -> Type.
intros.
Fail rewrite <- H.
(* Anomaly
"Unable to handle arbitrary u+k <= v constraints."
Please report at http://coq.inria.fr/bugs/. *)
Abort.
