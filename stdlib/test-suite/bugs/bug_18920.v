(* Check that obligations resulting from evars in the binders are
   correctly substituted for wf/measure fixpoints *)
From Stdlib Require Import Program.
Program Fixpoint f (A : nat * _) (n:nat) {measure n} : nat :=
    match n with 0 => 0 | S n => f A n end.
Next Obligation. exact nat. Defined.
Next Obligation. Admitted.
(* used to return an Anomaly "in econstr: grounding a non evar-free term" *)
