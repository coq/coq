(* coq-prog-args: ("-nois") *)

Notation "[ a + + * .. + + * c | d ]" := (forall _ : a, .. (forall _ : c, d) ..) (a at level 10).
Print Grammar constr.
