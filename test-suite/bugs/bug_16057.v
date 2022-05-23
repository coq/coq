Record squash (A : Type) : Prop := sq { _ : A }.

(* This is a contrived test to check that squash is *not* template poly. A
   template poly behaves as is it were living in Type for typing purposes,
   so the name [H] below generated for the hypothesis would be instead based on
   the type of the argument (i.e. [f] for [False]). *)
Goal squash False -> True.
Proof.
intros [?].
destruct H.
Qed.
