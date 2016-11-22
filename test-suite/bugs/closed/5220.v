(* Check that destruct does not use only the name to tell that a goal
   variable is a section variable *)

Section foo.
Context (H : True).

Lemma bar : True \/ True -> True.
Proof.
  (* Does not remove H : True \/ True *)
  clear H. intros H. destruct H as [H'|H'].
  Fail Check H.
Abort.
