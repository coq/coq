(** Checks that Ltac's '+' tactical works as intended. *)

Goal forall (A B C D:Prop), (A->C) -> (B->C) -> (D->C) -> B -> C.
Proof.
  intros A B C D h0 h1 h2 h3.
  (* backtracking *)
  (apply h0 + apply h1);apply h3.
  Undo.
  Fail ((apply h0+apply h2) || apply h1); apply h3.
  (* interaction with || *)
  ((apply h0+apply h1) || apply h2); apply h3.
Qed.
