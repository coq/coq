(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)
Goal forall (P : SProp), P -> P.
Proof.
  intros P H. set (H0 := H).
  (* goal is now H0 *)
  exact H0.
Qed.
