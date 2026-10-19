(* Print Assumptions reuses traversals across queries in one environment.
   Print Opaque, Transparent and All Dependencies share that traversal. *)

Axiom ax : nat.
Definition tr := ax + 1.
Lemma op : tr = tr. Proof. reflexivity. Qed.
Definition both := op.
Print Assumptions both.
Print Opaque Dependencies both.
Print Transparent Dependencies both.
Print All Dependencies both.
Print All Dependencies both.
Print Opaque Dependencies op.
Print Assumptions both.
