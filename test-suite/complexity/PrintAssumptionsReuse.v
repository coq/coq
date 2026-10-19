(* Expected time < 0.05s *)

(** [Print Assumptions] reuses the traversal of an earlier query in the same
    environment (#5639). [t1] and [t2] share the closure of [big], a complete
    binary tree of depth 20: the first query walks it, which takes about
    0.2 s, and the second query, which is timed, does not walk it again. *)

Inductive tree := leaf | node (l r : tree).

Fixpoint build (n : nat) : tree :=
  match n with 0 => leaf | S m => node (build m) (build m) end.

Axiom ax : tree.

Definition big := Eval vm_compute in node ax (build 20).

Definition t1 := node big leaf.
Definition t2 := node leaf big.

Print Assumptions t1.
Time Print Assumptions t2.
