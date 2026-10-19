(* Print Assumptions reuses traversals across queries in one environment.
   Reset rolls the environment back; nothing from before it may be
   replayed after it. *)

Axiom ax1 : nat.
Axiom ax2 : nat.
Definition f := ax1.
Definition g := f.
Print Assumptions g.
Reset f.
Definition f := ax2.
Definition g := f.
Print Assumptions g.
Print Assumptions f.
