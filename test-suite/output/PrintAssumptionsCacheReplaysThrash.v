(* MA.d is one user name with two canonical names: M.d where it is written
   directly, and MA.d inside Q's implementation, which Print Assumptions reads
   through the sealed functor application. Walking Q.d does not replace the
   entry recorded for x2's closure, so the later queries on x2 are replayed. *)

Set Debug "assumptions-cache".

Axiom ax : nat.
Module Type T. Parameter d : nat. End T.
Module M : T. Definition d := ax. End M.
Module MA := M.
Module F (X : T) : T. Definition d := X.d. End F.
Module Q := F MA.
Definition x0 := MA.d.
Definition x1 := x0.
Definition x2 := x1.
Print Assumptions x2.
Print Assumptions Q.d.
Print Assumptions x2.
Print Assumptions Q.d.
Print Assumptions x2.
