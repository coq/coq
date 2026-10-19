(* Thrash.v with an inductive in place of the constant: MA.I is one user name
   with two canonical names, M.I where it is written directly and MA.I inside
   Q's implementation. Walking Q.d does not record the block again under MA.I,
   so the entry for z3's closure is kept and the second query on z3 is
   replayed. *)

Set Debug "assumptions-cache".

Axiom ax : nat.
Module Type T. Inductive I := c0 : nat -> I. End T.
Module M : T. Inductive I := c0 : nat -> I. End M.
Module MA := M.
Module Type T2. Parameter d : nat. End T2.
Module F (X : T) : T2. Definition d := match X.c0 ax with X.c0 k => k end. End F.
Module Q := F MA.
Definition z0 := match MA.c0 ax with MA.c0 k => k end.
Definition z1 := S z0.
Definition z2 := S z1.
Definition z3 := S z2.
Print Assumptions z3.
Print Assumptions Q.d.
Print Assumptions z3.
Print Assumptions Q.d.
