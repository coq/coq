Inductive sTrue : SProp := sI.

(* Singleton Prop to SProp *)
Definition elim0 (x : False) : sTrue := match x return sTrue with end.
Definition elim0' (x : False) : sTrue := match x with end.

(* Non-singleton Prop to SProp *)
Definition elim1 (x : inhabited nat) : sTrue := match x return sTrue with inhabits _ => sI end.
Definition elim1' (x : inhabited nat) : sTrue := match x with inhabits _ => sI end.
