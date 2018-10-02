(* Another instance of bug #3262, on looping in unification *)

Inductive bool := true | false.

Inductive RBT2 : forall a:bool, Type :=
 Full2 : forall (a b c n:bool),
            forall H:RBT2 n, RBT2 n.

Definition balance4 color p q r :=
  match color, p, q, r with
      | _,_,_,_ => Full2 color p q r
  end.
