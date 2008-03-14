(* This has been a bug reported by Y. Bertot *)
Inductive expr : Set :=
  | b : expr -> expr -> expr
  | u : expr -> expr
  | a : expr
  | var : nat -> expr.

Fixpoint f (t : expr) : expr :=
  match t with
  | b t1 t2 => b (f t1) (f t2)
  | a => a
  | x => b t a
  end.

Fixpoint f2 (t : expr) : expr :=
  match t with
  | b t1 t2 => b (f2 t1) (f2 t2)
  | a => a
  | x => b x a
  end.

