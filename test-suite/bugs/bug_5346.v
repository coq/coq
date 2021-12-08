Inductive comp : Type -> Type :=
| Ret {T} : forall (v:T), comp T
| Bind {T T'} : forall (p: comp T') (p': T' -> comp T), comp T.

Notation "'do' x .. y <- p1 ; p2" :=
  (Bind p1 (fun x => .. (fun y => p2) ..))
    (at level 60, right associativity,
     x binder, y binder).

Definition Fst1 A B (p: comp (A*B)) : comp A :=
  do '(a, b) <- p;
    Ret a.

Definition Fst2 A B (p: comp (A*B)) : comp A :=
  match tt with
  | _ => Bind p (fun '(a, b) => Ret a)
  end.

Definition Fst3 A B (p: comp (A*B)) : comp A :=
  match tt with
  | _ => do a <- p;
          Ret (fst a)
  end.

Definition Fst A B (p: comp (A * B)) : comp A :=
  match tt with
  | _ => do '(a, b) <- p;
          Ret a
  end.
