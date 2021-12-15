Unset Asymmetric Patterns.

Definition goodid : forall {A} (x: A), A := fun A x => x.
Definition wrongid : forall A (x: A), A := fun {A} x => x.

Inductive ty := N | B.

Inductive alt_list : ty -> ty -> Type :=
  | nil {k} : alt_list k k
  | Ncons {k} : nat -> alt_list B k -> alt_list N k
  | Bcons {k} : bool -> alt_list N k -> alt_list B k.

Definition trullynul k {k'} (l : alt_list k k') :=
match k,l with
 |N,l' => Ncons 0 (Bcons true l')
 |B,l' => Bcons true (Ncons 0 l')
end.

(* At some time, the success of trullynul was dependent on the name of
   the variables! *)

Definition trullynul2 k {a} (l : alt_list k a) :=
match k,l with
 |N,l' => Ncons 0 (Bcons true l')
 |B,l' => Bcons true (Ncons 0 l')
end.

Definition trullynul3 k {z} (l : alt_list k z) :=
match k,l with
 |N,l' => Ncons 0 (Bcons true l')
 |B,l' => Bcons true (Ncons 0 l')
end.

Fixpoint app (P : forall {k k'}, alt_list k k' -> alt_list k k') {t1 t2} (l : alt_list t1 t2) {struct l}: forall {t3}, alt_list t2 t3 ->
alt_list t1 t3 :=
  match l with
  | nil => fun _ l2 => P l2
  | Ncons n l1 => fun _ l2 => Ncons n (app (@P) l1 l2)
  | Bcons b l1 => fun _ l2 => Bcons b (app (@P) l1 l2)
  end.

Check (fun {t t'} (l: alt_list t t') =>
 app trullynul (goodid l) (wrongid _ nil)).
