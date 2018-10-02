(* Are recursively non-uniform params correctly treated? *)
Inductive list (A:nat -> Type) n := cons : A n -> list A (S n) -> list A n.
Inductive term n := app (l : list term n).
Definition term_list :=
  fix term_size n (t : term n) (acc : nat) {struct t} : nat :=
    match t with
    | app _ l =>
      (fix term_list_size n (l : list term n) (acc : nat) {struct l} : nat :=
      match l with
      | cons _ _ t q => term_list_size (S n) q (term_size n t acc)
      end) n l (S acc)
    end.
