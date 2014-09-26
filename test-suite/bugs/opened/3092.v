Fail Fixpoint le_pred (n1 n2 : nat) (H1 : n1 <= n2) : pred n1 <= pred n2 :=
  match H1 with
  | le_n      => le_n (pred _)
  | le_S _ H2 =>
    match n2 with
    | 0   => fun H3 => H3
    | S _ => le_S _ _
    end (le_pred _ _ H2)
  end.
