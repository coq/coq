Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, nat -> listn n -> listn (S n).

Definition length1 (n : nat) (l : listn n) :=
  match l with
  | consn n _ (consn m _ _) => S (S m)
  | consn n _ _ => 1
  | _ => 0
  end.

Fail Type
  (fun (n : nat) (l : listn n) =>
   match n return nat with
   | O => 0
   | S n => match l return nat with
            | niln => 1
            | l' => length1 (S n) l'
            end
   end).
