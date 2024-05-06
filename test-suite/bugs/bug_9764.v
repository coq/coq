Notation "[ 'fun' x => F ]" := (fun x => F)
  (at level 0, x ident, only parsing).
               (* or `x pattern` *)

Implicit Types (n : nat).

Definition nat_id := [fun n => n].
