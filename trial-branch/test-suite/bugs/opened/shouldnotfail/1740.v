
Definition f :=
  fun n m : nat =>
    match n, m with
      | O, _ => O
      | n, O => n
      | _, _ => O
    end.

Goal f =
  fun n m : nat =>
    match n, m with
      | O, _ => O
      | n, O => n
      | _, _ => O
    end.
  unfold f. 
  reflexivity.
Qed.

