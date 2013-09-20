(* Check that expansion of alias in pattern-matching compilation is no
   longer dependent of whether the pattern-matching problem occurs in a
   typed context or at toplevel (solved from revision 10883) *)

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

