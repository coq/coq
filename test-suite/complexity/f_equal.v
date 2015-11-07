(* Checks that f_equal does not reduce the term uselessly *)
(* Expected time < 1.00s *)

Fixpoint stupid (n : nat) : unit :=
match n with
| 0 => tt
| S n =>
  let () := stupid n in
  let () := stupid n in
  tt
end.

Goal stupid 23 = stupid 23.
Timeout 5 Time f_equal.
