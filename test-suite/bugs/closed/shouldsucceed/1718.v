(* lazy delta unfolding used to miss delta on rels and vars (fixed in 10172) *)

Check
  let g := fun _ => 0 in
  fix f (n : nat) :=
  match n with
  | 0 => g f
  | S n' => 0
  end.
