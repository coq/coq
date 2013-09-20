
Fail Definition Berry (x y z : bool) :=
  match x, y, z with
  | true, false, _ => 0
  | false, _, true => 1
  | _, true, false => 2
  end.
