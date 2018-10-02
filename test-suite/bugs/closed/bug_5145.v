Class instructions :=
  {
    W : Type;
    ldi : nat -> W
  }.

Fail Definition foo :=
  let y2 := ldi 0 in
  let '(CF, _) := (true, 0) in
  y2.
