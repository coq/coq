CoInductive A: Set :=
  mk_A: B -> A
with B: Set :=
  mk_B: A -> B.

CoFixpoint a:A := mk_A b
with b:B := mk_B a.

Goal b = match a with mk_A a1 => a1 end.
  simpl. reflexivity.
Qed.


