Module P.
Private Inductive private_type :=
|cons:private_type.
End P.
Import P.

Inductive new_type: private_type-> Type :=
|cons2: forall m:private_type, new_type m.

Definition my_fun (x:private_type) (y:new_type x) :=
  match y with
  |cons2 _ =>True
  end.

Fail Definition foo (x:P.private_type) := match x with P.cons => tt end.
