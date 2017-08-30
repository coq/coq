Module WithoutProj.
Record foo := Foo {
  foo_car : Type;
  foo_op : foo_car -> foo_car -> foo_car
}.
Arguments foo_op : simpl never.

Definition nat_foo := Foo nat plus.

Goal match foo_op nat_foo 10 10 with 0 => True | _ => False end.
  simpl. 
  match goal with
    |- match foo_op nat_foo 10 10 with
       | 0 => True
       | S _ => False
       end => idtac
  end.
  unfold foo_op; simpl.
  match goal with
    |- False => idtac
  end.
  Undo 2.
  cbn.
  match goal with
    |- match foo_op nat_foo 10 10 with
       | 0 => True
       | S _ => False
       end => idtac
  end.
  unfold foo_op; cbn.
  match goal with
    |- False => idtac
  end.
Abort.
End WithoutProj.

Set Primitive Projections.
Module WithProj.
Record foo := Foo {
  foo_car : Type;
  foo_op : foo_car -> foo_car -> foo_car
}.
Arguments foo_op : simpl never.

Definition nat_foo := Foo nat plus.

Goal match foo_op nat_foo 10 10 with 0 => True | _ => False end.
  simpl. 
  match goal with
    |- match foo_op nat_foo 10 10 with
       | 0 => True
       | S _ => False
       end => idtac
  end.
  unfold foo_op; simpl.
  match goal with
    |- False => idtac
  end.
  Undo 2.
  cbn.
  match goal with
    |- match foo_op nat_foo 10 10 with
       | 0 => True
       | S _ => False
       end => idtac
  end.
  unfold foo_op; cbn.
  match goal with
    |- False => idtac
  end.
Abort.
End WithProj.
