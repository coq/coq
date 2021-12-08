Unset Primitive Projections.

Record Box (A:Type) := box { unbox : A }.
Arguments box {_} _. Arguments unbox {_} _.

Definition map {A B} (f:A -> B) x :=
  match x with box x => box (f x) end.

Definition tuple (l : Box Type) : Type :=
  match l with
  | box x => x
  end.

Fail Inductive stack : Type -> Type :=
| Stack T foos :
  tuple (map stack foos) ->
  stack T.
