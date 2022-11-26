Inductive Box : Type -> Type :=
| box : forall A, A -> Box A.

Fail Definition open_box (s : Box unit) : unit :=
  match s with
  | box _ x => x
  end.
