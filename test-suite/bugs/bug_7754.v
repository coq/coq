
Set Universe Polymorphism.

Module OK.

  Inductive one@{i j} : Type@{i} :=
  with two : Type@{j} := .
  Check one@{Set Type} : Set.
  Fail Check two@{Set Type} : Set.

End OK.

Module Bad.

  Fail Inductive one :=
    with two@{i +} : Type@{i} := .

  Fail Inductive one@{i +} :=
    with two@{i +} := .

End Bad.
