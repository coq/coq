Module Record.
  Record foo := {x:nat; y:nat}.

  Existing Class foo.

  Fail Instance baz : foo := _.

  #[refine] Instance bar : foo := {}.
  Proof.
    1,2:exact 0.
  Qed.

  Instance bar' : foo := {x:=0; y:=0}.

  Instance baz : foo := _.

  Instance baz' : foo.
  Proof.
    exact baz.
  Qed.
End Record.

Module Inductive.

  Inductive foo := mkfoo (x:nat) (y:nat).

  Existing Class foo.

  Fail Instance baz : foo := _.

  #[refine] Instance bar : foo := {}.
  Proof.
    constructor.
    1,2:exact 0.
  Qed.

  Fail Instance bar' : foo := {x:=0; y:=0}.

  Instance baz : foo := _.

  Instance baz' : foo.
  Proof.
    exact baz.
  Qed.
End Inductive.

Module EmptyRecord.
  Record foo := {}.

  Existing Class foo.

  Fail Instance baz : foo := _.

  Instance bar : foo := {}.

  Instance baz : foo := _.

  Instance baz' : foo.
  Proof.
    exact baz.
  Qed.
End EmptyRecord.
