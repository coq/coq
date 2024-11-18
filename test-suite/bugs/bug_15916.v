Set Universe Polymorphism. Set Printing Universes.
Monomorphic Universe aboveset.
Module MultiInd.
  Section S.
    Universe u.

    Cumulative Inductive I1 := C1 (_:Type@{u}).

    Cumulative Inductive I2 := C2 (_:I1).
  End S.

  (* !!! should be covariant !!! *)
  Fail Cumulative Inductive I3@{*u} := C3 (_:I2@{u}).

  Cumulative Inductive I3@{u} := C3 (_:I2@{u}).

  (* alternative test without the variance syntax: *)
  Fail Check C3@{Type} _ : I3@{Set}.

  (* should fail but doesn't *)
  Fail Check C3@{aboveset} _ : I3@{Set}.
End MultiInd.

Module WithAxiom.
  Section S.
    Universe u.
    Axiom t : Type@{u}. (* or even a Qed definition *)

    Cumulative Inductive I1 := C1 (_:t).
  End S.

  (* !!! should be invariant !!! *)
  Fail Cumulative Inductive I2@{*u} := C2 (_:I1@{u}).
  Fail Cumulative Inductive I2@{+u} := C2 (_:I1@{u}).
  Cumulative Inductive I2@{u} := C2 (_:I1@{u}).

  (* !!! should not work !!! *)
  Fail Polymorphic Definition lift_t@{u v|} (x:t@{u}) : t@{v}
    := match (C1@{u} x) : I1@{v} with C1 y => y end.
  Fail Polymorphic Definition lift_t@{u v|u < v ?} (x:t@{u}) : t@{v}
    := match (C1@{u} x) : I1@{v} with C1 y => y end.

  (* sanity check that the above 2 test the right thing *)
  Polymorphic Definition lift_t@{u v} (x:t@{u}) : t@{v}
    := match (C1@{u} x) : I1@{v} with C1 y => y end.

End WithAxiom.

Module WithVars.

  Module Rel.
    Fail Cumulative Inductive foo@{*u ?} (X:=Type@{u}) := C (_:X).

    Cumulative Inductive foo@{+u ?} (X:=Type@{u}) := C (_:X).
  End Rel.

  Module Var.
    Section S.
      Universe i.
      Let X:=Type@{i}.
      Cumulative Inductive foo := C (_:X).
    End S.

    Fail Cumulative Inductive bar@{*u} := C' (_:foo@{u}).

    Cumulative Inductive bar@{+u} := C' (_:foo@{u}).
  End Var.

End WithVars.
