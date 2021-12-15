Module Test1.

  Module Type Foo.
    Parameter t : unit.
  End Foo.

  Module Bar : Foo.
    Module Type Rnd. Definition t' : unit := tt. End Rnd.
    Module Rnd_inst : Rnd. Definition t' : unit := tt. End Rnd_inst.
    Definition t : unit.
      exact Rnd_inst.t'.
    Qed.
  End Bar.

  Print Assumptions Bar.t.
End Test1.

Module Test2.
  Module Type Foo.
    Parameter t1 : unit.
    Parameter t2 : unit.
  End Foo.

  Module Bar : Foo.
    Inductive ind := .
    Definition t' : unit := tt.
    Definition t1 : unit.
    Proof.
      exact ((fun (_ : ind -> False) => tt) (fun H => match H with end)).
    Qed.
    Definition t2 : unit.
    Proof.
      exact t'.
    Qed.
  End Bar.

  Print Assumptions Bar.t1.
  Print Assumptions Bar.t1.
End Test2.
