(* -*- coq-prog-args: ("-profile-ltac") -*- *)
Require Coq.ZArith.BinInt.
Module WithIdTac.
  Ltac sleep := do 50 (idtac; let sleep := (eval vm_compute in Coq.ZArith.BinInt.Z.div_eucl) in idtac).

  Ltac foo0 := idtac; sleep.
  Ltac foo1 := sleep; foo0.
  Ltac foo2 := sleep; foo1.
  Goal True.
    foo2.
    Show Ltac Profile CutOff 47.
    constructor.
  Qed.
End WithIdTac.

Module TestEval.
  Ltac sleep := let sleep := (eval vm_compute in Coq.ZArith.BinInt.Z.div_eucl) in idtac.

  Ltac foo0 := idtac; do 50 (idtac; sleep).
  Ltac foo1 := sleep; foo0.
  Ltac foo2 := sleep; foo1.
  Goal True.
    Reset Ltac Profile.
    foo2.
    Show Ltac Profile CutOff 47.
    constructor.
  Qed.
End TestEval.
