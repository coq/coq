(* -*- coq-prog-args: ("-noinit"); -*- *)
Require Import Ltac.
Unset Elimination Schemes.
Inductive unit : Set := tt.

Module Type S.
  Parameter value : unit.
End S.

Module Implemented : S.
  Definition value := tt.
End Implemented.

Module WithAxiom : S.
  Axiom hidden : unit.
  Definition value : unit.
  Proof. exact hidden.
  Qed.
End WithAxiom.

Module Nested.
  Module Inner : S.
    Definition value : unit.
    Proof. exact tt.
    Qed.
  End Inner.
End Nested.

Module Alias := Implemented.
Declare Module Abstract : S.
Axiom declared : unit.
