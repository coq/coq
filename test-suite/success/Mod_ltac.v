(* Submitted by Houda Anoun *)

Module toto.
Ltac titi := auto.
End toto.

Module ti.
Import toto.
Ltac equal := match goal with
              |  |- (?X1 = ?X1) => titi
              |  |- _ => idtac
              end.

End ti.

Import ti.
Definition simple : forall a : nat, a = a.
intro.
equal.
Qed.
