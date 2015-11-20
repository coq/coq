(* This wrongly succeeded in 8.3pl5 *)

Inductive IND : forall X:Type, let Y:=X in Type :=
  C : IND True.

Definition F (x:IND True) (A:Type) :=
  match x in IND Y Z return Z with
  C => I
  end.

Theorem paradox : False.
Fail Proof (F C False).
