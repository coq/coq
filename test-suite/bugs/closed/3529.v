(* Check that Prop can be inferred to fill some sorts *)

Module Example1.
Class R T := { f: T -> Prop }.
Instance r : R Prop := {| f P := P -> P |}.
Definition foo : R Prop := Build_R _ (fun P => P -> P).
End Example1.

Require Coq.Setoids.Setoid.
Import Coq.Setoids.Setoid.

Module Example2.
Class ILogicOps Frm := { lentails: relation Frm }.
Instance ILogicOps_Prop : ILogicOps Prop | 2 := {| lentails P Q := P -> Q |}.
Definition ILogicOps_Prop' : ILogicOps Prop := {| lentails P Q := P -> Q |}.
End Example2.
