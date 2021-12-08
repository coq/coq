Set Universe Polymorphism.

Record Type_Over (X : Type)
:= { Domain :> Type;
     proj : Domain -> X }.

Definition Self_Over (X : Type)
  := {| Domain := X; proj := (fun x => x) |}.

Canonical Structure Self_Over. (* fails with Anomaly: Mismatched instance and context when building universe substitution. Please report. for polymorphic structures *)
(* if monomorphic, Warning: No global reference exists for projection
 valuefun x : _UNBOUND_REL_1 => x in instance Self_Over of proj, ignoring it. *)
