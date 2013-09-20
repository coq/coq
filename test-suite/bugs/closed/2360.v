(* This failed in V8.3 because descend_in_conjunctions built ill-typed terms *)
Definition interp (etyp : nat -> Type) (p: nat) := etyp p.

Record Value (etyp : nat -> Type) := Mk {
  typ : nat; 
  value : interp etyp typ
}.

Definition some_value (etyp : nat -> Type) :  (Value etyp).
Proof.
  intros.
  Fail apply Mk. (* Check that it does not raise an anomaly *)

