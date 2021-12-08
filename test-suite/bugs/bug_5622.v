Module Type HasType.
  Axiom t:Type.
End HasType.

(* This should fail graciously *)
Fail Module M (T1:HasType) <: HasType
  with Definition t := Nat.mul T1.t T1.t.
