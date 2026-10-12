Module Type A.
  Parameter t: Type.
  Parameter len : t -> nat.
  Parameter len2 : t -> nat.
End A.

Module A_impl.
  Definition t : Type := list nat.
  (* Adding incr to A fixes the anomaly *)
  Definition incr (n: nat) := S n.
  Definition len (m: t) := incr (length m).
  Definition len2 (m: t) := length m.
End A_impl.

Module Type B.
  Declare Module M : A.
End B.

Module Type Bp.
  Include B.
End Bp.

Declare Module Bp0 : Bp with Module M := A_impl.

Module Bp_inst.
  (* Using instead "Include B with Module M := A_impl" also fixes the anomaly *)
  Include Bp0.
End Bp_inst.

(* This Print works *)
Print Bp_inst.M.len2.

(* This Print raises an anomaly *)
Print Bp_inst.M.len.
