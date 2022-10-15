Goal False.
Proof.
assert (H: forall x:unit, False).
{ native_cast_no_check (fun x:unit => I). }
exact (H tt).
Fail Qed.
Abort.
