Module Type T1.
  Parameter t : Type.
End T1.

Module Type T2.
  Declare Module M : T1.
  Parameter t : Type.
  Parameter test : t = M.t.
End T2.

Module M1 <: T1.
  Definition t : Type := bool.
End M1.

Module M2 <: T2.
  Module M := M1.
  Definition t : Type := nat.
  Lemma test : t = t. Proof. reflexivity. Qed.
End M2.
