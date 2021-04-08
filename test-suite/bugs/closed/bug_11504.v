(* These examples should fail with "Unable to find an instance for the variable ..." *)
(* but they used to raise an anomaly from 8.5 to 8.13 *)

Definition hl_inv(a b c: nat): Prop := a > 0 /\ b > 0.

Goal forall a b,
    (forall m, hl_inv a b m) ->
    True.
Proof.
  intros.
  Fail destruct H.
Abort.

Definition R (arg: bool) : Type := bool.

Definition r (arg: bool) : R arg := false.

Goal True.
  Fail destruct r.
Abort.

(* #14090 *)
Lemma t (H : forall x, (fun _ : unit => unit) x) : True.
Fail destruct H.
Abort.
