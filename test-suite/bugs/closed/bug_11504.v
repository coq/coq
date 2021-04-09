(* These examples should generate side conditions for the non-instantiated non-dependent parameters *)
(* but they used to raise an anomaly from 8.5 to 8.13 *)

Definition hl_inv(a b c: nat): Prop := a > 0 /\ b > 0.

Goal forall a b,
    (forall m, hl_inv a b m) ->
    True.
Proof.
  intros.
  destruct H.
Abort.

Definition R (arg: bool) : Type := bool.

Definition r (arg: bool) : R arg := false.

Goal True.
  destruct r.
Abort.

(* #14090 *)
Lemma t (H : forall x, (fun _ : unit => unit) x) : True.
destruct H.
Abort.
