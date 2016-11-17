(*See below. They sometimes work, and sometimes do not. Is this a bug?*)

Require Import Omega Psatz.

Definition foo := nat.

Goal forall (n : foo), 0 = n - n.
Proof. intros. omega. (* works *) Qed.

Goal forall (x n : foo), x = x + n - n.
Proof.
  intros.
  Fail omega. (* Omega can't solve this system *)
  Fail lia. (* Cannot find witness. *)
  unfold foo in *.
  omega. (* works *)
Qed.

(* Guillaume Melquiond: What matters is the equality. In the first case, it is @eq nat. In the second case, it is @eq foo. The same issue exists for ring and field. So it is not a bug, but it is worth fixing.*)
