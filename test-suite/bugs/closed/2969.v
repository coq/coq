Require Import TestSuite.admit.
(* Check that Goal.V82.byps and Goal.V82.env are consistent *)

(* This is a shorten variant of the initial bug which raised anomaly *)

Goal forall x : nat, (forall z, (exists y:nat, z = y) -> True) -> True.
evar nat.
intros x H.
apply (H n).
unfold n. clear n.
eexists.
reflexivity.
Grab Existential Variables.
admit.
Admitted.

(* Alternative variant which failed but without raising anomaly *)

Goal forall x : nat, True.
evar nat.
intro x.
evar nat.
assert (H := eq_refl : n0 = n).
clearbody n n0.
exact I.
Grab Existential Variables.
admit.
Admitted.
