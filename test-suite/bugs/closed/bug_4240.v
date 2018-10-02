(* Check that closure of filter did not restrict the former evar filter *)

Lemma foo (new : nat) : False.
evar (H1: nat).
set (H3 := 0).
assert (H3' := id H3).
evar (H5: nat).
clear H3.
assert (H5 = new).
unfold H5.
unfold H1.
exact (eq_refl new).
