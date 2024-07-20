From Stdlib Require Import Zify ZifyUint63 ZifySint63 Sint63 Uint63 ZArith Lia.

Lemma boom : False.
Proof.
  assert (sint_bad : forall y z : int, Sint63Axioms.to_Z (y / z) = Uint63Axioms.to_Z (y / z)).
  { zify. Fail reflexivity.
  (*}
  specialize (sint_bad (-1)%sint63 1%uint63).
  vm_compute in sint_bad. (* sint_bad : (-1)%Z = 9223372036854775807%Z *)
  congruence. *)
Abort.
