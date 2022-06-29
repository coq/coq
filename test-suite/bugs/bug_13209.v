Class A (n : nat) := {}.
Definition three := 3.
#[export] Instance A_three : A three := {}.
Definition three' := if true then three else 1.
(* 1 *) Goal A (if true then three else 1). apply _. Qed.
#[export] Hint Opaque three : typeclass_instances.
(* 2 *) Goal A (if true then three else 1). apply _. Qed.
(* 3 *) Goal A (three'). apply _. Qed.
