Require Import Reals.

Open Scope R_scope.

Parameter Rpow : R -> R -> R.

Axiom Rpow_convert_Z : forall x n,
  Rpow x (IZR n) = pow x (Z.abs_nat n).

Lemma Rpow_non_0 x y : x <> 0 -> Rpow x (IZR y) <> 0.
Proof.
now rewrite Rpow_convert_Z; apply pow_nonzero.
Qed.

Ltac to_pow :=
  repeat
    (match goal with |- context [Rpow ?x (IZR (Z.pos ?n))] =>
      let nN := constr:(Z.abs_nat (Z.pos n)) in
      let v := eval compute in nN in
        replace (Rpow x (IZR (Z.pos n))) with (pow x v);
         [ | rewrite (Rpow_convert_Z x (Z.pos n)); easy]
    end).

Ltac from_pow :=
  repeat
    (match goal with |- context [pow ?x ?n] =>
      let nZ := constr:(Z.of_nat n) in
      let v := eval compute in nZ in
        replace (pow x n) with (Rpow x (IZR v));
         [ | rewrite (Rpow_convert_Z x v); easy]
    end).


Add Field RField_w_Rpow : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac],
    preprocess [to_pow],
    postprocess [from_pow], power_tac R_power_theory [Rpow_tac]).

Example test_ring n : Rpow (n + 1) 2 = 3 * n - n + 1 + Rpow n 2.
Proof.
ring_simplify.
easy.
Qed.

Example test_field n (np1n0 : Rpow n 2 + 2 * n + 1 <> 0): 1 / (Rpow n 2 + 2 * n + 1) =
Rpow ((n + 1) / Rpow (n + 1) 2) 2.
Proof.
field_simplify.
    easy.
  assert (it : Rpow n 2 + 2 * n + 1 = Rpow (n + 1) 2) by ring.
  rewrite it in np1n0; intros abs; case np1n0; rewrite abs; ring.
assumption.
Qed.

Example test_field2 n (np1n0 : n + 1 <> 0) : 1 / (1 + 2 * n + Rpow n 2) =
  Rpow ((n + 1) / Rpow (1 + n) 2) 2.
Proof.
assert (Rpown0: forall x k, x <> 0 -> Rpow x (IZR k) <> 0).
  intros x k; rewrite Rpow_convert_Z.
  now apply pow_nonzero.
assert (np12n0 : Rpow n 2 + 2 * n + 1 <> 0).
  replace (Rpow n 2 + 2 * n + 1) with (Rpow (n + 1) 2) by ring.
  now apply Rpown0.
assert (np14n0 : Rpow n 4 + 4 * Rpow n 3 + 6 * Rpow n 2 + 4 * n + 1 <> 0).
  replace (Rpow n 4 + 4 * Rpow n 3 + 6 * Rpow n 2 + 4 * n + 1) with
  (Rpow (n + 1) 4) by ring.
  now apply Rpown0.
field_simplify (1 + 2 * n + Rpow n 2).
field_simplify ((n + 1) / Rpow (1 + n) 2).
field_simplify.
field_simplify_eq.
easy.
all: auto.
replace (1 + n) with (n + 1) by ring; auto.
Qed.
