Require Import ZArith_base.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Fixpoint fib (n: nat) : Z :=
  match n with
  | O => 1
  | S O => 1
  | S (S n as p) => fib p + fib n
  end.

Axiom fib_47_computed: fib 47 = 2971215073.

Lemma fib_bound:
  fib 47 < 2 ^ 32.
Proof.
  pose proof fib_47_computed.
  lia.
Qed.

Require Import Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Fixpoint fibr (n: nat) : R :=
  match n with
  | O => 1
  | S O => 1
  | S (S n as p) => fibr p + fibr n
  end.

Axiom fibr_47_computed: fibr 47 = 2971215073.

Lemma fibr_bound:
  fibr 47 < 2 ^ 32.
Proof.
  pose proof fibr_47_computed.
  lra.
Qed.

Lemma fibr_bound':
  fibr 47 < IZR (Z.pow_pos 2  32).
Proof.
  pose proof fibr_47_computed.
  lra.
Qed.
