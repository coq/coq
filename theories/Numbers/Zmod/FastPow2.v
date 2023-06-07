Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Numbers.Zmod.Base.

(** Optimized conversions and operations for m=2^w *)

Local Open Scope Z_scope.
Local Open Scope Zmod_scope.
Import Zmod.Base.Coercions.

Definition of_N_pow2 (w : positive) (n : N) : Zmod (2^w).
Proof.
  refine (of_small_N _ (N.land n (Pos.ones w)) (fun _ => _)).
  abstract (rewrite N.pos_ones, N.land_ones; apply N.mod_upper_bound; discriminate).
Defined.

Lemma of_N_pow2_ok {w} n : of_N_pow2 w n = of_N (2^w) n.
Proof.
  cbv [of_N_pow2]. apply to_N_inj. rewrite of_small_N_ok, !to_N_of_N.
  rewrite N.pos_ones, N.land_ones, N.Div0.mod_mod; trivial; discriminate.
Qed.

Definition of_Z_pow2 (w : positive) (z : Z) : Zmod (2^w).
  refine (of_small_Z _ (Z.land z (Pos.ones w)) (fun _ => _)).
  abstract (rewrite Z.pos_ones, Z.land_ones; Z.div_mod_to_equations; lia).
Defined.

Lemma of_Z_pow2_ok {w} z : of_Z_pow2 w z = of_Z (2^w) z.
Proof.
  cbv [of_Z_pow2]. apply to_N_inj. rewrite of_small_Z_ok, !to_N_of_Z.
  rewrite Z.pos_ones, Z.land_ones, Pos2Z.inj_pow, Z.mod_mod; lia.
Qed.

Definition mul_pow2 {w} (x y : Zmod (2^w)) : Zmod (2^w) := of_N_pow2 w (x * y).

Lemma mul_pow2_ok {w} (x y : Zmod (2^w)) : mul_pow2 x y = mul x y.
Proof. apply of_N_pow2_ok. Qed.

Section Tests.
Import Coq.Numbers.Zmod.Base.Notations.
Goal True. unify (add (of_N_value 4 3 I) (of_Z_pow2 2 1)) (of_Z 4 0). Abort.
Goal True. pose (((of_N_value 4 3 I) - (of_Z_pow2 2 1) + of_Z _ 2)). cbv in z. Abort.
Add Ring ring_Zmod2 : (@ring_theory 2).
Add Ring ring_Zmod2p1 : (@ring_theory (2^1)).
Goal True. assert (one - one = zero :> Zmod 2) as _ by ring. Abort.
Goal True. assert (of_Z _ 1 - of_Z _ 1 = zero :> Zmod (2^1)) as _ by ring. Abort.

Goal pow_N (of_Z (2^127-1) 2) (2^127-3) =? inv (of_Z (2^127-1) 2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End Tests.
