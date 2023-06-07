Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Numbers.Zmod.Base.
Require Import Coq.Numbers.Zmod.Inverse.
Require Import Coq.Numbers.Zmod.FastPow2.
Require Import Coq.Numbers.Zmod.NonuniformDependent.
Require Import Coq.Numbers.Zstar.Fermat.

Include Zmod.Base.
Include Zmod.Inverse.
Include Zmod.FastPow2.
Include Zmod.NonuniformDependent.
Include Zstar.Fermat.Zmod.

Local Open Scope Z_scope.
Import Base.Zmod Inverse.Zmod.

(* TODO: should we keep these? where? *)
Lemma prod_Permutation {m} (xs ys : list (Zmod m)) (H : Permutation.Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); congruence. Qed.

Lemma prod_map_mul {m} (a : Zmod m) xs :
  List.fold_right mul one (List.map (mul a) xs) =
  mul (pow_N a (N.of_nat (length xs))) (List.fold_right mul one xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length];
    rewrite ?pow_N_0_r, ?mul_1_r, ?Nat2N.inj_succ, ?pow_N_succ_r, ?IHxs; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
Qed.
