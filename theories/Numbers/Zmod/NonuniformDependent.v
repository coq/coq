Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Numbers.Zmod.Base.

Local Open Scope Z_scope.
Import Zmod.Base.Coercions.

(** Operations that change the modulus *)

(* This module provides operations that vary m in [Zmod m], for example
 * concatenating bitvectors and combining congruences. *)

(* Effective use of the operations defined here with moduli that are not
   converitble to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus.
   The next few lemmas will give a taste of the challenges. *)

Goal forall {m} (a : Zmod m) {n} (b : Zmod n), Prop.
  intros.
  assert_fails (assert (a = b)). (* type error: need n == m *)
  assert_fails (pose (add a b)). (* type error: need n == m *)
Abort.

Lemma to_N_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_N a = to_N b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_N_inj. Qed.

Lemma to_N_eq_rect {m} (a : Zmod m) n p : to_N (eq_rect _ _ a n p) = to_N a.
Proof. case p; trivial. Qed.

Lemma to_N_eq_rect_attempt {m} (a : Zmod m) n p : to_N (eq_rect (Zmod m) id a (Zmod n) p) = to_N a.
Proof. assert_fails (case p). Abort.

Lemma to_Z_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.

Lemma to_Z_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.

(** Conversions to Fin.t *)

(* Please consider using [to_nat] or [to_N] instead. *)
Definition to_Fin {m} (a : Zmod m) : Fin.t (Pos.to_nat m) :=
  @Fin.of_nat_lt (to_nat a) (Pos.to_nat m) (to_nat_range a).

(* Please consider using [of_nat] or [of_N] instead. *)
Definition of_Fin {n} (f : Fin.t n) : Zmod (Pos.of_nat n).
  refine (of_small_N _ (N.of_nat (FinFun.Fin2Restrict.f2n f)) (fun _ => _)).
  abstract (pose proof FinFun.Fin2Restrict.f2n_ok f; lia).
Defined.

Lemma to_nat_of_Fin {n} f : to_nat (@of_Fin n f) = FinFun.Fin2Restrict.f2n f.
Proof. cbv [to_nat of_Fin]. rewrite to_N_of_small_N; lia. Qed.

Lemma to_N_of_Fin {n} f : to_N (@of_Fin n f) = N.of_nat (FinFun.Fin2Restrict.f2n f).
Proof. cbv [of_Fin]. rewrite to_N_of_small_N; lia. Qed.

Lemma to_Z_of_Fin {n} f : to_Z (@of_Fin n f) = N.of_nat (FinFun.Fin2Restrict.f2n f).
Proof. cbv [of_Fin]. rewrite to_Z_of_small_N; lia. Qed.

Lemma of_Fin_to_Fin_dep {m} a :
  existT Zmod _ (of_Fin (@to_Fin m a)) = existT Zmod _ a.
Proof.
  apply to_Z_inj_dep; [lia|]; cbv [to_Fin].
  rewrite to_Z_of_Fin, FinFun.Fin2Restrict.f2n_n2f, to_N_to_nat; trivial.
Qed.

Lemma to_fin_of_Fin_dep {n} f :
  existT Fin.t _ (to_Fin (@of_Fin n f)) = existT Fin.t _ f.
Proof.
  destruct n; [apply Fin.case0; assumption|].
  apply Fin.f2n_inj_dep; [lia|]; cbv [to_Fin].
  rewrite FinFun.Fin2Restrict.f2n_n2f, to_nat_of_Fin; trivial.
Qed.

(* TODO: high part first or low part first? *)
Definition undivmodM {a b} (hi : Zmod a) (lo : Zmod b) : Zmod (a * b).
  refine (of_small_N _ (N.undivmod b hi lo) (fun _ => _))%N.
  abstract (cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma undivmodM_ok {a b} hi lo : @undivmodM a b hi lo = of_N _ (N.undivmod b hi lo).
Proof. apply of_small_N_ok. Qed.

Lemma to_N_undivmodM {a b} hi lo : to_N (@undivmodM a b hi lo) = N.undivmod b hi lo.
Proof. apply to_N_of_small_N. Qed.

Lemma to_Z_undivmodM {a b} hi lo : to_Z (@undivmodM a b hi lo) = b*hi + lo.
Proof. cbv [to_Z]. rewrite to_N_undivmodM. cbv [N.undivmod]. lia. Qed.

Definition divM a b (x : Zmod (a * b)) : Zmod a.
  refine (of_small_N _ (x / b) (fun _ => _))%N.
  abstract (pose proof to_N_range x; zify; Z.div_mod_to_equations; nia).
Defined.

Lemma divM_ok {a b} x : @divM a b x = of_N _ (x / b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_divM {a b} x : to_N (@divM a b x) = (x / b)%N.
Proof. apply to_N_of_small_N. Qed.

Lemma divM_undivmodM {a b} x y : divM a b (undivmodM x y) = x.
Proof.
  apply to_N_inj. rewrite to_N_divM, to_N_undivmodM, N.div_undivmod;
    auto using to_N_range.
Qed.

Definition modM a b (x : Zmod (a * b)) := of_N b x.

Lemma modM_ok {a b} x : @modM a b x = of_N _ (x mod b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_modM {a b} x : to_N (@modM a b x) = (x mod b)%N.
Proof. apply to_N_of_N. Qed.

Lemma to_Z_modM {a b} x : to_Z (@modM a b x) = x mod b.
Proof. apply to_Z_of_N. Qed.

Lemma modM_undivmodM {a b} x y : modM a b (undivmodM x y) = y.
Proof.
  apply to_N_inj. rewrite to_N_modM, to_N_undivmodM, N.mod_undivmod;
    auto using to_N_range.
Qed.

Definition crtM {a b} (x : Zmod a) (y : Zmod b) := of_Z (a*b) (Znumtheory.solvecong a b x y).

Lemma to_Z_crtM {a b} (x : Zmod a) (y : Zmod b) :
 to_Z (crtM x y) = Znumtheory.solvecong a b x y mod (a*b).
Proof. apply to_Z_of_Z. Qed.

Lemma modM_crtM {a b : positive} x y (H : Z.gcd a b = 1) : modM a b (crtM x y) = y.
Proof.
  apply to_Z_inj; cbv [crtM modM].
  rewrite to_N_of_Z, to_Z_of_N, Z2N.id, <-Znumtheory.Zmod_div_mod; try lia.
  { rewrite (proj2 (Znumtheory.solvecong_coprime a b x y H)), mod_to_Z; trivial. }
  { exists a. lia. }
  { apply Z.mod_pos_bound. lia. }
Qed.

Lemma crtM_comm {a b} (x : Zmod a) (y : Zmod b) (H : Z.gcd a b = 1) :
  existT Zmod _ (crtM x y) = existT Zmod _ (crtM y x).
Proof.
  apply to_Z_inj_dep; try lia; cbv [crtM]; rewrite !to_Z_of_Z.
  rewrite Znumtheory.solvecong_comm; f_equal; try lia.
Qed.

Lemma crtM_inj {a b} (x x' : Zmod a) (y y' : Zmod b) (H : Z.gcd a b = 1) :
  existT Zmod _ (crtM x y) = existT Zmod _ (crtM x' y') -> x = x' /\ y = y'.
Proof.
  intros Hx; pose proof Hx as Hy.
  rewrite (crtM_comm x), (crtM_comm x') in Hy by trivial.
  inversion_sigma; erewrite <-Eqdep_dec.eq_rect_eq_dec in * by apply Pos.eq_dec.
  eapply (f_equal (modM _ _)) in Hx2, Hy2.
  rewrite !modM_crtM in * by (trivial || rewrite Z.gcd_comm; trivial). auto.
Qed.

Import Coq.Lists.List Coq.Sorting.Permutation.
Lemma elements_as_crtM {a b : positive} (H : Z.gcd a b = 1) :
  Permutation
    (elements (a*b))
    (map (uncurry crtM) (list_prod (elements a) (elements b))).
Proof.
  eapply NoDup_Permutation.
  { apply NoDup_elements. }
  { apply FinFun.Injective_map_NoDup; auto using NoDup_elements, List.NoDup_list_prod.
    intros [] [] ?; epose proof crtM_inj z z1 z0 z2 H ltac:(f_equal; auto).
    intuition auto using f_equal2. }
  split; trivial using in_elements; intros _; cbv [uncurry].
  eapply in_map_iff, ex_intro, conj; auto using in_prod, in_elements; cbn.
  (* NOTE: might be nice to factor out: [crtM ?y ?z = x] *)
  instantiate (1:= modM _ b x).
  instantiate (1:=modM _ a (eq_rect _ _ x _ (Pos.mul_comm _ _))).
  apply to_Z_inj. rewrite to_Z_crtM, 2 to_Z_modM, to_Z_eq_rect.
  symmetry; rewrite <-mod_to_Z at 1. rewrite !Pos2Z.inj_mul.
  eapply Znumtheory.chinese_remainder_solvecong; rewrite ?Zmod_mod; lia.
Qed.

Definition concatM {a b} (hi : Zmod (2^a)) (lo : Zmod (2^b)) : Zmod (2^(a+b)).
  refine (of_small_N _ (N.lor (N.shiftl hi b) lo) (fun _ => _))%N.
  abstract (
    rewrite <-N.undivmod_pow2, Pos.pow_add_r by auto using to_N_range;
    cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma concatM_ok {a b} hi lo : to_N (@concatM a b hi lo) = to_N (undivmodM hi lo).
Proof.
  cbv [concatM]; rewrite to_N_of_small_N, to_N_undivmodM.
  rewrite <-N.undivmod_pow2 by auto using to_N_range; trivial.
Qed.

Lemma concatM_ok_dep {a b} hi lo : existT _ _ (@concatM a b hi lo) = existT _ _ (undivmodM hi lo).
Proof. apply to_N_inj_dep; auto using concatM_ok, Pos.pow_add_r. Qed.
