Require Import Reals.

Axiom y : R -> R.
Axiom d_y : derivable y.
Axiom n_y : forall x : R, y x <> 0%R.
Axiom dy_0 : derive_pt y 0 (d_y 0%R) = 1%R.

Lemma essai0 : continuity_pt (fun x : R => ((x + 2) / y x + x / y x)%R) 0.
assert (H := d_y).
assert (H0 := n_y).
reg.
Qed.

Lemma essai1 : derivable_pt (fun x : R => (/ 2 * sin x)%R) 1.
reg.
Qed.

Lemma essai2 : continuity (fun x : R => (Rsqr x * cos (x * x) + x)%R).
reg.
Qed.

Lemma essai3 : derivable_pt (fun x : R => (x * (Rsqr x + 3))%R) 0.
reg.
Qed.

Lemma essai4 : derivable (fun x : R => ((x + x) * sin x)%R).
reg.
Qed.

Lemma essai5 : derivable (fun x : R => (1 + sin (2 * x + 3) * cos (cos x))%R).
reg.
Qed.

Lemma essai6 : derivable (fun x : R => cos (x + 3)).
reg.
Qed.

Lemma essai7 :
 derivable_pt (fun x : R => (cos (/ sqrt x) * Rsqr (sin x + 1))%R) 1.
reg.
apply Rlt_0_1.
red; intro;  rewrite sqrt_1 in H; assert (H0 := R1_neq_R0); elim H0;
 assumption.
Qed.

Lemma essai8 : derivable_pt (fun x : R => sqrt (Rsqr x + sin x + 1)) 0.
reg.
 rewrite sin_0.
 rewrite Rsqr_0.
 replace (0 + 0 + 1)%R with 1%R; [ apply Rlt_0_1 |  ring ].
Qed.

Lemma essai9 : derivable_pt (id + sin) 1.
reg.
Qed.

Lemma essai10 : derivable_pt (fun x : R => (x + 2)%R) 0.
reg.
Qed.

Lemma essai11 : derive_pt (fun x : R => (x + 2)%R) 0 essai10 = 1%R.
reg.
Qed.

Lemma essai12 : derivable (fun x : R => (x + Rsqr (x + 2))%R).
reg.
Qed.

Lemma essai13 :
 derive_pt (fun x : R => (x + Rsqr (x + 2))%R) 0 (essai12 0%R) = 5%R.
reg.
Qed.

Lemma essai14 : derivable_pt (fun x : R => (2 * x + x)%R) 2.
reg.
Qed.

Lemma essai15 : derive_pt (fun x : R => (2 * x + x)%R) 2 essai14 = 3%R.
reg.
Qed.

Lemma essai16 : derivable_pt (fun x : R => (x + sin x)%R) 0.
reg.
Qed.

Lemma essai17 : derive_pt (fun x : R => (x + sin x)%R) 0 essai16 = 2%R.
reg.
 rewrite cos_0.
reflexivity.
Qed.

Lemma essai18 : derivable_pt (fun x : R => (x + y x)%R) 0.
assert (H := d_y).
reg.
Qed.

Lemma essai19 : derive_pt (fun x : R => (x + y x)%R) 0 essai18 = 2%R.
assert (H := dy_0).
assert (H0 := d_y).
reg.
Qed.

Axiom z : R -> R.
Axiom d_z : derivable z.

Lemma essai20 : derivable_pt (fun x : R => z (y x)) 0.
reg.
apply d_y.
apply d_z.
Qed.

Lemma essai21 : derive_pt (fun x : R => z (y x)) 0 essai20 = 1%R.
assert (H := dy_0).
reg.
Abort.

Lemma essai22 : derivable (fun x : R => (sin (z x) + Rsqr (z x) / y x)%R).
assert (H := d_y).
reg.
apply n_y.
apply d_z.
Qed.

(* Pour tester la continuite de sqrt en 0 *)
Lemma essai23 :
 continuity_pt
   (fun x : R => (sin (sqrt (x - 1)) + exp (Rsqr (sqrt x + 3)))%R) 1.
reg.
left; apply Rlt_0_1.
right; unfold Rminus;  rewrite Rplus_opp_r; reflexivity.
Qed.

Lemma essai24 :
 derivable (fun x : R => (sqrt (x * x + 2 * x + 2) + Rabs (x * x + 1))%R).
reg.
 replace (x * x + 2 * x + 2)%R with (Rsqr (x + 1) + 1)%R.
apply Rplus_le_lt_0_compat; [ apply Rle_0_sqr | apply Rlt_0_1 ].
unfold Rsqr;  ring.
red; intro; cut (0 < x * x + 1)%R.
intro;  rewrite H in H0; elim (Rlt_irrefl _ H0).
apply Rplus_le_lt_0_compat;
 [  replace (x * x)%R with (Rsqr x); [ apply Rle_0_sqr | reflexivity ]
 | apply Rlt_0_1 ].
Qed.
