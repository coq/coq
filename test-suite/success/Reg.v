Require Reals.

Axiom y : R->R.
Axiom d_y : (derivable y).
Axiom n_y : (x:R)``(y x)<>0``.
Axiom dy_0 : (derive_pt y R0 (d_y R0)) == R1.

Lemma essai0 : (continuity_pt [x:R]``(x+2)/(y x)+x/(y x)`` R0).
Assert H := d_y.
Assert H0 := n_y.
Reg().
Qed.

Lemma essai1 : (derivable_pt [x:R]``/2*(sin x)`` ``1``).
Reg ().
Qed.

Lemma essai2 : (continuity [x:R]``(Rsqr x)*(cos (x*x))+x``).
Reg ().
Qed.

Lemma essai3 : (derivable_pt [x:R]``x*((Rsqr x)+3)`` R0).
Reg ().
Qed.

Lemma essai4 : (derivable [x:R]``(x+x)*(sin x)``).
Reg ().
Qed.

Lemma essai5 : (derivable [x:R]``1+(sin (2*x+3))*(cos (cos x))``).
Reg ().
Qed.

Lemma essai6 : (derivable [x:R]``(cos (x+3))``).
Reg ().
Qed.

Lemma essai7 : (derivable_pt [x:R]``(cos (/(sqrt x)))*(Rsqr ((sin x)+1))`` R1).
Reg ().
Apply Rlt_R0_R1.
Red; Intro; Rewrite sqrt_1 in H; Assert H0 := R1_neq_R0; Elim H0; Assumption.
Qed.

Lemma essai8 : (derivable_pt [x:R]``(sqrt ((Rsqr x)+(sin x)+1))`` R0).
Reg ().
Rewrite sin_0.
Rewrite Rsqr_O.
Replace ``0+0+1`` with ``1``; [Apply Rlt_R0_R1 | Ring].
Qed.

Lemma essai9 : (derivable_pt (plus_fct id sin) R1).
Reg ().
Qed.

Lemma essai10 : (derivable_pt [x:R]``x+2`` R0).
Reg().
Qed.

Lemma essai11 : (derive_pt [x:R]``x+2`` R0 essai10)==R1.
Reg().
Qed.

Lemma essai12 : (derivable [x:R]``x+(Rsqr (x+2))``).
Reg().
Qed.

Lemma essai13 : (derive_pt [x:R]``x+(Rsqr (x+2))`` R0 (essai12 R0)) == ``5``.
Reg().
Qed.

Lemma essai14 : (derivable_pt [x:R]``2*x+x`` ``2``).
Reg ().
Qed.

Lemma essai15 : (derive_pt [x:R]``2*x+x`` ``2`` essai14) == ``3``.
Reg().
Qed.

Lemma essai16 : (derivable_pt [x:R]``x+(sin x)`` R0).
Reg().
Qed.

Lemma essai17 : (derive_pt [x:R]``x+(sin x)`` R0 essai16)==``2``.
Reg ().
Rewrite cos_0.
Reflexivity.
Qed.

Lemma essai18 : (derivable_pt [x:R]``x+(y x)`` ``0``).
Assert H := d_y.
Reg ().
Qed.

Lemma essai19 : (derive_pt [x:R]``x+(y x)`` ``0`` essai18) == ``2``.
Assert H := dy_0.
Assert H0 := d_y.
Reg ().
Qed.

Axiom z:R->R.
Axiom d_z: (derivable z).

Lemma essai20 : (derivable_pt [x:R]``(z (y x))`` R0).
Reg ().
Apply d_y.
Apply d_z.
Qed.

Lemma essai21 : (derive_pt [x:R]``(z (y x))`` R0 essai20) == R1.
Assert H := dy_0.
Reg().
Abort.

Lemma essai22 : (derivable [x:R]``(sin (z x))+(Rsqr (z x))/(y x)``).
Assert H := d_y.
Reg().
Apply n_y.
Apply d_z.
Qed.