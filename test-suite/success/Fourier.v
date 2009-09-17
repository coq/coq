Require Import Rfunctions.
Require Import Fourier.

Lemma l1 : forall x y z : R, Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
intros; split_Rabs; fourier.
Qed.

Lemma l2 :
 forall x y : R, x < Rabs y -> y < 1 -> x >= 0 -> - y <= 1 -> Rabs x <= 1.
intros.
split_Rabs; fourier.
Qed.
