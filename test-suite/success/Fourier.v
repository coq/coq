Require Rfunctions.
Require Fourier.
 
Lemma l1:
 (x, y, z : R)
  ``(Rabsolu x-z) <= (Rabsolu x-y)+(Rabsolu y-z)``.
Intros; SplitAbsolu; Fourier.
Qed.
 
Lemma l2:
 (x, y : R)
 ``x < (Rabsolu y)`` ->
 ``y < 1`` -> ``x >= 0`` -> ``-y <= 1`` ->  ``(Rabsolu x) <= 1``.
Intros.
SplitAbsolu; Fourier.
Qed.
