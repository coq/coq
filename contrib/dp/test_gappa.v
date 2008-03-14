Require Export Gappa.
Require Export Gappa_library.
Require Export Reals.

Open Scope Z_scope.
Open Scope R_scope.

Ltac gappa := gappa_prepare; gappa_internal.

Lemma test1 : 
  forall x y:R,
  0 <= x <= 1 -> 
  0 <= -y <= 1 ->  
  0 <= x  * (-y) <= 1.
Proof.
  gappa.
Qed.

Lemma test2 : 
  forall x y:R,
  0 <= x <= 3 -> 
  0 <= sqrt x <= 1775 * (powerRZ 2 (-10)).
Proof.
  gappa.
Qed.

Lemma test3 : 
  forall x y z:R,
  0 <= x - y <= 3 -> 
  -2 <= y - z <= 4 ->
  -2 <= x - z <= 7.
Proof.
  gappa.
Qed.

Lemma test4 : 
  forall x1 x2 y1 y2 : R,
  1 <= Rabs y1 <= 1000 ->
  1 <= Rabs y2 <= 1000 ->
  - powerRZ 2 (-53) <= (x1 - y1) / y1 <= powerRZ 2 (-53) ->
  - powerRZ 2 (-53) <= (x2 - y2) / y2 <= powerRZ 2 (-53) ->
  - powerRZ 2 (-51) <= (x1 * x2 - y1 * y2) / (y1 * y2) <= powerRZ 2 (-51).
Proof.
  gappa.


