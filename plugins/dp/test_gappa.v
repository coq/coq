Require Export Gappa_tactic.
Require Export Reals.

Open Scope Z_scope.
Open Scope R_scope.

Lemma test_base10 : 
  forall x y:R,
  0 <= x <= 4 -> 
  0 <= x * (24 * powerRZ 10 (-1)) <= 10.
Proof.
  gappa.
Qed.

(*
@rnd = float< ieee_32, zr >;
a = rnd(a_); b = rnd(b_);
{ a in [3.2,3.3] /\ b in [1.4,1.9] ->
  rnd(a - b) - (a - b) in [0,0] }
*)

Definition rnd := gappa_rounding (rounding_float roundZR 43 (120)).

Lemma test_float3 :
  forall a_ b_ a b : R,
  a = rnd a_ ->
  b = rnd b_ ->
  52 / 16 <= a <= 53 / 16 ->
  22 / 16 <= b <= 30 / 16 ->
  0 <= rnd (a - b) - (a - b) <= 0.
Proof.
  unfold rnd.
  gappa.
Qed.

Lemma test_float2 :
  forall x y:R,
  0 <= x <= 1 ->
  0 <= y <= 1 ->
  0 <= gappa_rounding (rounding_float roundNE 53 (1074)) (x+y) <= 2. 
Proof.
  gappa.
Qed.

Lemma test_float1 :
  forall x y:R,
  0 <= gappa_rounding (rounding_fixed roundDN (0)) x -
           gappa_rounding (rounding_fixed roundDN (0)) y <= 0 ->
  Rabs (x - y) <= 1.
Proof.
  gappa.
Qed.

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
  3/4 <= x <= 3 -> 
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
Qed.


