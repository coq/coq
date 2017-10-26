Require Import ZArith Omega.
Open Scope Z_scope.

(* Pierre L: examples gathered while debugging romega. *)

Lemma test_romega_0 :
 forall m m',
  0<= m <= 1 -> 0<= m' <= 1 -> (0 < m <-> 0 < m') -> m = m'.
Proof.
intros.
omega.
Qed.

Lemma test_romega_0b :
 forall m m',
  0<= m <= 1 -> 0<= m' <= 1 -> (0 < m <-> 0 < m') -> m = m'.
Proof.
intros m m'.
omega.
Qed.

Lemma test_romega_1 :
 forall (z z1 z2 : Z),
    z2 <= z1 ->
    z1 <= z2 ->
    z1 >= 0 ->
    z2 >= 0 ->
    z1 >= z2 /\ z = z1 \/ z1 <= z2 /\ z = z2 ->
    z >= 0.
Proof.
intros.
omega.
Qed.

Lemma test_romega_1b :
 forall (z z1 z2 : Z),
    z2 <= z1 ->
    z1 <= z2 ->
    z1 >= 0 ->
    z2 >= 0 ->
    z1 >= z2 /\ z = z1 \/ z1 <= z2 /\ z = z2 ->
    z >= 0.
Proof.
intros z z1 z2.
omega.
Qed.

Lemma test_romega_2 : forall a b c:Z,
 0<=a-b<=1 -> b-c<=2 -> a-c<=3.
Proof.
intros.
omega.
Qed.

Lemma test_romega_2b : forall a b c:Z,
 0<=a-b<=1 -> b-c<=2 -> a-c<=3.
Proof.
intros a b c.
omega.
Qed.

Lemma test_romega_3 : forall a b h hl hr ha hb,
 0 <= ha - hl <= 1 ->
 -2 <= hl - hr <= 2 ->
 h =b+1 ->
 (ha >= hr /\ a = ha \/ ha <= hr /\ a = hr) ->
 (hl >= hr /\ b = hl \/ hl <= hr /\ b = hr) ->
 (-3 <= ha -hr <=3 -> 0 <= hb - a <= 1) ->
 (-2 <= ha-hr <=2 -> hb = a  + 1) ->
 0 <= hb - h <= 1.
Proof.
intros.
omega.
Qed.

Lemma test_romega_3b : forall a b h hl hr ha hb,
 0 <= ha - hl <= 1 ->
 -2 <= hl - hr <= 2 ->
 h =b+1 ->
 (ha >= hr /\ a = ha \/ ha <= hr /\ a = hr) ->
 (hl >= hr /\ b = hl \/ hl <= hr /\ b = hr) ->
 (-3 <= ha -hr <=3 -> 0 <= hb - a <= 1) ->
 (-2 <= ha-hr <=2 -> hb = a  + 1) ->
 0 <= hb - h <= 1.
Proof.
intros a b h hl hr ha hb.
omega.
Qed.


Lemma test_romega_4 : forall hr ha,
 ha = 0 ->
 (ha = 0 -> hr =0) ->
 hr = 0.
Proof.
intros hr ha.
omega.
Qed.

Lemma test_romega_5 : forall hr ha,
 ha = 0 ->
 (~ha = 0 \/ hr =0) ->
 hr = 0.
Proof.
intros hr ha.
omega.
Qed.

Lemma test_romega_6 : forall z, z>=0 -> 0>z+2 -> False.
Proof.
intros.
omega.
Qed.

Lemma test_romega_6b : forall z, z>=0 -> 0>z+2 -> False.
Proof.
intros z.
omega.
Qed.

Lemma test_romega_7 : forall z,
  0>=0 /\ z=0 \/ 0<=0 /\ z =0 -> 1 = z+1.
Proof.
intros.
omega.
Qed.

Lemma test_romega_7b : forall z,
  0>=0 /\ z=0 \/ 0<=0 /\ z =0 -> 1 = z+1.
Proof.
intros.
omega.
Qed.

(* Magaud BZ#240 *)

Lemma test_romega_8 : forall x y:Z, x*x<y*y-> ~ y*y <= x*x.
intros.
omega.
Qed.

Lemma test_romega_8b : forall x y:Z, x*x<y*y-> ~ y*y <= x*x.
intros x y.
omega.
Qed.




