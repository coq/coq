Require Import ZArith Lia.
Open Scope Z_scope.

(* Pierre L: examples gathered while debugging rlia. *)

Lemma test_rlia_0 :
 forall m m',
  0<= m <= 1 -> 0<= m' <= 1 -> (0 < m <-> 0 < m') -> m = m'.
Proof.
intros.
lia.
Qed.

Lemma test_rlia_0b :
 forall m m',
  0<= m <= 1 -> 0<= m' <= 1 -> (0 < m <-> 0 < m') -> m = m'.
Proof.
intros m m'.
lia.
Qed.

Lemma test_rlia_1 :
 forall (z z1 z2 : Z),
    z2 <= z1 ->
    z1 <= z2 ->
    z1 >= 0 ->
    z2 >= 0 ->
    z1 >= z2 /\ z = z1 \/ z1 <= z2 /\ z = z2 ->
    z >= 0.
Proof.
intros.
lia.
Qed.

Lemma test_rlia_1b :
 forall (z z1 z2 : Z),
    z2 <= z1 ->
    z1 <= z2 ->
    z1 >= 0 ->
    z2 >= 0 ->
    z1 >= z2 /\ z = z1 \/ z1 <= z2 /\ z = z2 ->
    z >= 0.
Proof.
intros z z1 z2.
lia.
Qed.

Lemma test_rlia_2 : forall a b c:Z,
 0<=a-b<=1 -> b-c<=2 -> a-c<=3.
Proof.
intros.
lia.
Qed.

Lemma test_rlia_2b : forall a b c:Z,
 0<=a-b<=1 -> b-c<=2 -> a-c<=3.
Proof.
intros a b c.
lia.
Qed.

Lemma test_rlia_3 : forall a b h hl hr ha hb,
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
lia.
Qed.

Lemma test_rlia_3b : forall a b h hl hr ha hb,
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
lia.
Qed.


Lemma test_rlia_4 : forall hr ha,
 ha = 0 ->
 (ha = 0 -> hr =0) ->
 hr = 0.
Proof.
intros hr ha.
lia.
Qed.

Lemma test_rlia_5 : forall hr ha,
 ha = 0 ->
 (~ha = 0 \/ hr =0) ->
 hr = 0.
Proof.
intros hr ha.
lia.
Qed.

Lemma test_rlia_6 : forall z, z>=0 -> 0>z+2 -> False.
Proof.
intros.
lia.
Qed.

Lemma test_rlia_6b : forall z, z>=0 -> 0>z+2 -> False.
Proof.
intros z.
lia.
Qed.

Lemma test_rlia_7 : forall z,
  0>=0 /\ z=0 \/ 0<=0 /\ z =0 -> 1 = z+1.
Proof.
intros.
lia.
Qed.

Lemma test_rlia_7b : forall z,
  0>=0 /\ z=0 \/ 0<=0 /\ z =0 -> 1 = z+1.
Proof.
intros.
lia.
Qed.

(* Magaud BZ#240 *)

Lemma test_rlia_8 : forall x y:Z, x*x<y*y-> ~ y*y <= x*x.
intros.
lia.
Qed.

Lemma test_rlia_8b : forall x y:Z, x*x<y*y-> ~ y*y <= x*x.
intros x y.
lia.
Qed.




