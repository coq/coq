Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Lemma two_x_eq_1 : forall x, 2 * x = 1 -> False.
Proof.
  intros.
  lia.
Qed.


Lemma two_x_y_eq_1 : forall x y, 2 * x + 2 * y = 1 -> False.
Proof.
  intros. 
  lia.
Qed.

Lemma two_x_y_z_eq_1 : forall x y z, 2 * x + 2 * y + 2 * z= 1 -> False.
Proof.
  intros.
  lia.
Qed.

Lemma unused : forall x y, y >= 0 /\ x = 1 -> x = 1.
Proof.
  intros x y.
  lia.
Qed.

Lemma omega_nightmare : forall x y, 27 <= 11 * x + 13 * y <= 45 ->  -10 <= 7 * x - 9 * y <= 4 -> False.
Proof.
  intros ; intuition auto.
  lia.
Qed.

Lemma compact_proof : forall z,
 (z < 0) ->
 (z >= 0) ->
  (0 >= z \/ 0 < z) -> False.
Proof.
 intros.
 lia.
Qed.

Lemma dummy_ex : exists (x:Z),  x = x.
Proof.
  eexists.
  lia.
  Unshelve.
  exact Z0.
Qed.

Lemma unused_concl : forall x,
    False -> x > 0 -> x < 0.
Proof.
  intro.
  lia.
Qed.

Lemma unused_concl_match : forall (x:Z),
    False -> match x with
             | Z0 => True
             | _ => x = x
             end.
Proof.
  intros.
  lia.
Qed.

Lemma fresh : forall (__arith : Prop),
    __arith -> True.
Proof.
  intros.
  lia.
Qed.

Class Foo {x : Z} := { T : Type ; dec : T -> Z }.
Goal forall bound {F : @Foo bound} (x y : T), 0 <= dec x < bound -> 0 <= dec y 
< bound -> dec x + dec y >= bound -> dec x + dec y < 2 * bound.
Proof.
  intros.
  lia.
Qed.

Section S.
  Variables x y: Z.
  Variables XGe : x >= 0.
  Variables YGt : y > 0.
  Variables YLt : y < 0.

  Goal False.
  Proof using - XGe.
    lia.
  Qed.

  Goal False.
  Proof using YGt YLt x y.
    lia.
  Qed.

  End S.

(*  Bug 5073 *)
Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
Proof.
  lia.
Qed.

Lemma ex_pos : forall x, exists z t, x = z - t /\ z >= 0 /\ t >= 0.
Proof.
  intros.
  destruct (dec_Zge x 0).
  exists x, 0.
  lia.
  exists 0, (-x).
  lia.
Qed.

Goal forall
    (b q r : Z)
    (H : b * q + r <= 0)
    (H5 : - b < r)
    (H6 : r <= 0)
    (H2 : 0 <= b),
  b = 0 -> False.
Proof.
  intros b q r.
  lia.
Qed.
