From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Section S.
  Variables H1 H2 H3 H4 : True.

  Lemma bug_9848 : True.
  Proof using.
    lia.
  Qed.
End S.

Lemma concl_in_Type : forall   (k : nat)
             (H : (k < 0)%nat) (F : k < 0 -> Type),
    F H.
Proof.
  intros.
  lia.
Qed.

Lemma bug_10707 : forall
    (T : Type)
    (t : nat -> Type)
    (k : nat)
    (default : T)
    (arr : t 0 -> T)
    (H : (k < 0)%nat) of_nat_lt,
 match k with
 | 0 | _ => default
 end = arr (of_nat_lt H).
Proof.
  intros.
  lia.
Qed.

Axiom decompose_nat : nat -> nat -> nat.
Axiom inleft : forall {P}, {m : nat & P m} -> nat.
Axiom foo : nat.

Lemma bug_7886 : forall (x x0 : nat)
                        (e : 0 = x0 + S x)
                        (H : decompose_nat x 0 = inleft (existT (fun m : nat => 0 = m + S x) x0 e))
                        (x1 : nat)
                        (e0 : 0 = x1 + S (S x))
                        (H1 : decompose_nat (S x) 0 = inleft (existT (fun m : nat => 0 = m + S (S x)) x1 e0)),
    False.
Proof.
  intros.
  lia.
Qed.


Lemma bug_8898 : forall (p : 0 < 0) (H: p = p), False.
Proof.
  intros p H.
  lia.
Qed.



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


Lemma fresh1 : forall (__p1 __p2 __p3 __p5:Prop) (x y z:Z), (x = 0 /\ y = 0) /\ z = 0 -> x = 0.
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

Section S.
  Variable x y: Z.
  Variable H1 : 1 > 0 -> x = 1.
  Variable H2 : x = y.

  Goal x = y.
  Proof using H2.
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


Section S.
  (* From bedrock2, used to be slow *)
  Variables (x3 q r q2 r3 : Z)
            (H : 2 ^ 2 <> 0 -> r3 + 3 = 2 ^ 2 * q + r)
            (H0 : 0 < 2 ^ 2 -> 0 <= r < 2 ^ 2)
            (H1 : 2 ^ 2 < 0 -> 2 ^ 2 < r <= 0)
            (H2 : 2 ^ 2 = 0 -> q = 0)
            (H3 : 2 ^ 2 = 0 -> r = 0)
            (q0 r0 : Z)
            (H4 : 4 <> 0 -> 0 = 4 * q0 + r0)
            (H5 : 0 < 4 -> 0 <= r0 < 4)
            (H6 : 4 < 0 -> 4 < r0 <= 0)
            (H7 : 4 = 0 -> q0 = 0)
            (H8 : 4 = 0 -> r0 = 0)
            (q1 r1 : Z)
            (H9 : 4 <> 0 -> q + q + (q + q) = 4 * q1 + r1)
            (H10 : 0 < 4 -> 0 <= r1 < 4)
            (H11 : 4 < 0 -> 4 < r1 <= 0)
            (H12 : 4 = 0 -> q1 = 0)
            (H13 : 4 = 0 -> r1 = 0)
            (r2 : Z)
            (H14 : 2 ^ 16 <> 0 ->  x3 = 2 ^ 16 * q2 + r2)
            (H15 : 0 < 2 ^ 16 -> 0 <= r2 < 2 ^ 16)
            (H16 : 2 ^ 16 < 0 -> 2 ^ 16 < r2 <= 0)
            (H17 : 2 ^ 16 = 0 -> q2 = 0)
            (H18 : 2 ^ 16 = 0 -> r2 = 0)
            (q3 : Z)
            (H19 : 16383 + 1 <> 0 -> q2 = (16383 + 1) * q3 + r3)
            (H20 : 0 < 16383 + 1 -> 0 <= r3 < 16383 + 1)
            (H21 : 16383 + 1 < 0 -> 16383 + 1 < r3 <= 0)
            (H22 : 16383 + 1 = 0 -> q3 = 0)
            (H23 : 16383 + 1 = 0 -> r3 = 0).

  Goal r0 = r1.
  Proof using H10 H9 H5 H4.
    intros.
    lia.
  Qed.

End S.
