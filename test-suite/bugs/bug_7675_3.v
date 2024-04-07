Require Import Setoid CMorphisms.

Parameter A : Type.
Parameter R : A -> A -> Type.

Definition B := Type.

Definition Ri := fun x y => x -> y.
Definition Ra := arrow.
Definition Rb := Basics.arrow.
Definition RBi : B -> B -> Type := fun x y => x -> y.
Definition RBa : B -> B -> Type := arrow.
Definition RBb : B -> B -> Type := Basics.arrow.
Definition RTi : Type -> Type -> Type := fun x y => x -> y.
Definition RTa : Type -> Type -> Type := arrow.
Definition RTb : Type -> Type -> Type := Basics.arrow.
Definition RRBi : crelation B := fun x y => x -> y.
Definition RRBa : crelation B := arrow.
Definition RRBb : crelation B := Basics.arrow.
Definition RRTi : crelation Type := fun x y => x -> y.
Definition RRTa : crelation Type := arrow.
Definition RRTb : crelation Type := Basics.arrow.

Parameter f: A -> B.
#[local] Instance f_Ri: Proper (R ==> Ri) f. Admitted.
#[local] Instance f_Ra: Proper (R ==> Ra) f. Admitted.
#[local] Instance f_Rb: Proper (R ==> Rb) f. Admitted.
#[local] Instance f_RBi: Proper (R ==> RBi) f. Admitted.
#[local] Instance f_RBa: Proper (R ==> RBa) f. Admitted.
#[local] Instance f_RBb: Proper (R ==> RBb) f. Admitted.
#[local] Instance f_RTi: Proper (R ==> RTi) f. Admitted.
#[local] Instance f_RTa: Proper (R ==> RTa) f. Admitted.
#[local] Instance f_RTb: Proper (R ==> RTb) f. Admitted.
#[local] Instance f_RRBi: Proper (R ==> RRBi) f. Admitted.
#[local] Instance f_RRBa: Proper (R ==> RRBa) f. Admitted.
#[local] Instance f_RRBb: Proper (R ==> RRBb) f. Admitted.
#[local] Instance f_RRTi: Proper (R ==> RRTi) f. Admitted.
#[local] Instance f_RRTa: Proper (R ==> RRTa) f. Admitted.
#[local] Instance f_RRTb: Proper (R ==> RRTb) f. Admitted.



Ltac asserts b t :=
  match b with
  | true => assert_succeeds t
  | false => assert_fails t
  end.

Ltac test S b1 b2 b3 b4 :=
  let Ht := fresh in
  assert (forall a b, R a b -> S (f a) (f b)) as Ht;
  [ intros a b HR;
    asserts b1 ltac:(rewrite HR);
    asserts b2 ltac:(rewrite <- HR);
    unfold S;
    asserts b3 ltac:(rewrite HR);
    asserts b4 ltac:(rewrite <- HR);
    unfold arrow, Basics.arrow; now rewrite <- HR | clear Ht ].

Goal True.
Proof.
test Ra   true  true  true  true.
test Rb   false false false false.
test RBa  true  true  true  true.
test RBb  false false false false.
test RTa  true  true  true  true.
test RTb  false false false false.
test RRBa true  true  true  true.
test RRBb false false false false.
test RRTa true  true  true  true.
test RRTb false false false false.
apply I.
Qed.
