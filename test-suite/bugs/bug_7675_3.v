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
#[universes(polymorphic), local] Instance f_Ri@{u v?|?}: Proper@{u v} (R ==> Ri) f. Admitted.
#[universes(polymorphic), local] Instance f_Ra@{u v?}: Proper@{u v} (R ==> Ra) f. Admitted.
#[local,universes(polymorphic)] Instance f_Rb@{u v?}: Proper@{u v} (R ==> Rb) f. Admitted.
#[local,universes(polymorphic)] Instance f_RBi@{u v?}: Proper@{u v} (R ==> RBi) f. Admitted.
#[local,universes(polymorphic)] Instance f_RBa@{u v?}: @Proper@{u v} (A -> B) (R ==> RBa) f. Admitted.
#[local,universes(polymorphic)] Instance f_RBb@{u v?}: Proper@{u v} (R ==> RBb) f. Admitted.
#[local,universes(polymorphic)] Instance f_RTi@{u v?}: Proper@{u v} (R ==> RTi) f. Admitted.
#[local,universes(polymorphic)] Instance f_RTa@{u v?}: Proper@{u v} (R ==> RTa) f. Admitted.

(*
*** [ f_RTa@{u v u0 u1 u2 u3} :
Proper@{u v} (R ==> RTa) f ]
(* u v u0 u1 u2 u3 |= A.u0 <= u
                          A.u0 <= u0
                      R.u0 <= u1
                      RTa.u2 <= u3
                      u <= max(u0, u2)
                      v <= max(u0, u1, u3)
                      u0 <= u
                      u0 <= v
                      u1 <= v
                      u2 <= u
                      u3 <= v
                      B.u0+1 <= u
                      B.u0+1 <= u2
                      RTa.u1 = B.u0
                      RTa.u1 = RTa.u0 *)
*)

#[local,universes(polymorphic)] Instance f_RTb@{u v?}: Proper@{u v} (R ==> RTb) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRBi@{u v?}: Proper@{u v} (R ==> RRBi) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRBa@{u v?}: Proper@{u v} (R ==> RRBa) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRBb@{u v?}: Proper@{u v} (R ==> RRBb) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRTi@{u v?}: Proper@{u v} (R ==> RRTi) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRTa@{u v?}: @Proper@{u v} (A -> B) (R ==> RRTa) f. Admitted.
#[local,universes(polymorphic)] Instance f_RRTb@{u v?}: Proper@{u v} (R ==> RRTb) f. Admitted.



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
Print Universes.

Goal True.
Proof.
(* test Ra   true  true  true  true.  *)
Show Universes.
 (* test Rb   false false false false.  *)
(* test RBa  true  true  true  true.  *)
(* test RBb  false false false false. *)
(* test RTa  true  true  true  true. *)
(* test RTb  false false false false. *)
(* test RRBa true  true  true  true. *)
(* test RRBb false false false false. *)
test RRTa true  true  true  true. *)
test RRTb false false false false.
apply I.
Qed.
