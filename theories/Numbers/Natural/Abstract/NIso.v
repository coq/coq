Require Export NAxioms.

Module Homomorphism (Nat1 Nat2 : NBaseSig).

Notation Local N1 := Nat1.NDomainModule.N.
Notation Local N2 := Nat2.NDomainModule.N.
Notation Local E1 := Nat1.NDomainModule.E.
Notation Local E2 := Nat2.NDomainModule.E.
Notation Local O1 := Nat1.O.
Notation Local O2 := Nat2.O.
Notation Local S1 := Nat1.S.
Notation Local S2 := Nat2.S.
Notation Local "x == y" := (Nat2.NDomainModule.E x y) (at level 70).

Definition homomorphism (f : N1 -> N2) : Prop :=
  f O1 == O2 /\ forall x : N1, f (S1 x) == S2 (f x).

Definition natural_isomorphism : N1 -> N2 :=
  Nat1.recursion O2 (fun (x : N1) (p : N2) => S2 p).

Add Morphism natural_isomorphism
with signature E1 ==> E2
as natural_isomorphism_wd.
Proof.
unfold natural_isomorphism.
intros x y Exy.
apply Nat1.recursion_wd with (EA := E2).
reflexivity.
unfold eq_fun2. intros _ _ _ y' y'' H. now apply Nat2.succ_wd.
assumption.
Qed.

Theorem natural_isomorphism_0 : natural_isomorphism O1 == O2.
Proof.
unfold natural_isomorphism; now rewrite Nat1.recursion_0.
Qed.

Theorem natural_isomorphism_succ :
  forall x : N1, natural_isomorphism (S1 x) == S2 (natural_isomorphism x).
Proof.
unfold natural_isomorphism;
intro x; now rewrite (Nat1.recursion_succ Nat2.NDomainModule.E);
[| unfold fun2_wd; intros; apply Nat2.succ_wd |].
Qed.

Theorem iso_hom : homomorphism natural_isomorphism.
Proof.
unfold homomorphism, natural_isomorphism; split;
[exact natural_isomorphism_0 | exact natural_isomorphism_succ].
Qed.

End Homomorphism.

Module Inverse (Nat1 Nat2 : NBaseSig).

Module Import NBasePropMod1 := NBasePropFunct Nat1.
(* This makes the tactic induct available. Since it is taken from
NBasePropFunct Nat1, it refers to Nat1.induction. *)

Module Hom12 := Homomorphism Nat1 Nat2.
Module Hom21 := Homomorphism Nat2 Nat1.

Notation Local N1 := Nat1.NDomainModule.N.
Notation Local N2 := Nat2.NDomainModule.N.
Notation Local h12 := Hom12.natural_isomorphism.
Notation Local h21 := Hom21.natural_isomorphism.

Notation Local "x == y" := (Nat1.NDomainModule.E x y) (at level 70).

Lemma iso_inverse :
  forall x : N1, h21 (h12 x) == x.
Proof.
induct x.
now rewrite Hom12.natural_isomorphism_0; rewrite Hom21.natural_isomorphism_0.
intros x IH.
rewrite Hom12.natural_isomorphism_succ; rewrite Hom21.natural_isomorphism_succ;
now rewrite IH.
Qed.

End Inverse.

Module Isomorphism (Nat1 Nat2 : NBaseSig).

Module Hom12 := Homomorphism Nat1 Nat2.
Module Hom21 := Homomorphism Nat2 Nat1.

Module Inverse121 := Inverse Nat1 Nat2.
Module Inverse212 := Inverse Nat2 Nat1.

Notation Local N1 := Nat1.NDomainModule.N.
Notation Local N2 := Nat2.NDomainModule.N.
Notation Local E1 := Nat1.NDomainModule.E.
Notation Local E2 := Nat2.NDomainModule.E.
Notation Local h12 := Hom12.natural_isomorphism.
Notation Local h21 := Hom21.natural_isomorphism.

Definition isomorphism (f1 : N1 -> N2) (f2 : N2 -> N1) : Prop :=
  Hom12.homomorphism f1 /\ Hom21.homomorphism f2 /\
  forall x : N1, E1 (f2 (f1 x)) x /\
  forall y : N2, E2 (f1 (f2 y)) y.

Theorem iso_iso : isomorphism h12 h21.
Proof.
unfold isomorphism.
split. apply Hom12.iso_hom.
split. apply Hom21.iso_hom.
split. apply Inverse121.iso_inverse.
apply Inverse212.iso_inverse.
Qed.

End Isomorphism.

