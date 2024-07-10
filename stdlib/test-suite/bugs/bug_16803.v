From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
Import ZifyClasses.

Module Test1.

  Record Z2@{u} : Type@{u} := MkZ2 { unZ2 : Z }.

  Global Instance Inj_Z2_Z : InjTyp Z2 Z :=
    { inj := unZ2
    ; pred := fun _ => True
    ; cstr := fun _ => I
    }.
  Add Zify InjTyp Inj_Z2_Z.

  Lemma eq_Z2_inj :
    forall (n m : Z2),
      n = m <-> unZ2 n = unZ2 m.
  Proof.
  Admitted.

  Global Instance Op_eq : BinRel (@eq Z2) :=
    { TR := @eq Z
    ; TRInj := eq_Z2_inj
    }.
  Add Zify BinRel Op_eq.

  Theorem lia_refl_ex : forall (a b : Z2), a = a.
  Proof.
    lia.
  Defined.

  Fail Constraint mkrel.u0 < unZ2.u.

End Test1.

Module Test2.
  (* we need a separate copy of Z2 to test a different case because
     otherwise the constraint is set in one of the tests *)

  Record Z2@{u} : Type@{u} := MkZ2 { unZ2 : Z }.

  Global Instance Inj_Z2_Z : InjTyp Z2 Z :=
    { inj := unZ2
    ; pred := fun _ => True
    ; cstr := fun _ => I
    }.
  Add Zify InjTyp Inj_Z2_Z.

  Lemma eq_Z2_inj :
    forall (n m : Z2),
      n = m <-> unZ2 n = unZ2 m.
  Proof.
  Admitted.

  Global Instance Op_eq : BinRel (@eq Z2) :=
    { TR := @eq Z
    ; TRInj := eq_Z2_inj
    }.
  Add Zify BinRel Op_eq.

  Theorem lia_refl_ex : forall (a b : Z2), a = b -> True.
  Proof.
    zify.
    exact I.
  Defined.

  Fail Constraint mkrel.u0 < unZ2.u.

End Test2.

Module Test3.

  Record Z2@{u} : Type@{u} := MkZ2 { unZ2 : Z }.

  Global Instance Inj_Z2_Z : InjTyp Z2 Z :=
    { inj := unZ2
    ; pred := fun _ => True
    ; cstr := fun _ => I
    }.
  Add Zify InjTyp Inj_Z2_Z.

  Lemma eq_Z2_inj :
    forall (n m : Z2),
      n = m <-> unZ2 n = unZ2 m.
  Proof.
  Admitted.

  Global Instance Op_eq : BinRel (@eq Z2) :=
    { TR := @eq Z
    ; TRInj := eq_Z2_inj
    }.
  Add Zify BinRel Op_eq.

  Constraint mkrel.u0 < unZ2.u.

  Theorem lia_refl_ex : forall (a b : Z2), a = a.
  Proof.
    Fail lia.
  Abort.

End Test3.
