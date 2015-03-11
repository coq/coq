Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 64 lines to 30 lines. *)
Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.
Record SpecializedCategory (obj : Type) := { Object :> _ := obj }.

Record > Category :=
  { CObject : Type;
    UnderlyingCategory :> @SpecializedCategory CObject }.

Record SpecializedFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :=
  { ObjectOf :> objC -> objD }.

Definition Functor (C D : Category) := SpecializedFunctor C D.

Parameter TerminalCategory : SpecializedCategory unit.

Definition focus A (_ : A) := True.

Definition CommaCategory_Object (A : Category) (S : Functor TerminalCategory A) : Type.
  assert (Hf : focus ((S tt) = (S tt))) by constructor.
  let C1 := constr:(CObject) in
  let C2 := constr:(fun C => @Object (CObject C) C) in
  let check := constr:(eq_refl : C1 = C2) in
  unify C1 C2.
  progress change CObject with (fun C => @Object (CObject C) C) in *.
  (* not convertible *)
  admit.
Defined.
