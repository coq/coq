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
  progress change CObject with (fun C => @Object (CObject C) C) in *.
  (* not convertible *)
