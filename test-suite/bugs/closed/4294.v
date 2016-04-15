Require Import Hurkens.

Module NonPoly.
Module Type Foo.
  Definition U := Type.
  Parameter eq : Type = U.
End Foo.

Module M : Foo with Definition U := Type.
  Definition U := Type.
  Definition eq : Type = U := eq_refl.
End M.

Print Universes.
Fail Definition bad : False := TypeNeqSmallType.paradox M.U M.eq.
End NonPoly.

Set Universe Polymorphism.

Module Type Foo.
  Definition U := Type.
  Monomorphic Parameter eq : Type = U.
End Foo.

Module M : Foo with Definition U := Type.
  Definition U := Type.
  Monomorphic Definition eq : Type = U := eq_refl.
End M.

Fail Definition bad : False := TypeNeqSmallType.paradox Type M.eq.
(* Print Assumptions bad. *)
