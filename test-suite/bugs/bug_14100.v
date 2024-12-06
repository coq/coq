From Corelib Require Import Extraction.

Set Warnings "-extraction-inside-module".

Module OriginalExample.

Variant nondetE : Type -> Type :=
  Or : nondetE bool.

Module Type MinSIG.
Parameter otherE : Type -> Type.
End MinSIG.

Module Min : MinSIG.
Definition otherE := nondetE.
End Min.

Extraction TestCompile Min.

End OriginalExample.

(**)

Module ExampleWithSmallParameter.

Variant nondetE : nat -> Type -> Type :=
  Or : nondetE 0 bool.

Module Type MinSIG.
Parameter otherE : nat -> Type -> Type.
End MinSIG.

Module Min : MinSIG.
Definition otherE := nondetE.
End Min.

Extraction TestCompile Min.

End ExampleWithSmallParameter.

(* This was already working *)

Module ExampleWithLogicalDefinition.

Definition nondetE (n:nat) (X:Type) := Prop.

Module Type MinSIG.
Parameter otherE : nat -> Type -> Type.
End MinSIG.

Module Min : MinSIG.
Definition otherE := nondetE.
End Min.

Extraction TestCompile Min.

End ExampleWithLogicalDefinition.
