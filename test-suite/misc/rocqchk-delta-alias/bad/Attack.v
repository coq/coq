Unset Elimination Schemes.

Inductive bool : Set := true | false.

Module A.
  Definition x : bool := true.
  Inductive inhabited : Prop := witness : inhabited.
End A.

(* These declarations have the same user names as the included declarations
   in good/Attack.v, but incompatible bodies. *)
Module B.
  Definition x : bool := false.
  Inductive inhabited : Prop := .
End B.
