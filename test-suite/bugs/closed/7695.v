Require Import Hurkens.

Universes i j k.
Module Type T.
  Parameter T1 : Type@{i+1}.
  Parameter e : Type@{j} = T1 : Type@{k}.
End T.

Module M.
  Definition T1 := Type@{j}.
  Definition e : Type@{j} = T1 : Type@{k} := eq_refl.
End M.

Module F (A:T).
  Definition bad := TypeNeqSmallType.paradox _ A.e.
End F.

Set Printing Universes.
Fail Module X := F M.
(* Universe inconsistency. Cannot enforce j <= i because i < Coq.Logic.Hurkens.105 = j. *)
