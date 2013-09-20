(* Submitted by Roland Zumkeller *)

Notation "! A" := (forall i:nat, A) (at level 60).

(* Should fail: no dynamic capture *)
Fail Check ! (i=i).

