Axiom F : forall (b : bool), b = true ->
  forall (i : unit), i = i -> True.

Goal True.
Proof.
unshelve (refine (F _ _ _ _)).
+ exact true.
+ exact tt.
+ exact (@eq_refl bool true).
+ exact (@eq_refl unit tt).
Qed.

(* This was failing in 8.6, because of ?a:nat being wrongly duplicated *)

Goal (forall a : nat, a = 0 -> True) -> True.
intros F.
unshelve (eapply (F _);clear F).
2:reflexivity.
Qed.

(* same think but using Ltac2 refine *)
Require Import Ltac2.Ltac2.

Goal True.
Proof.
(* Ltac2 refine is more like simple_refine *)
unshelve (refine '(F _ _ _ _); Control.shelve_unifiable ()).
+ exact true.
+ exact tt.
+ exact (@eq_refl bool true).
+ exact (@eq_refl unit tt).
Qed.

Goal (forall a : nat, a = 0 -> True) -> True.
intros F.
unshelve (eapply (&F _);clear F).
2:reflexivity.
Qed.
