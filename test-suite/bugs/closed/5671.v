(* Fixing Meta-unclean specialize *)

Require Import Setoid.
Axiom a : forall x, x=0 -> True.
Lemma lem (x y1 y2:nat) (H:x=0) (H0:eq y1 y2) : y1 = y2.
specialize a with (1:=H). clear H x. intros _.
setoid_rewrite H0.
