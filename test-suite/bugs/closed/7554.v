Require Import Coq.Program.Tactics.

(* these should not result in anomalies *)

Fail Program Lemma foo:
  forall P, forall H, forall (n:nat), P n.

Fail Program Lemma foo:
  forall a (P : list a -> Prop), forall H, forall (n:list a), P n.

Fail Program Lemma foo:
  forall (a : Type) (P : list a -> Prop), forall H, forall (n:list a), P n.
