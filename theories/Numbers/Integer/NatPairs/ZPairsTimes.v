Require Import Ring.
Require Import NTimes.
Require Export ZTimes.
Require Export ZPairsPlus.

Module NatPairsTimes (Import NTimesMod : NTimesSig) <: ZTimesSignature.
Module Export ZPlusModule := NatPairsPlus NTimesMod.NPlusMod. (* "NTimesMod." is optional *)
Module Import NTimesPropertiesModule := NTimesPropFunct NTimesMod.
Open Local Scope NatScope.

Definition times (n m : Z) :=
  ((fst n) * (fst m) + (snd n) * (snd m), (fst n) * (snd m) + (snd n) * (fst m)).

Notation "x * y" := (times x y) : IntScope.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold times, E; intros x1 y1 H1 x2 y2 H2; simpl.
stepl_ring (fst x1 * fst x2 + (snd x1 * snd x2 + fst y1 * snd y2 + snd y1 * fst y2)).
stepr_ring (fst x1 * snd x2 + (fst y1 * fst y2 + snd y1 * snd y2 + snd x1 * fst x2)).
apply plus_times_repl_pair with (n := fst y2) (m := snd y2); [| now idtac].
stepl_ring (snd x1 * snd x2 + (fst x1 * fst y2 + fst y1 * snd y2 + snd y1 * fst y2)).
stepr_ring (snd x1 * fst x2 + (fst x1 * snd y2 + fst y1 * fst y2 + snd y1 * snd y2)).
apply plus_times_repl_pair with (n := snd y2) (m := fst y2);
  [| rewrite plus_comm; symmetry; now rewrite plus_comm].
stepl_ring (snd y2 * snd x1 + (fst x1 * fst y2 + fst y1 * snd y2 + snd y1 * fst y2)).
stepr_ring (snd y2 * fst x1 + (snd x1 * fst y2 + fst y1 * fst y2 + snd y1 * snd y2)).
apply plus_times_repl_pair with (n := snd y1) (m := fst y1);
  [| rewrite plus_comm; symmetry; now rewrite plus_comm].
stepl_ring (fst y2 * fst x1 + (snd y2 * snd y1 + fst y1 * snd y2 + snd y1 * fst y2)).
stepr_ring (fst y2 * snd x1 + (snd y2 * fst y1 + fst y1 * fst y2 + snd y1 * snd y2)).
apply plus_times_repl_pair with (n := fst y1) (m := snd y1); [| now idtac].
ring.
Qed.

Open Local Scope IntScope.

Theorem times_0 : forall n, n * 0 == 0.
Proof.
intro n; unfold times, E; simpl.
repeat rewrite times_0_r. now rewrite plus_assoc.
Qed.

Theorem times_succ : forall n m, n * (S m) == n * m + n.
Proof.
intros n m; unfold times, S, E; simpl.
do 2 rewrite times_succ_r. ring.
Qed.

End NatPairsTimes.

Module NatPairsTimesProperties (NTimesMod : NTimesSig).
Module Export NatPairsTimesModule := NatPairsTimes NTimesMod.
Module Export NatPairsTimesPropertiesModule := ZTimesProperties NatPairsTimesModule.
End NatPairsTimesProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
