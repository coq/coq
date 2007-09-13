Require Import NPlus.
Require Export ZPlus.
Require Export ZPairsAxioms.

Module NatPairsPlus (Import NPlusMod : NPlusSig) <: ZPlusSignature.
Module Export ZBaseMod := NatPairsInt NPlusMod.
Open Local Scope NatScope.

Definition plus (x y : Z) := ((fst x) + (fst y), (snd x) + (snd y)).
Definition minus (x y : Z) := ((fst x) + (snd y), (snd x) + (fst y)).
Definition uminus (x : Z) := (snd x, fst x).
(* Unfortunately, the elements of pair keep increasing, even during subtraction *)

Notation "x + y" := (plus x y) : IntScope.
Notation "x - y" := (minus x y) : IntScope.
Notation "- x" := (uminus x) : IntScope.

(* Below, we need to rewrite subtems that have several occurrences.
Since with the currect setoid_rewrite we cannot point an accurrence
using pattern, we use symmetry tactic to make a particular occurrence
the leftmost, since that is what rewrite will use. *)
Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold E, plus; intros x1 y1 H1 x2 y2 H2; simpl.
pose proof (plus_wd (fst x1 + snd y1) (fst y1 + snd x1) H1
                    (fst x2 + snd y2) (fst y2 + snd x2) H2) as H.
rewrite plus_shuffle1. symmetry. now rewrite plus_shuffle1.
Qed.

Add Morphism minus with signature E ==> E ==> E as minus_wd.
Proof.
unfold E, plus; intros x1 y1 H1 x2 y2 H2; simpl.
rewrite plus_comm in H2. symmetry in H2; rewrite plus_comm in H2.
pose proof (NPlusMod.plus_wd (fst x1 + snd y1) (fst y1 + snd x1) H1
                                (snd x2 + fst y2) (snd y2 + fst x2) H2) as H.
rewrite plus_shuffle1. symmetry. now rewrite plus_shuffle1.
Qed.

Add Morphism uminus with signature E ==> E as uminus_wd.
Proof.
unfold E, plus; intros x y H; simpl.
rewrite plus_comm. symmetry. now rewrite plus_comm.
Qed.

Open Local Scope IntScope.

Theorem plus_0 : forall n, 0 + n == n.
Proof.
intro n; unfold plus, E; simpl. now do 2 rewrite NPlusMod.plus_0_l.
Qed.

Theorem plus_succ : forall n m, (S n) + m == S (n + m).
Proof.
intros n m; unfold plus, E; simpl. now do 2 rewrite NPlusMod.plus_succ_l.
Qed.

Theorem minus_0 : forall n, n - 0 == n.
Proof.
intro n; unfold minus, E; simpl. now do 2 rewrite plus_0_r.
Qed.

Theorem minus_succ : forall n m, n - (S m) == P (n - m).
Proof.
intros n m; unfold minus, E; simpl. symmetry; now rewrite plus_succ_r.
Qed.

Theorem uminus_0 : - 0 == 0.
Proof.
unfold uminus, E; simpl. now rewrite plus_0_l.
Qed.

Theorem uminus_succ : forall n, - (S n) == P (- n).
Proof.
reflexivity.
Qed.

End NatPairsPlus.

Module NatPairsPlusProperties (NPlusMod : NPlusSig).
Module Export NatPairsPlusModule := NatPairsPlus NPlusMod.
Module Export NatPairsPlusPropertiesModule := ZPlusProperties NatPairsPlusModule.
End NatPairsPlusProperties.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
