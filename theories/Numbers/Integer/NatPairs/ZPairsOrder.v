Require Import NPlusOrder.
Require Export ZPlusOrder.
Require Export ZPairsPlus.

Module NatPairsOrder (Import NPlusModule : NPlusSignature)
                     (Import NOrderModule : NOrderSignature
                        with Module NatModule := NPlusModule.NatModule) <: ZOrderSignature.
Module Import NPlusOrderPropertiesModule :=
  NPlusOrderProperties NPlusModule NOrderModule.
Module Export IntModule := NatPairsInt NPlusModule.
Open Local Scope NatScope.

Definition lt (p1 p2 : Z) := (fst p1) + (snd p2) < (fst p2) + (snd p1).
Definition le (p1 p2 : Z) := (fst p1) + (snd p2) <= (fst p2) + (snd p1).

Notation "x < y" := (lt x y) : IntScope.
Notation "x <= y" := (le x y) : IntScope.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold lt, E; intros x1 y1 H1 x2 y2 H2; simpl.
rewrite eq_true_iff; split; intro H.
stepr (snd y1 + fst y2) by apply plus_comm.
apply (plus_lt_repl_pair (fst x1) (snd x1)); [| assumption].
stepl (snd y2 + fst x1) by apply plus_comm.
stepr (fst y2 + snd x1) by apply plus_comm.
apply (plus_lt_repl_pair (snd x2) (fst x2)).
now stepl (fst x1 + snd x2) by apply plus_comm.
stepl (fst y2 + snd x2) by apply plus_comm. now stepr (fst x2 + snd y2) by apply plus_comm.
stepr (snd x1 + fst x2) by apply plus_comm.
apply (plus_lt_repl_pair (fst y1) (snd y1)); [| now symmetry].
stepl (snd x2 + fst y1) by apply plus_comm.
stepr (fst x2 + snd y1) by apply plus_comm.
apply (plus_lt_repl_pair (snd y2) (fst y2)).
now stepl (fst y1 + snd y2) by apply plus_comm.
stepl (fst x2 + snd y2) by apply plus_comm. now stepr (fst y2 + snd x2) by apply plus_comm.
Qed.

(* Below is a very long explanation why it would be useful to be
able to use the fold tactic in hypotheses.
We will prove the following statement not from scratch, like lt_wd,
but expanding <= to < and == and then using lt_wd. The theorem we need
to prove is (x1 <= x2) = (y1 <= y2) for all x1 == y1 and x2 == y2 : Z.
To be able to express <= through < and ==, we need to expand <=%Int to
<=%Nat, since we have not proved yet the properties of <=%Int. But
then it would be convenient to fold back equalities from
(fst x1 + snd x2 == fst x2 + snd x1)%Nat to (x1 == x2)%Int.
The reason is that we will need to show that (x1 == x2)%Int <->
(y1 == y2)%Int from (x1 == x2)%Int and (y1 == y2)%Int. If we fold
equalities back to Int, then we could do simple rewriting, since we have
already showed that ==%Int is an equivalence relation. On the other hand,
if we leave equalities expanded to Nat, we will have to apply the
transitivity of ==%Int by hand. *)

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
unfold le, E; intros x1 y1 H1 x2 y2 H2; simpl.
rewrite eq_true_iff. do 2 rewrite le_lt.
pose proof (lt_wd x1 y1 H1 x2 y2 H2) as H; unfold lt in H; rewrite H; clear H.
(* This is a remark about an extra level of definitions created by
"with Module NatModule := NPlusModule.NatModule" constraint in the beginning
of this functor. We cannot just say "fold (x1 == x2)%Int" because it turns out
that it expand to (NPlusModule.NatModule.NDomainModule.E ... ...), since
NPlusModule was imported first. On the other hand, the goal uses
NOrderModule.NatModule.NDomainModule.E, or just NDomainModule.E, since le_lt
theorem was proved in NOrderDomain module. (E without qualifiers refers to
ZDomainModule.E.) Therefore, we issue the "replace" command. It would be nicer,
though, if the constraint "with Module NatModule := NPlusModule.NatModule" in the
declaration of this functor would not create an extra level of definitions
and there would be only one NDomainModule.E. *)
replace NDomainModule.E with NPlusModule.NatModule.NDomainModule.E by reflexivity.
fold (x1 == x2)%Int. fold (y1 == y2)%Int.
assert (H1' : (x1 == y1)%Int); [exact H1 |].
(* We do this instead of "fold (x1 == y1)%Int in H1" *)
assert (H2' : (x2 == y2)%Int); [exact H2 |].
rewrite H1'; rewrite H2'. reflexivity.
Qed.

Open Local Scope IntScope.

Theorem le_lt : forall n m : Z, n <= m <-> n < m \/ n == m.
Proof.
intros n m; unfold lt, le, E; simpl. apply le_lt. (* refers to NOrderModule.le_lt *)
Qed.

Theorem lt_irr : forall n : Z, ~ (n < n).
Proof.
intros n; unfold lt, E; simpl. apply lt_irr.
(* refers to NPlusOrderPropertiesModule.NOrderPropertiesModule.lt_irr *)
Qed.

Theorem lt_S : forall n m, n < (S m) <-> n <= m.
Proof.
intros n m; unfold lt, le, E; simpl. rewrite plus_S_l; apply lt_S.
Qed.

End NatPairsOrder.

(* Since to define the order on integers we need both plus and order
on natural numbers, we can export the properties of plus and order together *)
(*Module NatPairsPlusOrderProperties (NPlusModule : NPlusSignature)
                                   (NOrderModule : NOrderSignature
                                     with Module NatModule := NPlusModule.NatModule).
Module Export NatPairsPlusModule := NatPairsPlus NPlusModule.
Module Export NatPairsOrderModule := NatPairsOrder NPlusModule NOrderModule.
Module Export NatPairsPlusOrderPropertiesModule :=
  ZPlusOrderProperties NatPairsPlusModule NatPairsOrderModule.
End NatPairsPlusOrderProperties.*)
(* We cannot prove to Coq that NatPairsPlusModule.IntModule and
NatPairsOrderModule.IntModule are the same *)

