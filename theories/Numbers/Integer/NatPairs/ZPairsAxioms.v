Require Export NTimesOrder.
Require Export ZTimesOrder.

Module NatPairsDomain (Import NPlusModule : NPlusSignature) <: ZDomainSignature.
(*  with Definition Z :=
    (NPM.NatModule.DomainModule.N * NPM.NatModule.DomainModule.N)%type
  with Definition E :=
    fun p1 p2  =>
      NPM.NatModule.DomainModule.E (NPM.plus (fst p1) (snd p2)) (NPM.plus (fst p2) (snd p1))
  with Definition e :=
    fun p1 p2  =>
      NPM.NatModule.DomainModule.e (NPM.plus (fst p1) (snd p2)) (NPM.plus (fst p2) (snd p1)).*)

Module Export NPlusPropertiesModule := NPlusProperties NPlusModule.
Open Local Scope NatScope.

Definition Z : Set := (N * N)%type.
Definition E (p1 p2 : Z) := ((fst p1) + (snd p2) == (fst p2) + (snd p1)).
Definition e (p1 p2 : Z) := e ((fst p1) + (snd p2)) ((fst p2) + (snd p1)).

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.
Notation "x == y" := (E x y) (at level 70) : IntScope.
Notation "x # y" := (~ E x y) (at level 70) : IntScope.

Theorem E_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e; apply E_equiv_e.
Qed.

Theorem E_equiv : equiv Z E.
Proof.
split; [| split]; unfold reflexive, symmetric, transitive, E.
(* reflexivity *)
now intro.
(* transitivity *)
intros x y z H1 H2.
apply plus_cancel_l with (p := fst y + snd y).
rewrite (plus_shuffle2 (fst y) (snd y) (fst x) (snd z)).
rewrite (plus_shuffle2 (fst y) (snd y) (fst z) (snd x)).
rewrite plus_comm. rewrite (plus_comm (snd y) (fst x)).
rewrite (plus_comm (snd y) (fst z)). now apply plus_wd.
(* symmetry *)
now intros.
Qed.

Add Relation Z E                                                                                 
 reflexivity proved by (proj1 E_equiv)                                                           
 symmetry proved by (proj2 (proj2 E_equiv))                                                      
 transitivity proved by (proj1 (proj2 E_equiv))                                                  
as E_rel.

Add Morphism (@pair N N)
  with signature NDomainModule.E ==> NDomainModule.E ==> E
  as pair_wd.
Proof.
intros x1 x2 H1 y1 y2 H2; unfold E; simpl; rewrite H1; now rewrite H2.
Qed.

End NatPairsDomain.

Module NatPairsInt (Import NPlusModule : NPlusSignature) <: IntSignature.
Module Export ZDomainModule := NatPairsDomain NPlusModule.
Module Export ZDomainModuleProperties := ZDomainProperties ZDomainModule.
Open Local Scope IntScope.

Definition O : Z := (0, 0)%Nat.
Definition S (n : Z) := (NatModule.S (fst n), snd n).
Definition P (n : Z) := (fst n, NatModule.S (snd n)).
(* Unfortunately, we do not have P (S n) = n but only P (S n) == n.
It could be possible to consider as "canonical" only pairs where one of
the elements is 0, and make all operations convert canonical values into
other canonical values. We do not do this because this is more complex
and because we do not have the predecessor function on N at this point. *)

Notation "0" := O : IntScope.

Add Morphism S with signature E ==> E as S_wd.
Proof.
unfold S, E; intros n m H; simpl.
do 2 rewrite plus_Sn_m; now rewrite H.
Qed.

Add Morphism P with signature E ==> E as P_wd.
Proof.
unfold P, E; intros n m H; simpl.
do 2 rewrite plus_n_Sm; now rewrite H.
Qed.

Theorem S_inj : forall x y : Z, S x == S y -> x == y.
Proof.
unfold S, E; simpl; intros x y H.
do 2 rewrite plus_Sn_m in H. now apply S_inj in H.
Qed.

Theorem S_P : forall x : Z, S (P x) == x.
Proof.
intro x; unfold S, P, E; simpl.
rewrite plus_Sn_m; now rewrite plus_n_Sm.
Qed.

Section Induction.
Open Scope NatScope. (* automatically closes at the end of the section *)
Variable Q : Z -> Prop.
Hypothesis Q_wd : pred_wd E Q.

Add Morphism Q with signature E ==> iff as Q_morph.
Proof.
exact Q_wd.
Qed.

Theorem induction :
  Q 0 -> (forall x, Q x -> Q (S x)) -> (forall x, Q x -> Q (P x)) -> forall x, Q x.
Proof.
intros Q0 QS QP x; unfold O, S, P, pred_wd, E in *.
destruct x as [n m].
cut (forall p : N, Q (p, 0)); [intro H1 |].
cut (forall p : N, Q (0, p)); [intro H2 |].
destruct (plus_dichotomy n m) as [[p H] | [p H]].
rewrite (Q_wd (n, m) (0, p)); simpl. rewrite plus_0_l; now rewrite plus_comm. apply H2.
rewrite (Q_wd (n, m) (p, 0)); simpl. now rewrite plus_0_r. apply H1.
induct p. assumption. intros p IH.
replace 0 with (fst (0, p)); [| reflexivity].
replace p with (snd (0, p)); [| reflexivity]. now apply QP.
induct p. assumption. intros p IH.
replace 0 with (snd (p, 0)); [| reflexivity].
replace p with (fst (p, 0)); [| reflexivity]. now apply QS.
Qed.

End Induction.

End NatPairsInt.
