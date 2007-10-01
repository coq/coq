Require Export NDomain.
Declare Module Export NDomainModule : NDomainSignature.
Open Local Scope NatScope.

Parameter O : N.
Parameter S : N -> N.

Notation "0" := O.

Definition induction :=
forall P : N -> Prop, predicate_wd E P ->
    P 0 -> (forall n : N, P n -> P (S n)) -> forall n : N, P n.

Definition other_induction :=
forall P : N -> Prop,
  (forall n : N, n == 0 -> P n) ->
  (forall n : N, P n -> forall m : N, m == S n -> P m) ->
  forall n : N, P n.

Theorem other_ind_implies_ind : other_induction -> induction.
Proof.
unfold induction, other_induction; intros OI P predicate_wd Base Step.
apply OI; unfold predicate_wd in predicate_wd.
intros; now apply -> (predicate_wd 0).
intros n Pn m EmSn; now apply -> (predicate_wd (S n)); [apply Step|].
Qed.

Theorem ind_implies_other_ind : induction -> other_induction.
Proof.
intros I P Base Step.
set (A := fun n => forall m, m == n -> P m).
cut (forall n, A n).
unfold A; intros H n; now apply (H n).
apply I.
unfold predicate_wd, A. intros x y Exy.
split; intros H m Em; apply H; [now rewrite Exy | now rewrite <- Exy].
exact Base.
intros n Qn m EmSn; now apply Step with (n := n); [apply Qn |].
Qed.

(* This theorem is not really needed. It shows that if we have
other_induction and we proved the base case and the induction step, we
can in fact show that the predicate in question is well-defined, and
therefore we can turn this other induction into the standard one. *)
Theorem other_ind_implies_predicate_wd :
other_induction ->
  forall P : N -> Prop,
    (forall n : N, n == 0 -> P n) ->
    (forall n : N, P n -> forall m : N, m == S n -> P m) ->
    predicate_wd E P.
Proof.
intros OI P Base Step; unfold predicate_wd.
intros x; pattern x; apply OI; clear x.
(* Base case *)
intros x H1 y H2.
assert (y == 0); [rewrite <- H2; now rewrite H1|].
assert (P x); [now apply Base|].
assert (P y); [now apply Base|].
split; now intro.
(* Step *)
intros x IH z H y H1.
rewrite H in H1. symmetry in H1.
split; (intro H2; eapply Step; [|apply H || apply H1]); now apply OI.
Qed.

Section Recursion.

Variable A : Set.
Variable EA : relation A.
Hypothesis EA_symm : symmetric A EA.
Hypothesis EA_trans : transitive A EA.

Add Relation A EA
 symmetry proved by EA_symm
 transitivity proved by EA_trans
as EA_rel.

Lemma EA_neighbor : forall a a' : A, EA a a' -> EA a a.
Proof.
intros a a' EAaa'.
apply EA_trans with (y := a'); [assumption | apply EA_symm; assumption].
Qed.

Parameter recursion : A -> (N -> A -> A) -> N -> A.

Axiom recursion_0 :
  forall (a : A) (f : N -> A -> A),
    EA a a -> forall x : N, x == 0 -> EA (recursion a f x) a.

Axiom recursion_succ :
  forall (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == S m -> EA (recursion a f n) (f m (recursion a f m)).

Theorem recursion_wd : induction ->
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, fun2_wd E EA EA f -> fun2_wd E EA EA f' -> eq_fun2 E EA EA f f' ->
      forall x x' : N, x == x' ->
        EA (recursion a f x) (recursion a' f' x').
Proof.
intros I a a' Eaa' f f' f_wd f'_wd Eff'.
apply ind_implies_other_ind in I.
intro x; pattern x; apply I; clear x.
intros x Ex0 x' Exx'.
rewrite Ex0 in Exx'; symmetry in Exx'.
(* apply recursion_0 in Ex0. produces
Anomaly: type_of: this is not a well-typed term. Please report. *)
assert (EA (recursion a f x) a).
apply recursion_0. now apply EA_neighbor with (a' := a'). assumption.
assert (EA a' (recursion a' f' x')).
apply EA_symm. apply recursion_0. now apply EA_neighbor with (a' := a). assumption.
apply EA_trans with (y := a). assumption.
now apply EA_trans with (y := a').
intros x IH y H y' H1.
rewrite H in H1; symmetry in H1.
assert (EA (recursion a f y) (f x (recursion a f x))).
apply recursion_succ. now apply EA_neighbor with (a' := a').
assumption. now symmetry.
assert (EA (f' x (recursion a' f' x)) (recursion a' f' y')).
symmetry; apply recursion_succ. now apply EA_neighbor with (a' := a). assumption.
now symmetry.
assert (EA (f x (recursion a f x)) (f' x (recursion a' f' x))).
apply Eff'. reflexivity. apply IH. reflexivity.
apply EA_trans with (y := (f x (recursion a f x))). assumption.
apply EA_trans with (y := (f' x (recursion a' f' x))). assumption.
assumption.
Qed.

Axiom recursion_0' :
  forall (a : A) (f : N -> A -> A),
    forall x : N, x == 0 -> recursion a f x = a.

Axiom recursion_succ' :
  forall (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == S m -> EA (recursion a f n) (f m (recursion a f m)).

Theorem recursion_wd' : other_induction ->
  forall a a' : A, EA a a -> EA a' a' -> EA a a' ->
    forall f f' : N -> A -> A, fun2_wd E EA EA f -> fun2_wd E EA EA f' -> eq_fun2 E EA EA f f' ->
      forall x x' : N, x == x' ->
        EA (recursion a f x) (recursion a' f' x').
Proof.
intros I a a' a_wd a'_wd Eaa' f f' f_wd f'_wd Eff'.
intro x; pattern x; apply I; clear x.
intros x Ex0 x' Exx'. rewrite Ex0 in Exx'. symmetry in Exx'.
replace (recursion a f x) with a. replace (recursion a' f' x') with a'.
assumption. symmetry; now apply recursion_0'. symmetry; now apply recursion_0'.
intros x IH y EySx y' Eyy'. rewrite EySx in Eyy'. symmetry in Eyy'.
apply EA_trans with (y := (f x (recursion a f x))). now apply recursion_succ'.
apply EA_trans with (y := (f' x (recursion a' f' x))).
apply Eff'. reflexivity. now apply IH.
symmetry; now apply recursion_succ'.
Qed.



End Recursion.

Implicit Arguments recursion [A].

