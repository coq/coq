Require Import Ml.
Require Import MlSem.
Require Import List Bool.

(***** Définitions pour preuves de programmes extraits *****)

Fixpoint internalize_nat n := match n with
  | O => TConstr 0 nil
  | S n => TConstr 1 (internalize_nat n :: nil)
end.

Coercion internalize_nat : nat >-> term.

Lemma intern_clos : forall (n:nat), clos n.
Proof.
intros; rewrite clos_alt.
induction n; intros; simpl_clos_after; intuition; subst; auto.
Qed.
Hint Resolve intern_clos.

Lemma intern_IsValue : forall (n:nat), IsValue n.
Proof.
induction n; simpl; auto.
Qed.
Hint Resolve intern_IsValue.

(***** Preuve de plus *****)

Internal Extraction plus.

Lemma l1 : forall t, clos t -> IsValue t -> 
  (plus__extr @ 0 @ t ==> t).
Proof.
unfold plus__extr; intros.
eapply SmallSteps_trans.
eapply SmallStep_app1.
eapply SmallStep_iotafix; auto.
simpl.
eapply SmallSteps_trans.
eapply SmallStep_beta; auto.
simpl.
eapply SmallSteps_trans.
eapply SmallStep_iota; eauto.
simpl; auto.
exists 0; simpl; auto.
rewrite <- subst_list_equiv; auto; apply subst_list_clos; auto.
Qed.


Lemma l2 : forall t u, clos t -> clos u -> IsValue t -> IsValue u -> 
    (plus__extr @ (TConstr 1 (t::nil)) @ u ==>
     TConstr 1 (plus__extr @ t @ u :: nil)).
Proof.
unfold plus__extr; intros.
eapply SmallSteps_trans.
eapply SmallStep_app1.
eapply SmallStep_iotafix; auto.
match goal with |- context foo [ TFix ?fi ] => set (f:=fi) end.
simpl.
rewrite (subst_clos _ H).
eapply SmallSteps_trans.
eapply SmallStep_beta; auto.
simpl.
rewrite (subst_clos _ H).
eapply SmallSteps_trans.
eapply SmallStep_iota; eauto.
simpl; auto.
simpl.
rewrite <- subst_list_equiv; auto; rewrite subst_list_clos; auto.
unfold f.
exists 0; simpl; auto.
Qed.

Lemma l3 : forall (n m : nat),
  (plus__extr @ n @ m ==> n+m).
Proof.
induction n; simpl; intros.
apply l1; auto.
eapply SmallSteps_trans2.
eapply l2; auto.
eapply SmallSteps_constr1; eauto.
Qed.

(***** pred *****)

Internal Extraction pred.

Lemma l4 : forall (n:nat),
  pred__extr @ n ==> pred n.
Proof.
unfold pred__extr; intros.
eapply SmallSteps_trans.
eapply SmallStep_beta; auto.
simpl.
destruct n; simpl.
(* n=0 *)
eapply SmallSteps_trans.
eapply SmallStep_iota; simpl; auto.
exists 0; simpl; auto.
(* n>0 *)
eapply SmallSteps_trans.
eapply SmallStep_iota; simpl; auto.
exists 0; simpl; auto.
Qed.

(*** le point-fixe le plus simple possible ****)

Fixpoint test n :=
  match n with
    | O => O
    | S n => test n
  end.

Internal Extraction test.

Lemma l5 : forall (n:nat),
  test__extr @ n ==> test n.
Proof.
fix 1.
unfold test__extr; intros.
eapply SmallSteps_trans.
eapply SmallStep_iotafix; simpl; auto.
simpl.
rewrite (subst_clos _ (intern_clos n)).
destruct n; simpl.
eapply SmallSteps_trans.
eapply SmallStep_iota; simpl; auto.
exists 0; simpl; auto.
eapply SmallSteps_trans.
eapply SmallStep_iota; simpl; auto.
simpl.
apply l5; auto.
Qed.

Print l5.
