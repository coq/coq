Require Import Ml.
Require Import MlSem.
Require Import List Bool.

Set Implicit Arguments.
Unset Strict Implicit.


(***** Définitions pour preuves de programmes extraits *****)

(* Un type de données simple *)

Fixpoint internalize_nat n :=
  match n with
    | O => TConstr 0 nil
    | S n => TConstr 1 (internalize_nat n :: nil)
  end.

Coercion internalize_nat : nat >-> term.

Lemma intern_nat_clos : forall (n:nat), clos n.
Proof.
  intros; rewrite clos_alt.
  induction n; intros; simpl_clos_after; intuition; subst; auto.
Qed.
Hint Resolve intern_nat_clos.

Lemma intern_nat_IsValue : forall (n:nat), IsValue n.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve intern_nat_IsValue.

(* Un type dépendant avec paramètres *)

Section Internalize_sig.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable internalize_A : A -> term.
  Coercion Local internalize_A : A >-> term.
  Let sig_P := sig P.

  Hypothesis intern_A_clos : forall (a:A), clos a.
  Hypothesis intern_A_IsValue : forall (a:A), IsValue a.

  Definition internalize_sig (x : sig_P) :=
    match x with
      exist x _ => TConstr 0 (TDummy::TDummy::(x:term)::TDummy::nil)
    end.
  Coercion internalize_sig : sig_P >-> term.

  Lemma intern_sig_clos : forall (x:sig_P), clos x.
  Proof.
    intros; rewrite clos_alt.
    induction x; intros; simpl_clos_after; intuition; subst; auto;
    simpl_clos_after; auto.
    rewrite <- clos_alt.
    apply intern_A_clos.
  Qed.

  Lemma intern_sig_IsValue : forall (x:sig_P), IsValue x.
  Proof.
    induction x; simpl; auto.
    repeat constructor; apply intern_A_IsValue.
  Qed.

End Internalize_sig.

Hint Resolve intern_sig_clos.
Hint Resolve intern_sig_IsValue.

(* Intantiation à nat *)

Definition sig_nat := @sig nat.

Definition internalize_sig_nat P (x : sig_nat P) :=
  internalize_sig internalize_nat x.

Coercion internalize_sig_nat : sig_nat >-> term.


(***** La tactique *****)

Ltac extauto_absurd :=
  match goal with
    | H : context [ match ?a with end ] |- _ => destruct a
  end.

Ltac extauto :=
  intros; simpl;
  match goal with
    | |- context [ (internalize_nat ?n) [_:=_] ] => rewrite (subst_clos n); extauto
    | |- context [ (internalize_nat ?n) [_;;=_] ] => rewrite (subst_list_clos n); extauto

    | |- context [TMatch (internalize_nat ?n) _ ] =>
      trivial; induction n; simpl in *;
      try extauto_absurd; subst; extauto

    | |- (?a @ _ ==> _) =>
      try unfold a; trivial;
      eapply SmallSteps_beta_iotafix;
      extauto

    | |- (TMatch (TConstr ?n ?tl) ?l ==> _) =>
      eapply SmallSteps_iota with (pl:=l) (n:=n) (tl:=tl);
      extauto

    | |- (TConstr _ ?l ==> _) =>
      eapply SmallSteps_constr with (tl:=l);
      extauto

    | |- (TFun _ ==> _) => exists 0; simpl
    | |- (TFix _ ==> _) => exists 0; simpl
    | |- (TDummy ==> _) => exists 0; simpl
    | |- (internalize_nat _ ==> _) => exists 0; simpl
    | |- SmallSteps_list _ _ => econstructor; extauto
    | _ => idtac
  end; try (progress eauto; extauto).


(***** Preuve de plus *****)

Internal Extraction plus.

(* La tactique extauto devrait pouvoir résoudre la correction pour les
   fonctions simples sur les entiers... reste encore à tester les
   fonctions définies par patterns imbriqués. *)
Lemma plus__extr_correct : forall (n m : nat),
  (plus__extr @ n @ m ==> n+m).
Proof.
  extauto.
Qed.

(* Autre approche en utilisant Functional Scheme... dans ce cas, la
   tactique n'aurait pas besoin de faire d'induction, Functional
   Scheme donnant directement les équations à résoudre.
   Mais FS ne semple pas pas aimer les fonctions avec types dépendants
   (cf sig) *)
Functional Scheme plus_ind := Induction for plus Sort Prop.

Lemma plus__extr_correct' : forall (n m : nat),
  (plus__extr @ n @ m ==> n+m).
Proof.
  intros.
  functional induction (n+m); extauto.
Qed.


(***** Preuve de pred *****)

Internal Extraction pred.

Lemma pred__extr_correct : forall (n:nat), (pred__extr @ n ==> pred n).
Proof.
  extauto.
Qed.


(***** Prédécesseur avec précondition *****)

Definition pred2 : forall n, n <> 0 -> nat.
Proof.
  intros n H.
  destruct n; intros.
  destruct H; auto.
  exact n.
Defined.

Internal Extraction pred2.
(*
   Functional Scheme pred2_ind := Induction for pred2 Sort Prop.
   renvoie une erreur :
   "Anomaly: uncaught exception Not_found. Please report."
*)

Lemma pred2__extr_correct : forall n (H:n <> 0) p,
  p = pred2 H ->
  (pred2__extr @ n @ TDummy ==> p).
Proof.
  extauto.
Qed.


(***** Prédécesseur avec précondition et postcondition *****)

Definition pred3 : forall n, n <> 0 -> {p | n = S p}.
Proof.
  intros; destruct n.
  destruct H; simpl; auto.
  exists n; auto.
Defined.

Internal Extraction pred3.

Lemma pred3__extr_correct : forall n (H:n<>0), let P p := n = S p in
  forall (p:sig_nat P), p = pred3 H ->
  (pred3__extr @ n @ TDummy ==> p).
Proof.
  extauto.
Qed.


(*** Le point-fixe le plus simple possible ****)

Fixpoint test n :=
  match n with
    | O => O
    | S n => test n
  end.

Internal Extraction test.

Lemma test__extr_correct : forall (n:nat),
  test__extr @ n ==> test n.
Proof.
  extauto.
Qed.
