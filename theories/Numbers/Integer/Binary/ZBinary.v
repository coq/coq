Require Import ZTimesOrder.
Require Import ZArith.

Open Local Scope Z_scope.
Module Export ZBinDomain <: ZDomainSignature.
Delimit Scope IntScope with Int.
(* Is this really necessary? Without it, applying ZDomainProperties
functor to this module produces an error since the functor opens the
scope. *)

Definition Z := Z.
Definition E := (@eq Z).
Definition e := Zeq_bool.

Theorem E_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e, Zeq_bool; split; intro H.
rewrite H; now rewrite Zcompare_refl.
rewrite eq_true_unfold_pos in H.
assert (H1 : (x ?= y) = Eq).
case_eq (x ?= y); intro H1; rewrite H1 in H; simpl in H;
[reflexivity | discriminate H | discriminate H].
now apply Zcompare_Eq_eq.
Qed.

Theorem E_equiv : equiv Z E.
Proof.
apply eq_equiv with (A := Z). (* It does not work without "with (A := Z)" though it looks like it should *)
Qed.

Add Relation Z E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

End ZBinDomain.

Module Export ZBinInt <: IntSignature.
Module Export ZDomainModule := ZBinDomain.

Definition O := 0.
Definition S := Zsucc'.
Definition P := Zpred'.

Add Morphism S with signature E ==> E as S_wd.
Proof.
intros; unfold E; congruence.
Qed.

Add Morphism P with signature E ==> E as P_wd.
Proof.
intros; unfold E; congruence.
Qed.

Theorem S_inj : forall x y : Z, S x = S y -> x = y.
Proof.
exact Zsucc'_inj.
Qed.

Theorem S_P : forall x : Z, S (P x) = x.
Proof.
exact Zsucc'_pred'.
Qed.

Theorem induction :
  forall Q : Z -> Prop,
    pred_wd E Q -> Q 0 ->
    (forall x, Q x -> Q (S x)) ->
    (forall x, Q x -> Q (P x)) -> forall x, Q x.
Proof.
intros; now apply Zind.
Qed.

End ZBinInt.

Module Export ZBinPlus <: ZPlusSignature.
Module Export IntModule := ZBinInt.

Definition plus := Zplus.
Definition minus := Zminus.
Definition uminus := Zopp.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
intros; congruence.
Qed.

Add Morphism minus with signature E ==> E ==> E as minus_wd.
Proof.
intros; congruence.
Qed.

Add Morphism uminus with signature E ==> E as uminus_wd.
Proof.
intros; congruence.
Qed.

Theorem plus_0 : forall n, 0 + n = n.
Proof.
exact Zplus_0_l.
Qed.

Theorem plus_S : forall n m, (S n) + m = S (n + m).
Proof.
intros; do 2 rewrite <- Zsucc_succ'; apply Zplus_succ_l.
Qed.

Theorem minus_0 : forall n, n - 0 = n.
Proof.
exact Zminus_0_r.
Qed.

Theorem minus_S : forall n m, n - (S m) = P (n - m).
Proof.
intros; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred';
apply Zminus_succ_r.
Qed.

Theorem uminus_0 : - 0 = 0.
Proof.
reflexivity.
Qed.

Theorem uminus_S : forall n, - (S n) = P (- n).
Admitted.

End ZBinPlus.

Module Export ZBinTimes <: ZTimesSignature.
Module Export ZPlusModule := ZBinPlus.

Definition times := Zmult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
congruence.
Qed.

Theorem times_0 : forall n, n * 0 = 0.
Proof.
exact Zmult_0_r.
Qed.

Theorem times_S : forall n m, n * (S m) = n * m + n.
Proof.
intros; rewrite <- Zsucc_succ'; apply Zmult_succ_r.
Qed.

End ZBinTimes.

Module Export ZBinOrder <: ZOrderSignature.
Module Export IntModule := ZBinInt.

Definition lt := Zlt_bool.
Definition le := Zle_bool.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
congruence.
Qed.

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
congruence.
Qed.

Theorem le_lt : forall n m, le n m <-> lt n m \/ n = m.
Proof.
intros; unfold lt, le, Zlt_bool, Zle_bool.
case_eq (n ?= m); intro H.
apply Zcompare_Eq_eq in H; rewrite H; now split; intro; [right |].
now split; intro; [left |].
split; intro H1. now idtac.
destruct H1 as [H1 | H1].
assumption. unfold E in H1; rewrite H1 in H. now rewrite Zcompare_refl in H.
Qed.

Theorem lt_irr : forall n, ~ (lt n n).
Proof.
intro n; rewrite eq_true_unfold_pos; intro H.
assert (H1 : (Zlt n n)).
change (if true then (Zlt n n) else (Zge n n)). rewrite <- H.
unfold lt. apply Zlt_cases.
false_hyp H1 Zlt_irrefl.
Qed.

Theorem lt_S : forall n m, lt n (S m) <-> le n m.
Proof.
intros; unfold lt, le, S; do 2 rewrite eq_true_unfold_pos.
rewrite <- Zsucc_succ'; rewrite <- Zlt_is_lt_bool; rewrite <- Zle_is_le_bool.
split; intro; [now apply Zlt_succ_le | now apply Zle_lt_succ].
Qed.

End ZBinOrder.

Module Export ZTimesOrderPropertiesModule :=
  ZTimesOrderProperties ZBinTimes ZBinOrder.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
