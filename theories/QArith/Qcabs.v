(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * An absolute value for normalized rational numbers. *)

(** Contributed by Cédric Auger *)

Require Import Qabs Qcanon.

Lemma Qred_abs (x : Q) : Qred (Qabs x) = Qabs (Qred x).
Proof.
  destruct x as [[|a|a] d]; simpl; auto;
  destruct (Pos.ggcd a d) as [x [y z]]; simpl; auto.
Qed.

Lemma Qcabs_canon (x : Q) : Qred x = x -> Qred (Qabs x) = Qabs x.
Proof. intros H; now rewrite (Qred_abs x), H. Qed.

Definition Qcabs (x:Qc) : Qc := {| canon := Qcabs_canon x (canon x) |}.
Notation "[ q ]" := (Qcabs q) : Qc_scope.

Ltac Qc_unfolds :=
  unfold Qcabs, Qcminus, Qcopp, Qcplus, Qcmult, Qcle, Q2Qc, this.

Lemma Qcabs_case (x:Qc) (P : Qc -> Type) :
  (0 <= x -> P x) -> (x <= 0 -> P (- x)) -> P [x].
Proof.
  intros A B.
  apply (Qabs_case x (fun x => forall Hx, P {|this:=x;canon:=Hx|})).
  intros; case (Qc_decomp x {|canon:=Hx|}); auto.
  intros; case (Qc_decomp (-x) {|canon:=Hx|}); auto.
Qed.

Lemma Qcabs_pos x : 0 <= x -> [x] = x.
Proof.
  intro Hx; apply Qc_decomp; Qc_unfolds; fold (this x).
  set (K := canon [x]); simpl in K; case K; clear K.
  set (a := x) at 1; case (canon x); subst a; apply Qred_complete.
  now apply Qabs_pos.
Qed.

Lemma Qcabs_neg x : x <= 0 -> [x] = - x.
Proof.
  intro Hx; apply Qc_decomp; Qc_unfolds; fold (this x).
  set (K := canon [x]); simpl in K; case K; clear K.
  now apply Qred_complete; apply Qabs_neg.
Qed.

Lemma Qcabs_nonneg x : 0 <= [x].
Proof. intros; apply Qabs_nonneg. Qed.

Lemma Qcabs_opp x : [(-x)] = [x].
Proof.
  apply Qc_decomp; Qc_unfolds; fold (this x).
  set (K := canon [x]); simpl in K; case K; clear K.
  case Qred_abs; apply Qred_complete; apply Qabs_opp.
Qed.

Lemma Qcabs_triangle x y : [x+y] <= [x] + [y].
Proof.
  Qc_unfolds; case Qred_abs; rewrite !Qred_le; apply Qabs_triangle.
Qed.

Lemma Qcabs_Qcmult x y : [x*y] = [x]*[y].
Proof.
  apply Qc_decomp; Qc_unfolds; fold (this x) (this y); case Qred_abs.
  apply Qred_complete; apply Qabs_Qmult.
Qed.

Lemma Qcabs_Qcminus x y: [x-y] = [y-x].
Proof.
  apply Qc_decomp; Qc_unfolds; fold (this x) (this y) (this (-x)) (this (-y)).
  set (a := x) at 2; case (canon x); subst a.
  set (a := y) at 1; case (canon y); subst a.
  rewrite !Qred_opp; fold (Qred x - Qred y)%Q (Qred y - Qred x)%Q.
  repeat case Qred_abs; f_equal; apply Qabs_Qminus.
Qed.

Lemma Qcle_Qcabs x : x <= [x].
Proof. apply Qle_Qabs. Qed.

Lemma Qcabs_triangle_reverse x y : [x] - [y] <= [x - y].
Proof.
  unfold Qcle, Qcabs, Qcminus, Qcplus, Qcopp, Q2Qc, this;
  fold (this x) (this y) (this (-x)) (this (-y)).
  case Qred_abs; rewrite !Qred_le, !Qred_opp, Qred_abs.
  apply Qabs_triangle_reverse.
Qed.

Lemma Qcabs_Qcle_condition x y : [x] <= y <-> -y <= x <= y.
Proof.
  Qc_unfolds; fold (this x) (this y).
  destruct (Qabs_Qle_condition x y) as [A B].
  split; intros H.
  + destruct (A H) as [X Y]; split; auto.
    now case (canon x); apply Qred_le.
  + destruct H as [X Y]; apply B; split; auto.
    now case (canon y); case Qred_opp.
Qed.

Lemma Qcabs_diff_Qcle_condition x y r : [x-y] <= r <-> x - r <= y <= x + r.
Proof.
  Qc_unfolds; fold (this x) (this y) (this r).
  case Qred_abs; repeat rewrite Qred_opp.
  set (a := y) at 1; case (canon y); subst a.
  set (a := r) at 2; case (canon r); subst a.
  set (a := Qred r) at 2 3;
  assert (K := canon (Q2Qc r)); simpl in K; case K; clear K; subst a.
  set (a := Qred y) at 1;
  assert (K := canon (Q2Qc y)); simpl in K; case K; clear K; subst a.
  fold (x - Qred y)%Q (x - Qred r)%Q.
  destruct (Qabs_diff_Qle_condition x (Qred y) (Qred r)) as [A B].
  split.
  + clear B; rewrite !Qred_le. auto.
  + clear A; rewrite !Qred_le. auto.
Qed.

Lemma Qcabs_null x : [x] = 0 -> x = 0.
Proof.
  intros H.
  destruct (proj1 (Qcabs_Qcle_condition x 0)) as [A B].
  + rewrite H; apply Qcle_refl.
  + apply Qcle_antisym; auto.
Qed.
