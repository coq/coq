(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalFacts : some facts about Decimal numbers *)

Require Import Decimal.

Lemma uint_dec (d d' : uint) : { d = d' } + { d <> d' }.
Proof.
 decide equality.
Defined.

Lemma rev_revapp d d' :
 rev (revapp d d') = revapp d' d.
Proof.
 revert d'. induction d; simpl; intros; now rewrite ?IHd.
Qed.

Lemma rev_rev d : rev (rev d) = d.
Proof.
 apply rev_revapp.
Qed.

(** Normalization on little-endian numbers *)

Fixpoint nztail d :=
 match d with
 | Nil => Nil
 | D0 d => match nztail d with Nil => Nil | d' => D0 d' end
 | D1 d => D1 (nztail d)
 | D2 d => D2 (nztail d)
 | D3 d => D3 (nztail d)
 | D4 d => D4 (nztail d)
 | D5 d => D5 (nztail d)
 | D6 d => D6 (nztail d)
 | D7 d => D7 (nztail d)
 | D8 d => D8 (nztail d)
 | D9 d => D9 (nztail d)
 end.

Definition lnorm d :=
 match nztail d with
 | Nil => zero
 | d => d
 end.

Lemma nzhead_revapp_0 d d' : nztail d = Nil ->
 nzhead (revapp d d') = nzhead d'.
Proof.
 revert d'. induction d; intros d' [=]; simpl; trivial.
 destruct (nztail d); now rewrite IHd.
Qed.

Lemma nzhead_revapp d d' : nztail d <> Nil ->
 nzhead (revapp d d') = revapp (nztail d) d'.
Proof.
 revert d'.
 induction d; intros d' H; simpl in *;
 try destruct (nztail d) eqn:E;
  (now rewrite ?nzhead_revapp_0) || (now rewrite IHd).
Qed.

Lemma nzhead_rev d : nztail d <> Nil ->
 nzhead (rev d) = rev (nztail d).
Proof.
 apply nzhead_revapp.
Qed.

Lemma rev_nztail_rev d :
  rev (nztail (rev d)) = nzhead d.
Proof.
 destruct (uint_dec (nztail (rev d)) Nil) as [H|H].
 - rewrite H. unfold rev; simpl.
   rewrite <- (rev_rev d). symmetry.
   now apply nzhead_revapp_0.
 - now rewrite <- nzhead_rev, rev_rev.
Qed.

Lemma revapp_nil_inv d d' : revapp d d' = Nil -> d = Nil /\ d' = Nil.
Proof.
 revert d'.
 induction d; simpl; intros d' H; auto; now apply IHd in H.
Qed.

Lemma rev_nil_inv d : rev d = Nil -> d = Nil.
Proof.
 apply revapp_nil_inv.
Qed.

Lemma rev_lnorm_rev d :
  rev (lnorm (rev d)) = unorm d.
Proof.
 unfold unorm, lnorm.
 rewrite <- rev_nztail_rev.
 destruct nztail; simpl; trivial;
  destruct rev eqn:E; trivial; now apply rev_nil_inv in E.
Qed.

Lemma nzhead_nonzero d d' : nzhead d <> D0 d'.
Proof.
 induction d; easy.
Qed.

Lemma unorm_0 d : unorm d = zero <-> nzhead d = Nil.
Proof.
 unfold unorm. split.
 - generalize (nzhead_nonzero d).
   destruct nzhead; intros H [=]; trivial. now destruct (H u).
 - now intros ->.
Qed.

Lemma unorm_nonnil d : unorm d <> Nil.
Proof.
 unfold unorm. now destruct nzhead.
Qed.

Lemma nzhead_invol d : nzhead (nzhead d) = nzhead d.
Proof.
 now induction d.
Qed.

Lemma unorm_invol d : unorm (unorm d) = unorm d.
Proof.
 unfold unorm.
 destruct (nzhead d) eqn:E; trivial.
 destruct (nzhead_nonzero _ _ E).
Qed.

Lemma norm_invol d : norm (norm d) = norm d.
Proof.
 unfold norm.
 destruct d.
 - f_equal. apply unorm_invol.
 - destruct (nzhead d) eqn:E; auto.
   destruct (nzhead_nonzero _ _ E).
Qed.
