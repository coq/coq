(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalFacts : some facts about Hexadecimal numbers *)

Require Import Hexadecimal Arith.

Scheme Equality for uint.

Scheme Equality for int.

Lemma rev_revapp d d' :
  rev (revapp d d') = revapp d' d.
Proof.
  revert d'. induction d; simpl; intros; now rewrite ?IHd.
Qed.

Lemma rev_rev d : rev (rev d) = d.
Proof.
  apply rev_revapp.
Qed.

Lemma revapp_rev_nil d : revapp (rev d) Nil = d.
Proof. now fold (rev (rev d)); rewrite rev_rev. Qed.

Lemma app_nil_r d : app d Nil = d.
Proof. now unfold app; rewrite revapp_rev_nil. Qed.

Lemma app_int_nil_r d : app_int d Nil = d.
Proof. now case d; intro d'; simpl; rewrite app_nil_r. Qed.

Lemma revapp_revapp_1 d d' d'' :
  nb_digits d <= 1 ->
  revapp (revapp d d') d'' = revapp d' (revapp d d'').
Proof.
  now case d; clear d; intro d;
    [|case d; clear d; intro d;
      [|simpl; case nb_digits; [|intros n]; intros Hn; exfalso;
        [apply (Nat.nle_succ_diag_l _ Hn)|
         apply (Nat.nle_succ_0 _ (le_S_n _ _ Hn))]..]..].
Qed.

Lemma nb_digits_pos d : d <> Nil -> 0 < nb_digits d.
Proof. now case d; [|intros d' _; apply Nat.lt_0_succ..]. Qed.

Lemma nb_digits_revapp d d' :
  nb_digits (revapp d d') = nb_digits d + nb_digits d'.
Proof.
  now revert d'; induction d; [|intro d'; simpl; rewrite IHd; simpl..].
Qed.

Lemma nb_digits_rev u : nb_digits (rev u) = nb_digits u.
Proof. now unfold rev; rewrite nb_digits_revapp. Qed.

Lemma nb_digits_nzhead u : nb_digits (nzhead u) <= nb_digits u.
Proof. now induction u; [|apply le_S|..]. Qed.

Lemma nb_digits_iter_D0 n d :
  nb_digits (Nat.iter n D0 d) = n + nb_digits d.
Proof. now induction n; simpl; [|rewrite IHn]. Qed.

Fixpoint nth n u :=
  match n with
  | O =>
    match u with
    | Nil => Nil
    | D0 d => D0 Nil
    | D1 d => D1 Nil
    | D2 d => D2 Nil
    | D3 d => D3 Nil
    | D4 d => D4 Nil
    | D5 d => D5 Nil
    | D6 d => D6 Nil
    | D7 d => D7 Nil
    | D8 d => D8 Nil
    | D9 d => D9 Nil
    | Da d => Da Nil
    | Db d => Db Nil
    | Dc d => Dc Nil
    | Dd d => Dd Nil
    | De d => De Nil
    | Df d => Df Nil
    end
  | S n =>
    match u with
    | Nil => Nil
    | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d
    | Da d | Db d | Dc d | Dd d | De d | Df d =>
      nth n d
    end
  end.

Lemma nb_digits_nth n u : nb_digits (nth n u) <= 1.
Proof.
  revert u; induction n.
  - now intro u; case u; [apply Nat.le_0_1|..].
  - intro u; case u; [apply Nat.le_0_1|intro u'; apply IHn..].
Qed.

Lemma nth_revapp_r n d d' :
  nb_digits d <= n ->
  nth n (revapp d d') = nth (n - nb_digits d) d'.
Proof.
  revert d d'; induction n; intro d.
  - now case d; intro d';
      [case d'|intros d'' H; exfalso; revert H; apply Nat.nle_succ_0..].
  - now induction d;
      [intro d'; case d'|
       intros d' H;
       simpl revapp; rewrite IHd; [|now apply le_Sn_le];
       rewrite Nat.sub_succ_l; [|now apply le_S_n];
       simpl; rewrite <-(IHn _ _ (le_S_n _ _ H))..].
Qed.

Lemma nth_revapp_l n d d' :
  n < nb_digits d ->
  nth n (revapp d d') = nth (nb_digits d - n - 1) d.
Proof.
  revert d d'; induction n; intro d.
  - rewrite Nat.sub_0_r.
    now induction d;
      [|intros d' _; simpl revapp;
       revert IHd; case d; clear d; [|intro d..]; intro IHd;
       [|rewrite IHd; [simpl nb_digits; rewrite (Nat.sub_succ_l _ (S _))|];
         [|apply le_n_S, Nat.le_0_l..]..]..].
  - now induction d;
      [|intros d' H;
        simpl revapp; simpl nb_digits;
        simpl in H; generalize (lt_S_n _ _ H); clear H; intro H;
        case (le_lt_eq_dec _ _ H); clear H; intro H;
        [rewrite (IHd _ H), Nat.sub_succ_l;
         [rewrite Nat.sub_succ_l; [|apply Nat.le_add_le_sub_r]|
          apply le_Sn_le]|
         rewrite nth_revapp_r; rewrite <-H;
         [rewrite Nat.sub_succ, Nat.sub_succ_l; [rewrite !Nat.sub_diag|]|]]..].
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
  | Da d => Da (nztail d)
  | Db d => Db (nztail d)
  | Dc d => Dc (nztail d)
  | Dd d => Dd (nztail d)
  | De d => De (nztail d)
  | Df d => Df (nztail d)
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
  destruct (uint_eq_dec (nztail (rev d)) Nil) as [H|H].
  - rewrite H. unfold rev; simpl.
    rewrite <- (rev_rev d). symmetry.
    now apply nzhead_revapp_0.
  - now rewrite <- nzhead_rev, rev_rev.
Qed.

Lemma nzhead_D0 u : nzhead (D0 u) = nzhead u.
Proof. reflexivity. Qed.

Lemma nzhead_iter_D0 n u : nzhead (Nat.iter n D0 u) = nzhead u.
Proof. now induction n. Qed.

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

Lemma unorm_D0 u : unorm (D0 u) = unorm u.
Proof. reflexivity. Qed.

Lemma unorm_iter_D0 n u : unorm (Nat.iter n D0 u) = unorm u.
Proof. now induction n. Qed.

Lemma nb_digits_unorm u :
  u <> Nil -> nb_digits (unorm u) <= nb_digits u.
Proof.
  case u; clear u; [now simpl|intro u..]; [|now simpl..].
  intros _; unfold unorm.
  case_eq (nzhead (D0 u)); [|now intros u' <-; apply nb_digits_nzhead..].
  intros _; apply le_n_S, Nat.le_0_l.
Qed.

Lemma nzhead_invol d : nzhead (nzhead d) = nzhead d.
Proof.
  now induction d.
Qed.

Lemma nztail_invol d : nztail (nztail d) = nztail d.
Proof.
  rewrite <-(rev_rev (nztail _)), <-(rev_rev (nztail d)), <-(rev_rev d).
  now rewrite !rev_nztail_rev, nzhead_invol.
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

Lemma nzhead_app_nzhead d d' :
  nzhead (app (nzhead d) d') = nzhead (app d d').
Proof.
  unfold app.
  rewrite <-(rev_nztail_rev d), rev_rev.
  generalize (rev d); clear d; intro d.
  generalize (nzhead_revapp_0 d d').
  generalize (nzhead_revapp d d').
  generalize (nzhead_revapp_0 (nztail d) d').
  generalize (nzhead_revapp (nztail d) d').
  rewrite nztail_invol.
  now case nztail;
    [intros _ H _ H'; rewrite (H eq_refl), (H' eq_refl)
    |intros d'' H _ H' _; rewrite H; [rewrite H'|]..].
Qed.

Lemma unorm_app_unorm d d' :
  unorm (app (unorm d) d') = unorm (app d d').
Proof.
  unfold unorm.
  rewrite <-(nzhead_app_nzhead d d').
  now case (nzhead d).
Qed.

Lemma norm_app_int_norm d d' :
  unorm d' = zero ->
  norm (app_int (norm d) d') = norm (app_int d d').
Proof.
  case d; clear d; intro d; simpl.
  - now rewrite unorm_app_unorm.
  - unfold app_int, app.
    rewrite unorm_0; intro Hd'.
    rewrite <-rev_nztail_rev.
    generalize (nzhead_revapp (rev d) d').
    generalize (nzhead_revapp_0 (rev d) d').
    now case_eq (nztail (rev d));
      [intros Hd'' H _; rewrite (H eq_refl); simpl;
       unfold unorm; simpl; rewrite Hd'
      |intros d'' Hd'' _ H; rewrite H; clear H; [|now simpl];
       set (r := rev _);
       set (m := match r with Nil => Pos zero | _ => _ end);
       assert (H' : m = Neg r);
       [now unfold m; case_eq r; unfold r;
        [intro H''; generalize (rev_nil_inv _ H'')|..]
       |rewrite H'; unfold r; clear m r H'];
       unfold norm;
       rewrite rev_rev, <-Hd'';
       rewrite nzhead_revapp; rewrite nztail_invol; [|rewrite Hd'']..].
Qed.
