(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalFacts : some facts about Decimal numbers *)

Require Import Decimal Arith ZArith.

Variant digits := d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | d9.

Fixpoint to_list (u : uint) : list digits :=
  match u with
  | Nil => nil
  | D0 u => cons d0 (to_list u)
  | D1 u => cons d1 (to_list u)
  | D2 u => cons d2 (to_list u)
  | D3 u => cons d3 (to_list u)
  | D4 u => cons d4 (to_list u)
  | D5 u => cons d5 (to_list u)
  | D6 u => cons d6 (to_list u)
  | D7 u => cons d7 (to_list u)
  | D8 u => cons d8 (to_list u)
  | D9 u => cons d9 (to_list u)
  end.

Fixpoint of_list (l : list digits) : uint :=
  match l with
  | nil => Nil
  | cons d0 l => D0 (of_list l)
  | cons d1 l => D1 (of_list l)
  | cons d2 l => D2 (of_list l)
  | cons d3 l => D3 (of_list l)
  | cons d4 l => D4 (of_list l)
  | cons d5 l => D5 (of_list l)
  | cons d6 l => D6 (of_list l)
  | cons d7 l => D7 (of_list l)
  | cons d8 l => D8 (of_list l)
  | cons d9 l => D9 (of_list l)
  end.

Lemma of_list_to_list u : of_list (to_list u) = u.
Proof. now induction u; [|simpl; rewrite IHu..]. Qed.

Lemma to_list_of_list l : to_list (of_list l) = l.
Proof. now induction l as [|h t IHl]; [|case h; simpl; rewrite IHl]. Qed.

Lemma to_list_inj u u' : to_list u = to_list u' -> u = u'.
Proof.
  now intro H; rewrite <-(of_list_to_list u), <-(of_list_to_list u'), H.
Qed.

Lemma of_list_inj u u' : of_list u = of_list u' -> u = u'.
Proof.
  now intro H; rewrite <-(to_list_of_list u), <-(to_list_of_list u'), H.
Qed.

Lemma nb_digits_spec u : nb_digits u = length (to_list u).
Proof. now induction u; [|simpl; rewrite IHu..]. Qed.

Fixpoint lnzhead l :=
  match l with
  | nil => nil
  | cons d l' =>
    match d with
    | d0 => lnzhead l'
    | _ => l
    end
  end.

Lemma nzhead_spec u : to_list (nzhead u) = lnzhead (to_list u).
Proof. now induction u; [|simpl; rewrite IHu|..]. Qed.

Definition lzero := cons d0 nil.

Definition lunorm l :=
  match lnzhead l with
  | nil => lzero
  | d => d
  end.

Lemma unorm_spec u : to_list (unorm u) = lunorm (to_list u).
Proof. now unfold unorm, lunorm; rewrite <-nzhead_spec; case (nzhead u). Qed.

Lemma revapp_spec d d' :
  to_list (revapp d d') = List.rev_append (to_list d) (to_list d').
Proof. now revert d'; induction d; intro d'; [|simpl; rewrite IHd..]. Qed.

Lemma rev_spec d : to_list (rev d) = List.rev (to_list d).
Proof. now unfold rev; rewrite revapp_spec, List.rev_alt; simpl. Qed.

Lemma app_spec d d' :
  to_list (app d d') = Datatypes.app (to_list d) (to_list d').
Proof.
  unfold app.
  now rewrite revapp_spec, List.rev_append_rev, rev_spec, List.rev_involutive.
Qed.

Definition lnztail l :=
  let fix aux l_rev :=
    match l_rev with
    | cons d0 l_rev => let (r, n) := aux l_rev in pair r (S n)
    | _ => pair l_rev O
    end in
  let (r, n) := aux (List.rev l) in pair (List.rev r) n.

Lemma nztail_spec d :
  let (r, n) := nztail d in
  let (r', n') := lnztail (to_list d) in
  to_list r = r' /\ n = n'.
Proof.
  unfold nztail, lnztail.
  set (f := fix aux d_rev := match d_rev with
            | D0 d_rev => let (r, n) := aux d_rev in (r, S n)
            | _ => (d_rev, 0) end).
  set (f' := fix aux (l_rev : list digits) : list digits * nat :=
             match l_rev with
             | cons d0 l_rev => let (r, n) := aux l_rev in (r, S n)
             | _ => (l_rev, 0)
             end).
  rewrite <-(of_list_to_list (rev d)), rev_spec.
  induction (List.rev _) as [|h t IHl]; [now simpl|].
  case h; simpl; [|now rewrite rev_spec; simpl; rewrite to_list_of_list..].
  now revert IHl; case f; intros r n; case f'; intros r' n' [-> ->].
Qed.

Lemma del_head_spec_0 d : del_head 0 d = d.
Proof. now simpl. Qed.

Lemma del_head_spec_small n d :
  n <= length (to_list d) -> to_list (del_head n d) = List.skipn n (to_list d).
Proof.
  revert d; induction n as [|n IHn]; intro d; [now simpl|].
  now case d; [|intros d' H; apply IHn, le_S_n..].
Qed.

Lemma del_head_spec_large n d : length (to_list d) < n -> del_head n d = zero.
Proof.
  revert d; induction n; intro d; [now case d|].
  now case d; [|intro d'; simpl; intro H; rewrite (IHn _ (proj2 (Nat.succ_lt_mono _ _) H))..].
Qed.

Lemma nb_digits_0 d : nb_digits d = 0 -> d = Nil.
Proof.
  rewrite nb_digits_spec, <-(of_list_to_list d).
  now case (to_list d) as [|h t]; [|rewrite to_list_of_list].
Qed.

Lemma nb_digits_n0 d : nb_digits d <> 0 -> d <> Nil.
Proof. now case d; [|intros u _..]. Qed.

Lemma nb_digits_iter_D0 n d :
  nb_digits (Nat.iter n D0 d) = n + nb_digits d.
Proof. now induction n; simpl; [|rewrite IHn]. Qed.

Lemma length_lnzhead l : length (lnzhead l) <= length l.
Proof. now induction l as [|h t IHl]; [|case h; [apply le_S|..]]. Qed.

Lemma nb_digits_nzhead u : nb_digits (nzhead u) <= nb_digits u.
Proof. now induction u; [|apply le_S|..]. Qed.

Lemma unorm_nzhead u : nzhead u <> Nil -> unorm u = nzhead u.
Proof. now unfold unorm; case nzhead. Qed.

Lemma nb_digits_unorm u : u <> Nil -> nb_digits (unorm u) <= nb_digits u.
Proof.
  intro Hu; case (uint_eq_dec (nzhead u) Nil).
  { unfold unorm; intros ->; simpl.
    now revert Hu; case u; [|intros u' _; apply le_n_S, Nat.le_0_l..]. }
  intro H; rewrite (unorm_nzhead _ H); apply nb_digits_nzhead.
Qed.

Lemma nb_digits_rev d : nb_digits (rev d) = nb_digits d.
Proof. now rewrite !nb_digits_spec, rev_spec, List.length_rev. Qed.

Lemma nb_digits_del_head_sub d n :
  n <= nb_digits d ->
  nb_digits (del_head (nb_digits d - n) d) = n.
Proof.
  rewrite !nb_digits_spec; intro Hn.
  rewrite del_head_spec_small; [|now apply Nat.le_sub_l].
  rewrite List.length_skipn, <-(Nat2Z.id (_ - _)).
  rewrite Nat2Z.inj_sub; [|now apply Nat.le_sub_l].
  rewrite (Nat2Z.inj_sub _ _ Hn).
  rewrite Z.sub_sub_distr, Z.sub_diag; apply Nat2Z.id.
Qed.

Lemma unorm_D0 u : unorm (D0 u) = unorm u.
Proof. reflexivity. Qed.

Lemma app_nil_l d : app Nil d = d.
Proof. now simpl. Qed.

Lemma app_nil_r d : app d Nil = d.
Proof. now apply to_list_inj; rewrite app_spec, List.app_nil_r. Qed.

Lemma abs_app_int d d' : abs (app_int d d') = app (abs d) d'.
Proof. now case d. Qed.

Lemma abs_norm d : abs (norm d) = unorm (abs d).
Proof. now case d as [u|u]; [|simpl; unfold unorm; case nzhead]. Qed.

Lemma iter_D0_nzhead d :
  Nat.iter (nb_digits d - nb_digits (nzhead d)) D0 (nzhead d) = d.
Proof.
  induction d; [now simpl| |now rewrite Nat.sub_diag..].
  simpl nzhead; simpl nb_digits.
  rewrite (Nat.sub_succ_l _ _ (nb_digits_nzhead _)).
  now rewrite <-IHd at 4.
Qed.

Lemma iter_D0_unorm d :
  d <> Nil ->
  Nat.iter (nb_digits d - nb_digits (unorm d)) D0 (unorm d) = d.
Proof.
  case (uint_eq_dec (nzhead d) Nil); intro Hn.
  { unfold unorm; rewrite Hn; simpl; intro H.
    revert H Hn; induction d; [now simpl|intros _|now intros _..].
    case (uint_eq_dec d Nil); simpl; intros H Hn; [now rewrite H|].
    rewrite Nat.sub_0_r, <- (Nat.sub_add 1 (nb_digits d)), Nat.add_comm.
    { now simpl; rewrite IHd. }
    revert H; case d; [now simpl|intros u _; apply le_n_S, Nat.le_0_l..]. }
  intros _; rewrite (unorm_nzhead _ Hn); apply iter_D0_nzhead.
Qed.

Lemma nzhead_app_l d d' :
  nb_digits d' < nb_digits (nzhead (app d d')) ->
  nzhead (app d d') = app (nzhead d) d'.
Proof.
  intro Hl; apply to_list_inj; revert Hl.
  rewrite !nb_digits_spec, app_spec, !nzhead_spec, app_spec.
  induction (to_list d) as [|h t IHl].
  { now simpl; intro H; exfalso; revert H; apply Nat.le_ngt, length_lnzhead. }
  rewrite <-List.app_comm_cons.
  now case h; [simpl; intro Hl; apply IHl|..].
Qed.

Lemma nzhead_app_r d d' :
  nb_digits (nzhead (app d d')) <= nb_digits d' ->
  nzhead (app d d') = nzhead d'.
Proof.
  intro Hl; apply to_list_inj; revert Hl.
  rewrite !nb_digits_spec, !nzhead_spec, app_spec.
  induction (to_list d) as [|h t IHl]; [now simpl|].
  rewrite <-List.app_comm_cons.
  now case h; [| simpl; rewrite List.length_app; intro Hl; exfalso; revert Hl;
    apply Nat.le_ngt, Nat.le_add_l..].
Qed.

Lemma nzhead_app_nil_r d d' : nzhead (app d d') = Nil -> nzhead d' = Nil.
Proof.
now intro H; generalize H; rewrite nzhead_app_r; [|rewrite H; apply Nat.le_0_l].
Qed.

Lemma nzhead_app_nil d d' :
  nb_digits (nzhead (app d d')) <= nb_digits d' -> nzhead d = Nil.
Proof.
  intro H; apply to_list_inj; revert H.
  rewrite !nb_digits_spec, !nzhead_spec, app_spec.
  induction (to_list d) as [|h t IHl]; [now simpl|].
  now case h; [now simpl|..];
    simpl;intro H; exfalso; revert H; apply Nat.le_ngt;
    rewrite List.length_app; apply Nat.le_add_l.
Qed.

Lemma nzhead_app_nil_l d d' : nzhead (app d d') = Nil -> nzhead d = Nil.
Proof.
  intro H; apply to_list_inj; generalize (f_equal to_list H); clear H.
  rewrite !nzhead_spec, app_spec.
  induction (to_list d) as [|h t IHl]; [now simpl|].
  now rewrite <-List.app_comm_cons; case h.
Qed.

Lemma unorm_app_zero d d' :
  nb_digits (unorm (app d d')) <= nb_digits d' -> unorm d = zero.
Proof.
  unfold unorm.
  case (uint_eq_dec (nzhead (app d d')) Nil).
  { now intro Hn; rewrite Hn, (nzhead_app_nil_l _ _ Hn). }
  intro H; fold (unorm (app d d')); rewrite (unorm_nzhead _ H); intro H'.
  case (uint_eq_dec (nzhead d) Nil); [now intros->|].
  intro H''; fold (unorm d); rewrite (unorm_nzhead _ H'').
  exfalso; apply H''; revert H'; apply nzhead_app_nil.
Qed.

Lemma app_int_nil_r d : app_int d Nil = d.
Proof.
  now case d; intro d'; simpl;
    rewrite <-(of_list_to_list (app _ _)), app_spec;
    rewrite List.app_nil_r, of_list_to_list.
Qed.

Lemma unorm_app_l d d' :
  nb_digits d' < nb_digits (unorm (app d d')) ->
  unorm (app d d') = app (unorm d) d'.
Proof.
  case (uint_eq_dec d' Nil); [now intros->; rewrite !app_nil_r|intro Hd'].
  case (uint_eq_dec (nzhead (app d d')) Nil).
  { unfold unorm; intros->; simpl; intro H; exfalso; revert H; apply Nat.le_ngt.
    now revert Hd'; case d'; [|intros d'' _; apply le_n_S, Peano.le_0_n..]. }
  intro Ha; rewrite (unorm_nzhead _ Ha).
  intro Hn; generalize Hn; rewrite (nzhead_app_l _ _ Hn).
  rewrite !nb_digits_spec, app_spec, List.length_app.
  case (uint_eq_dec (nzhead d) Nil).
  { intros->; simpl; intro H; exfalso; revert H; apply Nat.lt_irrefl. }
  now intro H; rewrite (unorm_nzhead _ H).
Qed.

Lemma unorm_app_r d d' :
  nb_digits (unorm (app d d')) <= nb_digits d' ->
  unorm (app d d') = unorm d'.
Proof.
  case (uint_eq_dec (nzhead (app d d')) Nil).
  { now unfold unorm; intro H; rewrite H, (nzhead_app_nil_r _ _ H). }
  intro Ha; rewrite (unorm_nzhead _ Ha).
  case (uint_eq_dec (nzhead d') Nil).
  { now intros H H'; exfalso; apply Ha; rewrite nzhead_app_r. }
  intro Hd'; rewrite (unorm_nzhead _ Hd'); apply nzhead_app_r.
Qed.

Lemma norm_app_int d d' :
  nb_digits d' < nb_digits (unorm (app (abs d) d')) ->
  norm (app_int d d') = app_int (norm d) d'.
Proof.
  case (uint_eq_dec d' Nil); [now intros->; rewrite !app_int_nil_r|intro Hd'].
  case d as [d|d]; [now simpl; intro H; apply f_equal, unorm_app_l|].
  simpl; unfold unorm.
  case (uint_eq_dec (nzhead (app d d')) Nil).
  { intros->; simpl; intro H; exfalso; revert H; apply Nat.le_ngt.
    now revert Hd'; case d'; [|intros d'' _; apply le_n_S, Nat.le_0_l..]. }
  set (m := match nzhead _ with Nil => _ | _ => _ end).
  intro Ha.
  replace m with (nzhead (app d d')).
  2:{ now unfold m; revert Ha; case nzhead. }
  intro Hn; generalize Hn; rewrite (nzhead_app_l _ _ Hn).
  case (uint_eq_dec (app (nzhead d) d') Nil).
  { intros->; simpl; intro H; exfalso; revert H; apply Nat.le_ngt, Nat.le_0_l. }
  clear m; set (m := match app _ _ with Nil => _ | _ => _ end).
  intro Ha'.
  replace m with (Neg (app (nzhead d) d')); [|now unfold m; revert Ha'; case app].
  case (uint_eq_dec (nzhead d) Nil).
  { intros->; simpl; intro H; exfalso; revert H; apply Nat.lt_irrefl. }
  clear m; set (m := match nzhead _ with Nil => _ | _ => _ end).
  intro Hd.
  now replace m with (Neg (nzhead d)); [|unfold m; revert Hd; case nzhead].
Qed.

Lemma del_head_nb_digits d : del_head (nb_digits d) d = Nil.
Proof.
  apply to_list_inj.
  rewrite nb_digits_spec, del_head_spec_small; [|now simpl].
  now rewrite List.skipn_all.
Qed.

Lemma del_tail_nb_digits d : del_tail (nb_digits d) d = Nil.
Proof. now unfold del_tail; rewrite <-nb_digits_rev, del_head_nb_digits. Qed.

Lemma del_head_app n d d' :
  n <= nb_digits d -> del_head n (app d d') = app (del_head n d) d'.
Proof.
  rewrite nb_digits_spec; intro Hn.
  apply to_list_inj.
  rewrite del_head_spec_small.
  2:{ now rewrite app_spec, List.length_app, <- Nat.le_add_r. }
  rewrite !app_spec, (del_head_spec_small _ _ Hn).
  rewrite List.skipn_app.
  now rewrite (proj2 (Nat.sub_0_le _ _) Hn).
Qed.

Lemma del_tail_app n d d' :
  n <= nb_digits d' -> del_tail n (app d d') = app d (del_tail n d').
Proof.
  rewrite nb_digits_spec; intro Hn.
  unfold del_tail.
  rewrite <-(of_list_to_list (rev (app d d'))), rev_spec, app_spec.
  rewrite List.rev_app_distr, <-!rev_spec, <-app_spec, of_list_to_list.
  rewrite del_head_app; [|now rewrite nb_digits_spec, rev_spec, List.length_rev].
  apply to_list_inj.
  rewrite rev_spec, !app_spec, !rev_spec.
  now rewrite List.rev_app_distr, List.rev_involutive.
Qed.

Lemma del_tail_app_int n d d' :
  n <= nb_digits d' -> del_tail_int n (app_int d d') = app_int d (del_tail n d').
Proof. now case d as [d|d]; simpl; intro H; rewrite del_tail_app. Qed.

Lemma app_del_tail_head n (d:uint) :
  n <= nb_digits d -> app (del_tail n d) (del_head (nb_digits d - n) d) = d.
Proof.
  rewrite nb_digits_spec; intro Hn; unfold del_tail.
  rewrite <-(of_list_to_list (app _ _)), app_spec, rev_spec.
  rewrite del_head_spec_small; [|now rewrite rev_spec, List.length_rev].
  rewrite del_head_spec_small; [|now apply Nat.le_sub_l].
  rewrite rev_spec.
  set (n' := _ - n).
  assert (Hn' : n = length (to_list d) - n').
  { now rewrite <- (Nat.add_sub (length (to_list d)) n), Nat.add_comm,
                <- 2 Nat.add_sub_assoc, Nat.sub_diag; trivial. }
  now rewrite Hn', <-List.firstn_skipn_rev, List.firstn_skipn, of_list_to_list.
Qed.

Lemma app_int_del_tail_head n (d:int) :
  n <= nb_digits (abs d) ->
  app_int (del_tail_int n d) (del_head (nb_digits (abs d) - n) (abs d)) = d.
Proof. now case d; clear d; simpl; intros u Hu; rewrite app_del_tail_head. Qed.

Lemma del_head_app_int_exact i f :
  nb_digits f < nb_digits (unorm (app (abs i) f)) ->
  del_head (nb_digits (unorm (app (abs i) f)) - nb_digits f) (unorm (app (abs i) f)) = f.
Proof.
  simpl; intro Hnb; generalize Hnb; rewrite (unorm_app_l _ _ Hnb); clear Hnb.
  replace (_ - _) with (nb_digits (unorm (abs i))).
  - now rewrite del_head_app; [rewrite del_head_nb_digits|].
  - rewrite !nb_digits_spec, app_spec, List.length_app.
    symmetry; apply Nat.add_sub.
Qed.

Lemma del_tail_app_int_exact i f :
  nb_digits f < nb_digits (unorm (app (abs i) f)) ->
  del_tail_int (nb_digits f) (norm (app_int i f)) = norm i.
Proof.
  simpl; intro Hnb.
  rewrite (norm_app_int _ _ Hnb).
  rewrite del_tail_app_int; [|now simpl].
  now rewrite del_tail_nb_digits, app_int_nil_r.
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
  (rewrite IHd;[reflexivity|discriminate]) || (now rewrite ?nzhead_revapp_0).
Qed.

Lemma nzhead_rev d : nztail d <> Nil ->
  nzhead (rev d) = rev (nztail d).
Proof.
  apply nzhead_revapp.
Qed.

Lemma rev_rev d : rev (rev d) = d.
Proof. now apply to_list_inj; rewrite !rev_spec, List.rev_involutive. Qed.

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

Lemma unorm_iter_D0 n u : unorm (Nat.iter n D0 u) = unorm u.
Proof. now induction n. Qed.

Lemma del_head_nonnil n u :
  n < nb_digits u -> del_head n u <> Nil.
Proof.
  now revert n; induction u; intro n;
    [|case n; [|intro n'; simpl; intro H; apply IHu, Nat.succ_lt_mono]..].
Qed.

Lemma del_tail_nonnil n u :
  n < nb_digits u -> del_tail n u <> Nil.
Proof.
  unfold del_tail.
  rewrite <-nb_digits_rev.
  generalize (rev u); clear u; intro u.
  intros Hu H.
  generalize (rev_nil_inv _ H); clear H.
  now apply del_head_nonnil.
Qed.

Lemma nzhead_involutive d : nzhead (nzhead d) = nzhead d.
Proof.
  now induction d.
Qed.

Lemma nztail_involutive d : nztail (nztail d) = nztail d.
Proof.
  rewrite <-(rev_rev (nztail _)), <-(rev_rev (nztail d)), <-(rev_rev d).
  now rewrite !rev_nztail_rev, nzhead_involutive.
Qed.

Lemma unorm_involutive d : unorm (unorm d) = unorm d.
Proof.
  unfold unorm.
  destruct (nzhead d) eqn:E; trivial.
  destruct (nzhead_nonzero _ _ E).
Qed.

Lemma norm_involutive d : norm (norm d) = norm d.
Proof.
  unfold norm.
  destruct d.
  - f_equal. apply unorm_involutive.
  - destruct (nzhead d) eqn:E; auto.
    destruct (nzhead_nonzero _ _ E).
Qed.

Lemma lnzhead_neq_d0_head l l' : ~(lnzhead l = cons d0 l').
Proof. now induction l as [|h t Il]; [|case h]. Qed.

Lemma lnzhead_head_nd0 h t : h <> d0 -> lnzhead (cons h t) = cons h t.
Proof. now case h. Qed.

Lemma nzhead_del_tail_nzhead_eq n u :
  nzhead u = u ->
  n < nb_digits u ->
  nzhead (del_tail n u) = del_tail n u.
Proof.
  rewrite nb_digits_spec, <-List.length_rev.
  intros Hu Hn.
  apply to_list_inj; unfold del_tail.
  rewrite nzhead_spec, rev_spec.
  rewrite del_head_spec_small; [|now rewrite rev_spec; apply Nat.lt_le_incl].
  rewrite rev_spec.
  rewrite List.skipn_rev, List.rev_involutive.
  generalize (f_equal to_list Hu) Hn; rewrite nzhead_spec; intro Hu'.
  case (to_list u) as [|h t].
  { simpl; intro H; exfalso; revert H; apply Nat.le_ngt, Nat.le_0_l. }
  intro Hn'; generalize (Nat.sub_gt _ _ Hn'); rewrite List.length_rev.
  case (_ - _); [now simpl|]; intros n' _.
  rewrite List.firstn_cons, lnzhead_head_nd0; [now simpl|].
  intro Hh; revert Hu'; rewrite Hh; apply lnzhead_neq_d0_head.
Qed.

Lemma nzhead_del_tail_nzhead n u :
  n < nb_digits (nzhead u) ->
  nzhead (del_tail n (nzhead u)) = del_tail n (nzhead u).
Proof. apply nzhead_del_tail_nzhead_eq, nzhead_involutive. Qed.

Lemma unorm_del_tail_unorm n u :
  n < nb_digits (unorm u) ->
  unorm (del_tail n (unorm u)) = del_tail n (unorm u).
Proof.
  case (uint_eq_dec (nzhead u) Nil).
  - unfold unorm; intros->; case n; [now simpl|]; intro n'.
    now simpl; intro H; exfalso; generalize (proj2 (Nat.succ_lt_mono _ _) H).
  - unfold unorm.
    set (m := match nzhead u with Nil => zero | _ => _ end).
    intros H.
    replace m with (nzhead u).
    + intros H'.
      rewrite (nzhead_del_tail_nzhead _ _ H').
      now generalize (del_tail_nonnil _ _ H'); case del_tail.
    + now unfold m; revert H; case nzhead.
Qed.

Lemma norm_del_tail_int_norm n d :
  n < nb_digits (match norm d with Pos d | Neg d => d end) ->
  norm (del_tail_int n (norm d)) = del_tail_int n (norm d).
Proof.
  case d; clear d; intros u; simpl.
  - now intro H; simpl; rewrite unorm_del_tail_unorm.
  - case (uint_eq_dec (nzhead u) Nil); intro Hu.
    + now rewrite Hu; case n; [|intros n' Hn'; generalize (proj2 (Nat.succ_lt_mono _ _) Hn')].
    + set (m := match nzhead u with Nil => Pos zero | _ => _ end).
      replace m with (Neg (nzhead u)); [|now unfold m; revert Hu; case nzhead].
      unfold del_tail_int.
      clear m Hu.
      simpl.
      intro H; generalize (del_tail_nonnil _ _ H).
      rewrite (nzhead_del_tail_nzhead _ _ H).
      now case del_tail.
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
  rewrite nztail_involutive.
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
       rewrite nzhead_revapp; rewrite nztail_involutive; [|rewrite Hd'']..].
Qed.

Lemma unorm_app_l_nil d d' : nzhead d = Nil -> unorm (app d d') = unorm d'.
Proof.
  now unfold unorm; rewrite <-nzhead_app_nzhead; intros->; rewrite app_nil_l.
Qed.
