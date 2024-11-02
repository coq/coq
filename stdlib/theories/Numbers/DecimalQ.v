(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalQ

    Proofs that conversions between decimal numbers and [Q]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN DecimalZ QArith.
Import PeanoNat.

Lemma of_IQmake_to_decimal num den :
  match IQmake_to_decimal num den with
  | None => True
  | Some (DecimalExp _ _ _) => False
  | Some (Decimal i f) => of_decimal (Decimal i f) = IQmake (IZ_of_Z num) den
  end.
Proof.
  unfold IQmake_to_decimal.
  generalize (Unsigned.nztail_to_uint den).
  case Decimal.nztail; intros den' e_den'.
  case den'; [now simpl|now simpl| |now simpl..]; clear den'; intro den'.
  case den'; [ |now simpl..]; clear den'.
  case e_den' as [|e_den']; simpl; injection 1 as ->.
  { now unfold of_decimal; simpl; rewrite app_int_nil_r, DecimalZ.of_to. }
  replace (10 ^ _)%positive with (Nat.iter (S e_den') (Pos.mul 10) 1%positive).
  2:{ induction e_den' as [|n IHn]; [now simpl| ].
    now rewrite SuccNat2Pos.inj_succ, Pos.pow_succ_r, <-IHn. }
  case Nat.ltb_spec; intro He_den'.
  - unfold of_decimal; simpl.
    rewrite app_int_del_tail_head; [|now apply Nat.lt_le_incl].
    rewrite DecimalZ.of_to.
    now rewrite nb_digits_del_head_sub; [|now apply Nat.lt_le_incl].
  - unfold of_decimal; simpl.
    rewrite nb_digits_iter_D0.
    apply f_equal2.
    + apply f_equal, DecimalZ.to_int_inj.
      rewrite DecimalZ.to_of.
      rewrite <-(DecimalZ.of_to num), DecimalZ.to_of.
      case (Z.to_int num); clear He_den' num; intro num; simpl.
      * unfold app; simpl.
        now rewrite unorm_D0, unorm_iter_D0, unorm_involutive.
      * case (uint_eq_dec (nzhead num) Nil); [|intro Hn].
        { intros->; simpl; unfold app; simpl.
          now rewrite unorm_D0, unorm_iter_D0. }
        replace (match nzhead num with Nil => _ | _ => _ end)
          with (Neg (nzhead num)); [|now revert Hn; case nzhead].
        simpl.
        rewrite nzhead_iter_D0, nzhead_involutive.
        now revert Hn; case nzhead.
    + revert He_den'; case nb_digits as [|n]; [now simpl; rewrite Nat.add_0_r|].
      intro Hn.
      rewrite Nat.add_succ_r, Nat.sub_add; [|apply le_S_n]; auto.
Qed.

Lemma IZ_of_Z_IZ_to_Z z z' : IZ_to_Z z = Some z' -> IZ_of_Z z' = z.
Proof. now case z as [| |p|p]; [| injection 1 as <- ..]. Qed.

Lemma of_IQmake_to_decimal' num den :
  match IQmake_to_decimal' num den with
  | None => True
  | Some (DecimalExp _ _ _) => False
  | Some (Decimal i f) => of_decimal (Decimal i f) = IQmake num den
  end.
Proof.
  unfold IQmake_to_decimal'.
  case_eq (IZ_to_Z num); [intros num' Hnum'|now simpl].
  generalize (of_IQmake_to_decimal num' den).
  case IQmake_to_decimal as [d|]; [|now simpl].
  case d as [i f|]; [|now simpl].
  now rewrite (IZ_of_Z_IZ_to_Z _ _ Hnum').
Qed.

Lemma of_to (q:IQ) : forall d, to_decimal q = Some d -> of_decimal d = q.
Proof.
  intro d.
  case q as [num den|q q'|q q']; simpl.
  - generalize (of_IQmake_to_decimal' num den).
    case IQmake_to_decimal' as [d'|]; [|now simpl].
    case d' as [i f|]; [|now simpl].
    now intros H; injection 1 as <-.
  - case q as [num den| |]; [|now simpl..].
    case q' as [num' den'| |]; [|now simpl..].
    case num' as [z p| | |]; [|now simpl..].
    case (Z.eq_dec z 10); [intros->|].
    2:{ case z; [now simpl| |now simpl]; intro pz'.
      case pz'; [intros d0..| ]; [now simpl| |now simpl].
      case d0; [intros d1..| ]; [ |now simpl..].
      case d1; [intros d2..| ]; [now simpl| |now simpl].
      now case d2. }
    case (Pos.eq_dec den' 1%positive); [intros->|now case den'].
    generalize (of_IQmake_to_decimal' num den).
    case IQmake_to_decimal' as [d'|]; [|now simpl].
    case d' as [i f|]; [|now simpl].
    intros <-; clear num den.
    injection 1 as <-.
    unfold of_decimal; simpl.
    now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
  - case q as [num den| |]; [|now simpl..].
    case q' as [num' den'| |]; [|now simpl..].
    case num' as [z p| | |]; [|now simpl..].
    case (Z.eq_dec z 10); [intros->|].
    2:{ case z; [now simpl| |now simpl]; intro pz'.
      case pz'; [intros d0..| ]; [now simpl| |now simpl].
      case d0; [intros d1..| ]; [ |now simpl..].
      case d1; [intros d2..| ]; [now simpl| |now simpl].
      now case d2. }
    case (Pos.eq_dec den' 1%positive); [intros->|now case den'].
    generalize (of_IQmake_to_decimal' num den).
    case IQmake_to_decimal' as [d'|]; [|now simpl].
    case d' as [i f|]; [|now simpl].
    intros <-; clear num den.
    injection 1 as <-.
    unfold of_decimal; simpl.
    now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
Qed.

Definition dnorm (d:decimal) : decimal :=
  let norm_i i f :=
    match i with
    | Pos i => Pos (unorm i)
    | Neg i => match nzhead (app i f) with Nil => Pos zero | _ => Neg (unorm i) end
    end in
  match d with
  | Decimal i f => Decimal (norm_i i f) f
  | DecimalExp i f e =>
    match norm e with
    | Pos zero => Decimal (norm_i i f) f
    | e => DecimalExp (norm_i i f) f e
    end
  end.

Lemma dnorm_spec_i d :
  let (i, f) :=
    match d with Decimal i f => (i, f) | DecimalExp i f _ => (i, f) end in
  let i' := match dnorm d with Decimal i _ => i | DecimalExp i _ _ => i end in
  match i with
  | Pos i => i' = Pos (unorm i)
  | Neg i =>
    (i' = Neg (unorm i) /\ (nzhead i <> Nil \/ nzhead f <> Nil))
    \/ (i' = Pos zero /\ (nzhead i = Nil /\ nzhead f = Nil))
  end.
Proof.
  case d as [i f|i f e]; case i as [i|i].
  - now simpl.
  - simpl; case (uint_eq_dec (nzhead (app i f)) Nil); intro Ha.
    + rewrite Ha; right; split; [now simpl|split].
      * now unfold unorm; rewrite (nzhead_app_nil_l _ _ Ha).
      * now unfold unorm; rewrite (nzhead_app_nil_r _ _ Ha).
    + left; split; [now revert Ha; case nzhead|].
      case (uint_eq_dec (nzhead i) Nil).
      * intro Hi; right; intro Hf; apply Ha.
        now rewrite <-nzhead_app_nzhead, Hi, app_nil_l.
      * now intro H; left.
  - simpl; case (norm e); clear e; intro e; [|now simpl].
    now case e; clear e; [|intro e..]; [|case e|..].
  - simpl.
    set (m := match nzhead _ with Nil => _ | _ => _ end).
    set (m' := match _ with Decimal _ _ => _ | _ => _ end).
    replace m' with m.
    2:{ unfold m'; case (norm e); clear m' e; intro e; [|now simpl].
      now case e; clear e; [|intro e..]; [|case e|..]. }
    unfold m; case (uint_eq_dec (nzhead (app i f)) Nil); intro Ha.
    + rewrite Ha; right; split; [now simpl|split].
      * now unfold unorm; rewrite (nzhead_app_nil_l _ _ Ha).
      * now unfold unorm; rewrite (nzhead_app_nil_r _ _ Ha).
    + left; split; [now revert Ha; case nzhead|].
      case (uint_eq_dec (nzhead i) Nil).
      * intro Hi; right; intro Hf; apply Ha.
        now rewrite <-nzhead_app_nzhead, Hi, app_nil_l.
      * now intro H; left.
Qed.

Lemma dnorm_spec_f d :
  let f := match d with Decimal _ f => f | DecimalExp _ f _ => f end in
  let f' := match dnorm d with Decimal _ f => f | DecimalExp _ f _ => f end in
  f' = f.
Proof.
  case d as [i f|i f e]; [now simpl|].
  simpl; case (int_eq_dec (norm e) (Pos zero)); [now intros->|intro He].
  set (i' := match i with Pos _ => _ | _ => _ end).
  set (m := match norm e with Pos Nil => _ | _ => _ end).
  replace m with (DecimalExp i' f (norm e)); [now simpl|].
  unfold m; revert He; case (norm e); clear m e; intro e; [|now simpl].
  now case e; clear e; [|intro e; case e|..].
Qed.

Lemma dnorm_spec_e d :
  match d, dnorm d with
    | Decimal _ _, Decimal _ _ => True
    | DecimalExp _ _ e, Decimal _ _ => norm e = Pos zero
    | DecimalExp _ _ e, DecimalExp _ _ e' => e' = norm e /\ e' <> Pos zero
    | Decimal _ _, DecimalExp _ _ _ => False
  end.
Proof.
  case d as [i f|i f e]; [now simpl|].
  simpl; case (int_eq_dec (norm e) (Pos zero)); [now intros->|intro He].
  set (i' := match i with Pos _ => _ | _ => _ end).
  set (m := match norm e with Pos Nil => _ | _ => _ end).
  replace m with (DecimalExp i' f (norm e)); [now simpl|].
  unfold m; revert He; case (norm e); clear m e; intro e; [|now simpl].
  now case e; clear e; [|intro e; case e|..].
Qed.

Lemma dnorm_involutive d : dnorm (dnorm d) = dnorm d.
Proof.
  case d as [i f|i f e]; case i as [i|i].
  - now simpl; rewrite unorm_involutive.
  - simpl; case (uint_eq_dec (nzhead (app i f)) Nil); [now intros->|intro Ha].
    set (m := match nzhead _ with Nil =>_ | _ => _ end).
    replace m with (Neg (unorm i)).
    2:{ now unfold m; revert Ha; case nzhead. }
    case (uint_eq_dec (nzhead i) Nil); intro Hi.
    + unfold unorm; rewrite Hi; simpl.
      case (uint_eq_dec (nzhead f) Nil).
      * intro Hf; exfalso; apply Ha.
        now rewrite <-nzhead_app_nzhead, Hi, app_nil_l.
      * now case nzhead.
    + rewrite unorm_involutive, (unorm_nzhead _ Hi), nzhead_app_nzhead.
      now revert Ha; case nzhead.
  - simpl; case (int_eq_dec (norm e) (Pos zero)); intro He.
    + now rewrite He; simpl; rewrite unorm_involutive.
    + set (m := match norm e with Pos Nil => _ | _ => _ end).
      replace m with (DecimalExp (Pos (unorm i)) f (norm e)).
      2:{ unfold m; revert He; case (norm e); clear m e; intro e; [|now simpl].
        now case e; clear e; [|intro e; case e|..]. }
      simpl; rewrite norm_involutive, unorm_involutive.
      revert He; case (norm e); clear m e; intro e; [|now simpl].
      now case e; clear e; [|intro e; case e|..].
  - simpl; case (int_eq_dec (norm e) (Pos zero)); intro He.
    + rewrite He; simpl.
      case (uint_eq_dec (nzhead (app i f)) Nil); [now intros->|intro Ha].
      set (m := match nzhead _ with Nil =>_ | _ => _ end).
      replace m with (Neg (unorm i)).
      2:{ now unfold m; revert Ha; case nzhead. }
      case (uint_eq_dec (nzhead i) Nil); intro Hi.
      * unfold unorm; rewrite Hi; simpl.
        case (uint_eq_dec (nzhead f) Nil).
        -- intro Hf; exfalso; apply Ha.
           now rewrite <-nzhead_app_nzhead, Hi, app_nil_l.
        -- now case nzhead.
      * rewrite unorm_involutive, (unorm_nzhead _ Hi), nzhead_app_nzhead.
        now revert Ha; case nzhead.
    + set (m := match norm e with Pos Nil => _ | _ => _ end).
      pose (i' := match nzhead (app i f) with Nil => Pos zero | _ => Neg (unorm i) end).
      replace m with (DecimalExp i' f (norm e)).
      2:{ unfold m; revert He; case (norm e); clear m e; intro e; [|now simpl].
        now case e; clear e; [|intro e; case e|..]. }
      simpl; rewrite norm_involutive.
      set (i'' := match i' with Pos _ => _ | _ => _ end).
      clear m; set (m := match norm e with Pos Nil => _ | _ => _ end).
      replace m with (DecimalExp i'' f (norm e)).
      2:{ unfold m; revert He; case (norm e); clear m e; intro e; [|now simpl].
        now case e; clear e; [|intro e; case e|..]. }
      unfold i'', i'.
      case (uint_eq_dec (nzhead (app i f)) Nil); [now intros->|intro Ha].
      fold i'; replace i' with (Neg (unorm i)).
      2:{ now unfold i'; revert Ha; case nzhead. }
      case (uint_eq_dec (nzhead i) Nil); intro Hi.
      * unfold unorm; rewrite Hi; simpl.
        case (uint_eq_dec (nzhead f) Nil).
        -- intro Hf; exfalso; apply Ha.
           now rewrite <-nzhead_app_nzhead, Hi, app_nil_l.
        -- now case nzhead.
      * rewrite unorm_involutive, (unorm_nzhead _ Hi), nzhead_app_nzhead.
        now revert Ha; case nzhead.
Qed.

Lemma IZ_to_Z_IZ_of_Z z : IZ_to_Z (IZ_of_Z z) = Some z.
Proof. now case z. Qed.

Lemma dnorm_i_exact i f :
  (nb_digits f < nb_digits (unorm (app (abs i) f)))%nat ->
  match i with
  | Pos i => Pos (unorm i)
  | Neg i =>
    match nzhead (app i f) with
    | Nil => Pos zero
    | _ => Neg (unorm i)
    end
  end = norm i.
Proof.
  case i as [ni|ni]; [now simpl|]; simpl.
  case (uint_eq_dec (nzhead (app ni f)) Nil); intro Ha.
  { now rewrite Ha, (nzhead_app_nil_l _ _ Ha). }
  rewrite (unorm_nzhead _ Ha).
  set (m := match nzhead _ with Nil => _ | _ => _ end).
  replace m with (Neg (unorm ni)); [|now unfold m; revert Ha; case nzhead].
  case (uint_eq_dec (nzhead ni) Nil); intro Hni.
  { rewrite <-nzhead_app_nzhead, Hni, app_nil_l.
    intro H; exfalso; revert H; apply Nat.le_ngt, nb_digits_nzhead. }
  clear m; set (m := match nzhead ni with Nil => _ | _ => _ end).
  replace m with (Neg (nzhead ni)); [|now unfold m; revert Hni; case nzhead].
  now rewrite (unorm_nzhead _ Hni).
Qed.

Lemma dnorm_i_exact' i f :
  (nb_digits (unorm (app (abs i) f)) <= nb_digits f)%nat ->
  match i with
  | Pos i => Pos (unorm i)
  | Neg i =>
    match nzhead (app i f) with
    | Nil => Pos zero
    | _ => Neg (unorm i)
    end
  end =
  match norm (app_int i f) with
  | Pos _ => Pos zero
  | Neg _ => Neg zero
  end.
Proof.
  case i as [ni|ni]; simpl.
  { now intro Hnb; rewrite (unorm_app_zero _ _ Hnb). }
  unfold unorm.
  case (uint_eq_dec (nzhead (app ni f)) Nil); intro Hn.
  { now rewrite Hn. }
  set (m := match nzhead _ with Nil => _ | _ => _ end).
  replace m with (nzhead (app ni f)).
  2:{ now unfold m; revert Hn; case nzhead. }
  clear m; set (m := match nzhead _ with Nil => _ | _ => _ end).
  replace m with (Neg (unorm ni)).
  2:{ now unfold m, unorm; revert Hn; case nzhead. }
  clear m; set (m := match nzhead _ with Nil => _ | _ => _ end).
  replace m with (Neg (nzhead (app ni f))).
  2:{ now unfold m; revert Hn; case nzhead. }
  rewrite <-(unorm_nzhead _ Hn).
  now intro H; rewrite (unorm_app_zero _ _ H).
Qed.

Lemma to_of (d:decimal) : to_decimal (of_decimal d) = Some (dnorm d).
Proof.
  case d as [i f|i f e].
  - unfold of_decimal; simpl; unfold IQmake_to_decimal'.
    rewrite IZ_to_Z_IZ_of_Z.
    unfold IQmake_to_decimal; simpl.
    change (fun _ : positive => _) with (Pos.mul 10).
    rewrite nztail_to_uint_pow10, to_of.
    case_eq (nb_digits f); [|intro nb]; intro Hnb.
    + rewrite (nb_digits_0 _ Hnb), app_int_nil_r.
      case i as [ni|ni]; [now simpl|].
      rewrite app_nil_r; simpl; unfold unorm.
      now case (nzhead ni).
    + rewrite <-Hnb.
      rewrite abs_norm, abs_app_int.
      case Nat.ltb_spec; intro Hnb'.
      * rewrite (del_tail_app_int_exact _ _ Hnb').
        rewrite (del_head_app_int_exact _ _ Hnb').
        now rewrite (dnorm_i_exact _ _ Hnb').
      * rewrite (unorm_app_r _ _ Hnb').
        rewrite iter_D0_unorm; [|now apply nb_digits_n0; rewrite Hnb].
        now rewrite dnorm_i_exact'.
  - unfold of_decimal; simpl.
    rewrite <-to_of.
    case (Z.of_int e); clear e; [|intro e..]; simpl.
    + unfold IQmake_to_decimal'.
      rewrite IZ_to_Z_IZ_of_Z.
      unfold IQmake_to_decimal; simpl.
      change (fun _ : positive => _) with (Pos.mul 10).
      rewrite nztail_to_uint_pow10, to_of.
      case_eq (nb_digits f); [|intro nb]; intro Hnb.
      * rewrite (nb_digits_0 _ Hnb), app_int_nil_r.
        case i as [ni|ni]; [now simpl|].
        rewrite app_nil_r; simpl; unfold unorm.
        now case (nzhead ni).
      * rewrite <-Hnb.
        rewrite abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnb'.
        -- rewrite (del_tail_app_int_exact _ _ Hnb').
           rewrite (del_head_app_int_exact _ _ Hnb').
           now rewrite (dnorm_i_exact _ _ Hnb').
        -- rewrite (unorm_app_r _ _ Hnb').
           rewrite iter_D0_unorm; [|now apply nb_digits_n0; rewrite Hnb].
           now rewrite dnorm_i_exact'.
    + unfold IQmake_to_decimal'.
      rewrite IZ_to_Z_IZ_of_Z.
      unfold IQmake_to_decimal; simpl.
      change (fun _ : positive => _) with (Pos.mul 10).
      rewrite nztail_to_uint_pow10, to_of.
      generalize (Unsigned.to_uint_nonzero e); intro He.
      set (dnorm_i := match i with Pos _ => _ | _ => _ end).
      set (m := match Pos.to_uint e with Nil => _ | _ => _ end).
      replace m with (DecimalExp dnorm_i f (Pos (Pos.to_uint e))).
      2:{ now unfold m; revert He; case (Pos.to_uint e); [|intro u; case u|..]. }
      clear m; unfold dnorm_i.
      case_eq (nb_digits f); [|intro nb]; intro Hnb.
      * rewrite (nb_digits_0 _ Hnb), app_int_nil_r.
        case i as [ni|ni]; [now simpl|].
        rewrite app_nil_r; simpl; unfold unorm.
        now case (nzhead ni).
      * rewrite <-Hnb.
        rewrite abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnb'.
        -- rewrite (del_tail_app_int_exact _ _ Hnb').
           rewrite (del_head_app_int_exact _ _ Hnb').
           now rewrite (dnorm_i_exact _ _ Hnb').
        -- rewrite (unorm_app_r _ _ Hnb').
           rewrite iter_D0_unorm; [|now apply nb_digits_n0; rewrite Hnb].
           now rewrite dnorm_i_exact'.
    + unfold IQmake_to_decimal'.
      rewrite IZ_to_Z_IZ_of_Z.
      unfold IQmake_to_decimal; simpl.
      change (fun _ : positive => _) with (Pos.mul 10).
      rewrite nztail_to_uint_pow10, to_of.
      case_eq (nb_digits f); [|intro nb]; intro Hnb.
      * rewrite (nb_digits_0 _ Hnb), app_int_nil_r.
        case i as [ni|ni]; [now simpl|].
        rewrite app_nil_r; simpl; unfold unorm.
        now case (nzhead ni).
      * rewrite <-Hnb.
        rewrite abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnb'.
        -- rewrite (del_tail_app_int_exact _ _ Hnb').
           rewrite (del_head_app_int_exact _ _ Hnb').
           now rewrite (dnorm_i_exact _ _ Hnb').
        -- rewrite (unorm_app_r _ _ Hnb').
           rewrite iter_D0_unorm; [|now apply nb_digits_n0; rewrite Hnb].
           now rewrite dnorm_i_exact'.
Qed.

(** Some consequences *)

Lemma to_decimal_inj q q' :
  to_decimal q <> None -> to_decimal q = to_decimal q' -> q = q'.
Proof.
  intros Hnone EQ.
  generalize (of_to q) (of_to q').
  rewrite <-EQ.
  revert Hnone; case to_decimal; [|now simpl].
  now intros d _ H1 H2; rewrite <-(H1 d eq_refl), <-(H2 d eq_refl).
Qed.

Lemma to_decimal_surj d : exists q, to_decimal q = Some (dnorm d).
Proof.
  exists (of_decimal d). apply to_of.
Qed.

Lemma of_decimal_dnorm d : of_decimal (dnorm d) = of_decimal d.
Proof. now apply to_decimal_inj; rewrite !to_of; [|rewrite dnorm_involutive]. Qed.

Lemma of_inj d d' : of_decimal d = of_decimal d' -> dnorm d = dnorm d'.
Proof.
  intro H.
  apply (@f_equal _ _ (fun x => match x with Some x => x | _ => d end)
                  (Some (dnorm d)) (Some (dnorm d'))).
  now rewrite <- !to_of, H.
Qed.

Lemma of_iff d d' : of_decimal d = of_decimal d' <-> dnorm d = dnorm d'.
Proof.
  split.
  - apply of_inj.
  - intros E. rewrite <- of_decimal_dnorm, E.
    apply of_decimal_dnorm.
Qed.
