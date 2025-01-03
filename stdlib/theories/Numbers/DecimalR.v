(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalR

    Proofs that conversions between decimal numbers and [R]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalZ DecimalQ Rdefinitions.
Require Import PeanoNat.

Lemma of_IQmake_to_decimal num den :
  match IQmake_to_decimal num den with
  | None => True
  | Some (DecimalExp _ _ _) => False
  | Some (Decimal i f) =>
    of_decimal (Decimal i f) = IRQ (QArith_base.Qmake num den)
  end.
Proof.
  unfold IQmake_to_decimal.
  case (Pos.eq_dec den 1); [now intros->|intro Hden].
  assert (Hf : match QArith_base.IQmake_to_decimal num den with
               | Some (Decimal i f) => f <> Nil
               | _ => True
               end).
  { unfold QArith_base.IQmake_to_decimal; simpl.
    generalize (Unsigned.nztail_to_uint den).
    case Decimal.nztail as [den' e_den'].
    case den'; [now simpl|now simpl| |now simpl..]; clear den'; intro den'.
    case den'; [ |now simpl..]; clear den'.
    case e_den' as [|e_den']; [now simpl; intros H _; apply Hden; injection H|].
    intros _.
    case Nat.ltb_spec; intro He_den'.
    - apply del_head_nonnil.
      revert He_den'; case nb_digits as [|n]; [now simpl|].
      now intro H; simpl; apply Nat.lt_succ_r, Nat.le_sub_l.
    - apply nb_digits_n0.
      now rewrite nb_digits_iter_D0, Nat.sub_add. }
  replace (match den with 1%positive => _ | _ => _ end)
    with (QArith_base.IQmake_to_decimal num den); [|now revert Hden; case den].
  generalize (of_IQmake_to_decimal num den).
  case QArith_base.IQmake_to_decimal as [d'|]; [|now simpl].
  case d' as [i f|]; [|now simpl].
  unfold of_decimal; simpl.
  injection 1 as H <-.
  generalize (f_equal QArith_base.IZ_to_Z H); clear H.
  rewrite !IZ_to_Z_IZ_of_Z; injection 1 as <-.
  now revert Hf; case f.
Qed.

Lemma of_to (q:IR) : forall d, to_decimal q = Some d -> of_decimal d = q.
Proof.
  intro d.
  case q as [z|q|r r'|r r']; simpl.
  - case z as [z p| |p|p].
    + now simpl.
    + now simpl; injection 1 as <-.
    + simpl; injection 1 as <-.
      now unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to.
    + simpl; injection 1 as <-.
      now unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to.
  - case q as [num den].
    generalize (of_IQmake_to_decimal num den).
    case IQmake_to_decimal as [d'|]; [|now simpl].
    case d' as [i f|]; [|now simpl].
    now intros H; injection 1 as <-.
  - case r as [z|q| |]; [|case q as[num den]|now simpl..];
      (case r' as [z'| | |]; [|now simpl..]);
      (case z' as [p e| | |]; [|now simpl..]).
    + case (Z.eq_dec p 10); [intros->|intro Hp].
      2:{ revert Hp; case p; [now simpl|intro d0..];
        (case d0; [intro d1..|]; [now simpl| |now simpl];
         case d1; [intro d2..|]; [|now simpl..];
         case d2; [intro d3..|]; [now simpl| |now simpl];
         now case d3). }
      case z as [| |p|p]; [now simpl|..]; injection 1 as <-.
      * now unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to.
      * unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to; simpl.
        now rewrite Unsigned.of_to.
      * unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to; simpl.
        now rewrite Unsigned.of_to.
    + case (Z.eq_dec p 10); [intros->|intro Hp].
      2:{ revert Hp; case p; [now simpl|intro d0..];
        (case d0; [intro d1..|]; [now simpl| |now simpl];
         case d1; [intro d2..|]; [|now simpl..];
         case d2; [intro d3..|]; [now simpl| |now simpl];
         now case d3). }
      generalize (of_IQmake_to_decimal num den).
      case IQmake_to_decimal as [d'|]; [|now simpl].
      case d' as [i f|]; [|now simpl].
      intros H; injection 1 as <-.
      unfold of_decimal; simpl.
      change (match f with Nil => _ | _ => _ end) with (of_decimal (Decimal i f)).
      rewrite H; clear H.
      now unfold Z.of_uint; rewrite Unsigned.of_to.
  - case r as [z|q| |]; [|case q as[num den]|now simpl..];
      (case r' as [z'| | |]; [|now simpl..]);
      (case z' as [p e| | |]; [|now simpl..]).
    + case (Z.eq_dec p 10); [intros->|intro Hp].
      2:{ revert Hp; case p; [now simpl|intro d0..];
        (case d0; [intro d1..|]; [now simpl| |now simpl];
         case d1; [intro d2..|]; [|now simpl..];
         case d2; [intro d3..|]; [now simpl| |now simpl];
         now case d3). }
      case z as [| |p|p]; [now simpl|..]; injection 1 as <-.
      * now unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to.
      * unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to; simpl.
        now rewrite Unsigned.of_to.
      * unfold of_decimal; simpl; unfold Z.of_uint; rewrite Unsigned.of_to; simpl.
        now rewrite Unsigned.of_to.
    + case (Z.eq_dec p 10); [intros->|intro Hp].
      2:{ revert Hp; case p; [now simpl|intro d0..];
        (case d0; [intro d1..|]; [now simpl| |now simpl];
         case d1; [intro d2..|]; [|now simpl..];
         case d2; [intro d3..|]; [now simpl| |now simpl];
         now case d3). }
      generalize (of_IQmake_to_decimal num den).
      case IQmake_to_decimal as [d'|]; [|now simpl].
      case d' as [i f|]; [|now simpl].
      intros H; injection 1 as <-.
      unfold of_decimal; simpl.
      change (match f with Nil => _ | _ => _ end) with (of_decimal (Decimal i f)).
      rewrite H; clear H.
      now unfold Z.of_uint; rewrite Unsigned.of_to.
Qed.

Lemma to_of (d:decimal) : to_decimal (of_decimal d) = Some (dnorm d).
Proof.
  case d as [i f|i f e].
  - unfold of_decimal; simpl.
    case (uint_eq_dec f Nil); intro Hf.
    + rewrite Hf; clear f Hf.
      unfold to_decimal; simpl.
      rewrite IZ_to_Z_IZ_of_Z, DecimalZ.to_of.
      case i as [i|i]; [now simpl|]; simpl.
      rewrite app_nil_r.
      case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
      now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
    + set (r := IRQ _).
      set (m := match f with Nil => _ | _ => _ end).
      replace m with r; [unfold r|now unfold m; revert Hf; case f].
      unfold to_decimal; simpl.
      unfold IQmake_to_decimal; simpl.
      set (n := Nat.iter _ _ _).
      case (Pos.eq_dec n 1); intro Hn.
      { exfalso; apply Hf.
        now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
      clear m; set (m := match n with 1%positive | _ => _ end).
      replace m with (QArith_base.IQmake_to_decimal (Z.of_int (app_int i f)) n).
      2:{ now unfold m; revert Hn; case n. }
      unfold QArith_base.IQmake_to_decimal, n; simpl.
      rewrite nztail_to_uint_pow10.
      clear r; set (r := if _ <? _ then Some (Decimal _ _) else Some _).
      clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
      replace m with r; [unfold r|now unfold m; revert Hf; case f].
      rewrite DecimalZ.to_of, abs_norm, abs_app_int.
      case Nat.ltb_spec; intro Hnf.
      * rewrite (del_tail_app_int_exact _ _ Hnf).
        rewrite (del_head_app_int_exact _ _ Hnf).
        now rewrite (dnorm_i_exact _ _ Hnf).
      * rewrite (unorm_app_r _ _ Hnf).
        rewrite (iter_D0_unorm _ Hf).
        now rewrite dnorm_i_exact'.
  - unfold of_decimal; simpl.
    rewrite <-(DecimalZ.to_of e).
    case (Z.of_int e); clear e; [|intro e..]; simpl.
    + case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_decimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, DecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_decimal; simpl.
        unfold IQmake_to_decimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        { exfalso; apply Hf.
          now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_decimal (Z.of_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_decimal, n; simpl.
        rewrite nztail_to_uint_pow10.
        clear r; set (r := if _ <? _ then Some (Decimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite DecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
           now rewrite dnorm_i_exact'.
    + set (i' := match i with Pos _ => _ | _ => _ end).
      set (m := match Pos.to_uint e with Nil => _ | _ => _ end).
      replace m with (DecimalExp i' f (Pos (Pos.to_uint e))).
      2:{ unfold m; generalize (Unsigned.to_uint_nonzero e).
          now case Pos.to_uint; [|intro u; case u|..]. }
      unfold i'; clear i' m.
      case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_decimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, DecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_decimal; simpl.
        unfold IQmake_to_decimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        { exfalso; apply Hf.
          now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_decimal (Z.of_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_decimal, n; simpl.
        rewrite nztail_to_uint_pow10.
        clear r; set (r := if _ <? _ then Some (Decimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite DecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
           now rewrite dnorm_i_exact'.
    + case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_decimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, DecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_decimal; simpl.
        unfold IQmake_to_decimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        { exfalso; apply Hf.
          now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_decimal (Z.of_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_decimal, n; simpl.
        rewrite nztail_to_uint_pow10.
        clear r; set (r := if _ <? _ then Some (Decimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite DecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
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
