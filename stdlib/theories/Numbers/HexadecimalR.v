(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalR

    Proofs that conversions between hexadecimal numbers and [R]
    are bijections. *)

Require Import PeanoNat.
Require Import Decimal DecimalFacts.
Require Import Hexadecimal HexadecimalFacts HexadecimalPos HexadecimalZ.
Require Import HexadecimalQ Rdefinitions.

Lemma of_IQmake_to_hexadecimal num den :
  match IQmake_to_hexadecimal num den with
  | None => True
  | Some (HexadecimalExp _ _ _) => False
  | Some (Hexadecimal i f) =>
    of_hexadecimal (Hexadecimal i f) = IRQ (QArith_base.Qmake num den)
  end.
Proof.
  unfold IQmake_to_hexadecimal.
  case (Pos.eq_dec den 1); [now intros->|intro Hden].
  assert (Hf : match QArith_base.IQmake_to_hexadecimal num den with
               | Some (Hexadecimal i f) => f <> Nil
               | _ => True
               end).
  { unfold QArith_base.IQmake_to_hexadecimal; simpl.
    generalize (Unsigned.nztail_to_hex_uint den).
    case Hexadecimal.nztail as [den' e_den'].
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
    with (QArith_base.IQmake_to_hexadecimal num den); [|now revert Hden; case den].
  generalize (of_IQmake_to_hexadecimal num den).
  case QArith_base.IQmake_to_hexadecimal as [d'|]; [|now simpl].
  case d' as [i f|]; [|now simpl].
  unfold of_hexadecimal; simpl.
  injection 1 as H <-.
  generalize (f_equal QArith_base.IZ_to_Z H); clear H.
  rewrite !IZ_to_Z_IZ_of_Z; injection 1 as <-.
  now revert Hf; case f.
Qed.

Lemma of_to (q:IR) : forall d, to_hexadecimal q = Some d -> of_hexadecimal d = q.
Proof.
  intro d.
  case q as [z|q|r r'|r r']; simpl.
  - case z as [z p| |p|p].
    + now simpl.
    + now simpl; injection 1 as <-.
    + simpl; injection 1 as <-.
      now unfold of_hexadecimal; simpl; unfold Z.of_hex_uint; rewrite Unsigned.of_to.
    + simpl; injection 1 as <-.
      now unfold of_hexadecimal; simpl; unfold Z.of_hex_uint; rewrite Unsigned.of_to.
  - case q as [num den].
    generalize (of_IQmake_to_hexadecimal num den).
    case IQmake_to_hexadecimal as [d'|]; [|now simpl].
    case d' as [i f|]; [|now simpl].
    now intros H; injection 1 as <-.
  - case r as [z|q| |]; [|case q as[num den]|now simpl..];
      (case r' as [z'| | |]; [|now simpl..]);
      (case z' as [p e| | |]; [|now simpl..]).
    + case (Z.eq_dec p 2); [intros->|intro Hp].
      2:{ now revert Hp; case p;
          [|intro d0; case d0; [intro d1..|]; [|case d1|]..]. }
      case z as [| |p|p]; [now simpl|..]; injection 1 as <-.
      * now unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
      * unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        now unfold Z.of_hex_uint; rewrite Unsigned.of_to.
      * unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        now unfold Z.of_hex_uint; rewrite Unsigned.of_to.
    + case (Z.eq_dec p 2); [intros->|intro Hp].
      2:{ now revert Hp; case p;
          [|intro d0; case d0; [intro d1..|]; [|case d1|]..]. }
      generalize (of_IQmake_to_hexadecimal num den).
      case IQmake_to_hexadecimal as [d'|]; [|now simpl].
      case d' as [i f|]; [|now simpl].
      intros H; injection 1 as <-.
      unfold of_hexadecimal; simpl.
      change (match f with Nil => _ | _ => _ end) with (of_hexadecimal (Hexadecimal i f)).
      rewrite H; clear H.
      now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
  - case r as [z|q| |]; [|case q as[num den]|now simpl..];
      (case r' as [z'| | |]; [|now simpl..]);
      (case z' as [p e| | |]; [|now simpl..]).
    + case (Z.eq_dec p 2); [intros->|intro Hp].
      2:{ now revert Hp; case p;
          [|intro d0; case d0; [intro d1..|]; [|case d1|]..]. }
      case z as [| |p|p]; [now simpl|..]; injection 1 as <-.
      * now unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
      * unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        now unfold Z.of_hex_uint; rewrite Unsigned.of_to.
      * unfold of_hexadecimal; simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        now unfold Z.of_hex_uint; rewrite Unsigned.of_to.
    + case (Z.eq_dec p 2); [intros->|intro Hp].
      2:{ now revert Hp; case p;
          [|intro d0; case d0; [intro d1..|]; [|case d1|]..]. }
      generalize (of_IQmake_to_hexadecimal num den).
      case IQmake_to_hexadecimal as [d'|]; [|now simpl].
      case d' as [i f|]; [|now simpl].
      intros H; injection 1 as <-.
      unfold of_hexadecimal; simpl.
      change (match f with Nil => _ | _ => _ end) with (of_hexadecimal (Hexadecimal i f)).
      rewrite H; clear H.
      now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
Qed.

Lemma to_of (d:hexadecimal) : to_hexadecimal (of_hexadecimal d) = Some (dnorm d).
Proof.
  case d as [i f|i f e].
  - unfold of_hexadecimal; simpl.
    case (uint_eq_dec f Nil); intro Hf.
    + rewrite Hf; clear f Hf.
      unfold to_hexadecimal; simpl.
      rewrite IZ_to_Z_IZ_of_Z, HexadecimalZ.to_of.
      case i as [i|i]; [now simpl|]; simpl.
      rewrite app_nil_r.
      case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
      now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
    + set (r := IRQ _).
      set (m := match f with Nil => _ | _ => _ end).
      replace m with r; [unfold r|now unfold m; revert Hf; case f].
      unfold to_hexadecimal; simpl.
      unfold IQmake_to_hexadecimal; simpl.
      set (n := Nat.iter _ _ _).
      case (Pos.eq_dec n 1); intro Hn.
      * exfalso; apply Hf.
        { now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
      * clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_hexadecimal (Z.of_hex_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_hexadecimal, n; simpl.
        rewrite nztail_to_hex_uint_pow16.
        clear r; set (r := if _ <? _ then Some (Hexadecimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite HexadecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
           now rewrite dnorm_i_exact'.
  - unfold of_hexadecimal; simpl.
    rewrite <-(DecimalZ.to_of e).
    case (Z.of_int e); clear e; [|intro e..]; simpl.
    + case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_hexadecimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, HexadecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_hexadecimal; simpl.
        unfold IQmake_to_hexadecimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        -- exfalso; apply Hf.
           { now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        -- clear m; set (m := match n with 1%positive | _ => _ end).
           replace m with (QArith_base.IQmake_to_hexadecimal (Z.of_hex_int (app_int i f)) n).
           2:{ now unfold m; revert Hn; case n. }
           unfold QArith_base.IQmake_to_hexadecimal, n; simpl.
           rewrite nztail_to_hex_uint_pow16.
           clear r; set (r := if _ <? _ then Some (Hexadecimal _ _) else Some _).
           clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
           replace m with r; [unfold r|now unfold m; revert Hf; case f].
           rewrite HexadecimalZ.to_of, abs_norm, abs_app_int.
           case Nat.ltb_spec; intro Hnf.
           ++ rewrite (del_tail_app_int_exact _ _ Hnf).
              rewrite (del_head_app_int_exact _ _ Hnf).
              now rewrite (dnorm_i_exact _ _ Hnf).
           ++ rewrite (unorm_app_r _ _ Hnf).
              rewrite (iter_D0_unorm _ Hf).
              now rewrite dnorm_i_exact'.
    + set (i' := match i with Pos _ => _ | _ => _ end).
      set (m := match Pos.to_uint e with Decimal.Nil => _ | _ => _ end).
      replace m with (HexadecimalExp i' f (Decimal.Pos (Pos.to_uint e))).
      2:{ unfold m; generalize (DecimalPos.Unsigned.to_uint_nonzero e).
          now case Pos.to_uint; [|intro u; case u|..]. }
      unfold i'; clear i' m.
      case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_hexadecimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, HexadecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_hexadecimal; simpl.
        unfold IQmake_to_hexadecimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        { exfalso; apply Hf.
          now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_hexadecimal (Z.of_hex_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_hexadecimal, n; simpl.
        rewrite nztail_to_hex_uint_pow16.
        clear r; set (r := if _ <? _ then Some (Hexadecimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite HexadecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
           now rewrite dnorm_i_exact'.
    + case (uint_eq_dec f Nil); intro Hf.
      * rewrite Hf; clear f Hf.
        unfold to_hexadecimal; simpl.
        rewrite IZ_to_Z_IZ_of_Z, HexadecimalZ.to_of.
        case i as [i|i]; [now simpl|]; simpl.
        rewrite app_nil_r.
        case (uint_eq_dec (nzhead i) Nil); [now intros->|intro Hi].
        now rewrite (unorm_nzhead _ Hi); revert Hi; case nzhead.
      * set (r := IRQ _).
        set (m := match f with Nil => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        unfold to_hexadecimal; simpl.
        unfold IQmake_to_hexadecimal; simpl.
        set (n := Nat.iter _ _ _).
        case (Pos.eq_dec n 1); intro Hn.
        { exfalso; apply Hf.
          now apply nb_digits_0; revert Hn; unfold n; case nb_digits. }
        clear m; set (m := match n with 1%positive | _ => _ end).
        replace m with (QArith_base.IQmake_to_hexadecimal (Z.of_hex_int (app_int i f)) n).
        2:{ now unfold m; revert Hn; case n. }
        unfold QArith_base.IQmake_to_hexadecimal, n; simpl.
        rewrite nztail_to_hex_uint_pow16.
        clear r; set (r := if _ <? _ then Some (Hexadecimal _ _) else Some _).
        clear m; set (m := match nb_digits f with 0 => _ | _ => _ end).
        replace m with r; [unfold r|now unfold m; revert Hf; case f].
        rewrite HexadecimalZ.to_of, abs_norm, abs_app_int.
        case Nat.ltb_spec; intro Hnf.
        -- rewrite (del_tail_app_int_exact _ _ Hnf).
           rewrite (del_head_app_int_exact _ _ Hnf).
           now rewrite (dnorm_i_exact _ _ Hnf).
        -- rewrite (unorm_app_r _ _ Hnf).
           rewrite (iter_D0_unorm _ Hf).
           now rewrite dnorm_i_exact'.
Qed.

(** Some consequences *)

Lemma to_hexadecimal_inj q q' :
  to_hexadecimal q <> None -> to_hexadecimal q = to_hexadecimal q' -> q = q'.
Proof.
  intros Hnone EQ.
  generalize (of_to q) (of_to q').
  rewrite <-EQ.
  revert Hnone; case to_hexadecimal; [|now simpl].
  now intros d _ H1 H2; rewrite <-(H1 d eq_refl), <-(H2 d eq_refl).
Qed.

Lemma to_hexadecimal_surj d : exists q, to_hexadecimal q = Some (dnorm d).
Proof.
  exists (of_hexadecimal d). apply to_of.
Qed.

Lemma of_hexadecimal_dnorm d : of_hexadecimal (dnorm d) = of_hexadecimal d.
Proof. now apply to_hexadecimal_inj; rewrite !to_of; [|rewrite dnorm_involutive]. Qed.

Lemma of_inj d d' : of_hexadecimal d = of_hexadecimal d' -> dnorm d = dnorm d'.
Proof.
  intro H.
  apply (@f_equal _ _ (fun x => match x with Some x => x | _ => d end)
                  (Some (dnorm d)) (Some (dnorm d'))).
  now rewrite <- !to_of, H.
Qed.

Lemma of_iff d d' : of_hexadecimal d = of_hexadecimal d' <-> dnorm d = dnorm d'.
Proof.
  split.
  - apply of_inj.
  - intros E. rewrite <- of_hexadecimal_dnorm, E.
    apply of_hexadecimal_dnorm.
Qed.
