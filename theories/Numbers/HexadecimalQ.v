(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalQ

    Proofs that conversions between hexadecimal numbers and [Q]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN DecimalZ.
Require Import Hexadecimal HexadecimalFacts HexadecimalPos HexadecimalN HexadecimalZ QArith.

Lemma of_to (q:Q) : forall d, to_hexadecimal q = Some d -> of_hexadecimal d = q.
Proof.
  cut (match to_hexadecimal q with None => True | Some d => of_hexadecimal d = q end).
  { now case to_hexadecimal; [intros d <- d' Hd'; injection Hd'; intros ->|]. }
  destruct q as (num, den).
  unfold to_hexadecimal; simpl Qnum; simpl Qden.
  generalize (HexadecimalPos.Unsigned.nztail_to_hex_uint den).
  case Hexadecimal.nztail; intros u n.
  change 16%N with (2^4)%N; rewrite <-N.pow_mul_r.
  change 4%N with (N.of_nat 4); rewrite <-Nnat.Nat2N.inj_mul.
  change 4%Z with (Z.of_nat 4); rewrite <-Nat2Z.inj_mul.
  case u; clear u; try (intros; exact I); [| | |]; intro u;
    (case u; clear u; [|intros; exact I..]).
  - unfold Pos.of_hex_uint, Pos.of_hex_uint_acc; rewrite N.mul_1_l.
    case n.
    + unfold of_hexadecimal, app_int, app, Z.to_hex_int; simpl.
      intro H; inversion H as (H1); clear H H1.
      case num; [reflexivity|intro pnum; fold (rev (rev (Pos.to_hex_uint pnum)))..].
      * rewrite rev_rev; simpl.
        now unfold Z.of_hex_uint; rewrite HexadecimalPos.Unsigned.of_to.
      * rewrite rev_rev; simpl.
      now unfold Z.of_hex_uint; rewrite HexadecimalPos.Unsigned.of_to.
    + clear n; intros n.
      intro H; injection H; intros ->; clear H.
      unfold of_hexadecimal.
      rewrite DecimalZ.of_to.
      simpl nb_digits; rewrite Nat2Z.inj_0, Z.mul_0_r, Z.sub_0_r.
      now apply f_equal2; [rewrite app_int_nil_r, of_to|].
  - unfold Pos.of_hex_uint, Pos.of_hex_uint_acc.
    rewrite <-N.pow_succ_r', <-Nnat.Nat2N.inj_succ.
    intro H; injection H; intros ->; clear H.
    fold (4 * n)%nat.
    change 1%Z with (Z.of_nat 1); rewrite <-Znat.Nat2Z.inj_add.
    unfold of_hexadecimal.
    rewrite DecimalZ.of_to.
    simpl nb_digits; rewrite Nat2Z.inj_0, Z.mul_0_r, Z.sub_0_r.
    now apply f_equal2; [rewrite app_int_nil_r, of_to|].
  - change 2%Z with (Z.of_nat 2); rewrite <-Znat.Nat2Z.inj_add.
    unfold Pos.of_hex_uint, Pos.of_hex_uint_acc.
    change 4%N with (2^2)%N; rewrite <-N.pow_add_r.
    change 2%N with (N.of_nat 2); rewrite <-Nnat.Nat2N.inj_add.
    intro H; injection H; intros ->; clear H.
    fold (4 * n)%nat.
    unfold of_hexadecimal.
    rewrite DecimalZ.of_to.
    simpl nb_digits; rewrite Nat2Z.inj_0, Z.mul_0_r, Z.sub_0_r.
    now apply f_equal2; [rewrite app_int_nil_r, of_to|].
  - change 3%Z with (Z.of_nat 3); rewrite <-Znat.Nat2Z.inj_add.
    unfold Pos.of_hex_uint, Pos.of_hex_uint_acc.
    change 8%N with (2^3)%N; rewrite <-N.pow_add_r.
    change 3%N with (N.of_nat 3); rewrite <-Nnat.Nat2N.inj_add.
    intro H; injection H; intros ->; clear H.
    fold (4 * n)%nat.
    unfold of_hexadecimal.
    rewrite DecimalZ.of_to.
    simpl nb_digits; rewrite Nat2Z.inj_0, Z.mul_0_r, Z.sub_0_r.
    now apply f_equal2; [rewrite app_int_nil_r, of_to|].
Qed.

(* normalize without fractional part, for instance norme 0x1.2p-1 is 0x12e-5 *)
Definition hnorme (d:hexadecimal) : hexadecimal :=
  let '(i, f, e) :=
    match d with
    | Hexadecimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | HexadecimalExp i f e => (i, f, e)
    end in
  let i := norm (app_int i f) in
  let e := (Z.of_int e - 4 * Z.of_nat (nb_digits f))%Z in
  match e with
  | Z0 => Hexadecimal i Nil
  | Zpos e => Hexadecimal (Pos.iter double i e) Nil
  | Zneg _ => HexadecimalExp i Nil (Decimal.norm (Z.to_int e))
  end.

Lemma hnorme_spec d :
  match hnorme d with
  | Hexadecimal i Nil => i = norm i
  | HexadecimalExp i Nil e =>
    i = norm i /\ e = Decimal.norm e /\ e <> Decimal.Pos Decimal.zero
  | _ => False
  end.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold hnorme; simpl.
  - case_eq (nb_digits f); [now simpl; rewrite norm_invol|]; intros nf Hnf.
    split; [now simpl; rewrite norm_invol|].
    unfold Z.of_nat.
    now rewrite <-!DecimalZ.to_of, !DecimalZ.of_to.
  - set (e' := (_ - _)%Z).
    case_eq e'; [|intro pe'..]; intro He'.
    + now rewrite norm_invol.
    + rewrite Pos2Nat.inj_iter.
      set (ne' := Pos.to_nat pe').
      fold (Nat.iter ne' double (norm (app_int i f))).
      induction ne'; [now simpl; rewrite norm_invol|].
      now rewrite Unsigned.nat_iter_S, <-double_norm, IHne', norm_invol.
    + split; [now rewrite norm_invol|].
      split; [now rewrite DecimalFacts.norm_invol|].
      rewrite <-DecimalZ.to_of, DecimalZ.of_to.
      change (Decimal.Pos _) with (Z.to_int 0).
      now intro H; generalize (DecimalZ.to_int_inj _ _ H).
Qed.

Lemma hnorme_invol d : hnorme (hnorme d) = hnorme d.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold hnorme; simpl.
  - case_eq (nb_digits f); [now simpl; rewrite app_int_nil_r, norm_invol|].
    intros nf Hnf.
    unfold Z.of_nat.
    simpl.
    set (pnf := Pos.to_uint _).
    set (nz := Decimal.nzhead pnf).
    assert (Hnz : nz <> Decimal.Nil).
    { unfold nz, pnf.
      rewrite <-DecimalFacts.unorm_0.
      rewrite <-DecimalPos.Unsigned.to_of.
      rewrite DecimalPos.Unsigned.of_to.
      change Decimal.zero with (N.to_uint 0).
      now intro H; generalize (DecimalN.Unsigned.to_uint_inj _ _ H). }
    set (m := match nz with Decimal.Nil => _ | _ => _ end).
    assert (Hm : m = (Decimal.Neg (Decimal.unorm pnf))).
    { now revert Hnz; unfold m, nz, Decimal.unorm; fold nz; case nz. }
    rewrite Hm; unfold pnf.
    rewrite <-DecimalPos.Unsigned.to_of, DecimalPos.Unsigned.of_to.
    simpl; unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
    rewrite Z.sub_0_r; simpl.
    fold pnf; fold nz; fold m; rewrite Hm; unfold pnf.
    rewrite <-DecimalPos.Unsigned.to_of, DecimalPos.Unsigned.of_to.
    now rewrite app_int_nil_r, norm_invol.
  - set (e' := (_ - _)%Z).
    case_eq e'; [|intro pe'..]; intro Hpe'.
    + now simpl; rewrite app_int_nil_r, norm_invol.
    + simpl; rewrite app_int_nil_r.
      apply f_equal2; [|reflexivity].
      rewrite Pos2Nat.inj_iter.
      set (ne' := Pos.to_nat pe').
      fold (Nat.iter ne' double (norm (app_int i f))).
      induction ne'; [now simpl; rewrite norm_invol|].
      now rewrite Unsigned.nat_iter_S, <-double_norm, IHne'.
    + rewrite <-DecimalZ.to_of, !DecimalZ.of_to; simpl.
      rewrite app_int_nil_r, norm_invol.
      set (pnf := Pos.to_uint _).
      set (nz := Decimal.nzhead pnf).
      assert (Hnz : nz <> Decimal.Nil).
      { unfold nz, pnf.
        rewrite <-DecimalFacts.unorm_0.
        rewrite <-DecimalPos.Unsigned.to_of.
        rewrite DecimalPos.Unsigned.of_to.
        change Decimal.zero with (N.to_uint 0).
        now intro H; generalize (DecimalN.Unsigned.to_uint_inj _ _ H). }
      set (m := match nz with Decimal.Nil => _ | _ => _ end).
      assert (Hm : m = (Decimal.Neg (Decimal.unorm pnf))).
      { now revert Hnz; unfold m, nz, Decimal.unorm; fold nz; case nz. }
      rewrite Hm; unfold pnf.
      now rewrite <-DecimalPos.Unsigned.to_of, DecimalPos.Unsigned.of_to.
Qed.

Lemma to_of (d:hexadecimal) :
  to_hexadecimal (of_hexadecimal d) = Some (hnorme d).
Proof.
  unfold to_hexadecimal.
  pose (t10 := fun y => (y~0~0~0~0)%positive).
  assert (H : exists h e_den,
             Hexadecimal.nztail (Pos.to_hex_uint (Qden (of_hexadecimal d)))
             = (h, e_den)
             /\ (h = D1 Nil \/ h = D2 Nil \/ h = D4 Nil \/ h = D8 Nil)).
  { assert (H : forall p,
               Hexadecimal.nztail (Pos.to_hex_uint (Pos.iter (Pos.mul 2) 1%positive p))
               = ((match (Pos.to_nat p) mod 4 with 0%nat => D1 | 1 => D2 | 2 => D4 | _ => D8 end)%nat Nil,
                  (Pos.to_nat p / 4)%nat)).
    { intro p; clear d; rewrite Pos2Nat.inj_iter.
      fold (Nat.iter (Pos.to_nat p) (Pos.mul 2) 1%positive).
      set (n := Pos.to_nat p).
      fold (Nat.iter n t10 1%positive).
      set (nm4 := (n mod 4)%nat); set (nd4 := (n / 4)%nat).
      rewrite (Nat.div_mod n 4); [|now simpl].
      unfold nm4, nd4; clear nm4 nd4.
      generalize (Nat.mod_upper_bound n 4 ltac:(now simpl)).
      generalize (n mod 4); generalize (n / 4)%nat.
      intros d r Hr; clear p n.
      induction d.
      { simpl; revert Hr.
        do 4 (case r; [now simpl|clear r; intro r]).
        intro H; exfalso.
        now do 4 (generalize (lt_S_n _ _ H); clear H; intro H). }
      rewrite Nat.mul_succ_r, <-Nat.add_assoc, (Nat.add_comm 4), Nat.add_assoc.
      rewrite (Nat.add_comm _ 4).
      change (4 + _)%nat with (S (S (S (S (4 * d + r))))).
      rewrite !Unsigned.nat_iter_S.
      rewrite !Pos.mul_assoc.
      unfold Pos.to_hex_uint.
      change (2 * 2 *  2 * 2)%positive with 0x10%positive.
      set (n := Nat.iter _ _ _).
      change (Pos.to_little_hex_uint _) with (Unsigned.to_lu (16 * N.pos n)).
      rewrite Unsigned.to_lhex_tenfold.
      unfold Hexadecimal.nztail; rewrite rev_rev.
      rewrite <-(rev_rev (Unsigned.to_lu _)).
      set (m := _ (rev _)).
      replace m with (let (r, n) := let (r, n) := m in (rev r, n) in (rev r, n)).
      2:{ now case m; intros r' n'; rewrite rev_rev. }
      change (let (r, n) := m in (rev r, n))
        with (Hexadecimal.nztail (Pos.to_hex_uint n)).
      now unfold n; rewrite IHd, rev_rev; clear n m. }
    unfold of_hexadecimal.
    case d; intros i f; [|intro e]; unfold of_hexadecimal; simpl.
    - case (Z.of_nat _)%Z; [|intro p..];
        [now exists (D1 Nil), O; split; [|left]
        | |now exists (D1 Nil), O; split; [|left]].
      exists (D1 Nil), (Pos.to_nat p).
      split; [|now left]; simpl.
      change (Pos.iter _ _ _) with (Pos.iter (Pos.mul 2) 1%positive (4 * p)).
      rewrite H.
      rewrite Pos2Nat.inj_mul, Nat.mul_comm, Nat.div_mul; [|now simpl].
      now rewrite Nat.mod_mul; [|now simpl].
    - case (_ - _)%Z; [|intros p..]; [now exists (D1 Nil), O; split; [|left]..|].
      simpl Qden; rewrite H.
      eexists; eexists; split; [reflexivity|].
      case (_ mod _); [now left|intro n].
      case n; [now right; left|clear n; intro n].
      case n; [now right; right; left|clear n; intro n].
      now right; right; right. }
  generalize (HexadecimalPos.Unsigned.nztail_to_hex_uint (Qden (of_hexadecimal d))).
  destruct H as (h, (e, (He, Hh))); rewrite He; clear He.
  assert (Hn1 : forall p, N.pos (Pos.iter (Pos.mul 2) 1%positive p) = 1%N -> False).
  { intro p.
    rewrite Pos2Nat.inj_iter.
    case_eq (Pos.to_nat p); [|now simpl].
    intro H; exfalso; apply (lt_irrefl O).
    rewrite <-H at 2; apply Pos2Nat.is_pos. }
  assert (H16_2 : forall p, (16^p = 2^(4 * p))%positive).
  { intro p.
    apply (@f_equal _ _ (fun z => match z with Z.pos p => p | _ => 1%positive end)
                    (Z.pos _) (Z.pos _)).
    rewrite !Pos2Z.inj_pow_pos, !Z.pow_pos_fold, Pos2Z.inj_mul.
    now change 16%Z with (2^4)%Z; rewrite <-Z.pow_mul_r. }
  assert (HN16_2 : forall n, (16^n = 2^(4 * n))%N).
  { intro n.
    apply N2Z.inj; rewrite !N2Z.inj_pow, N2Z.inj_mul.
    change (Z.of_N 16) with (2^4)%Z.
    now rewrite <-Z.pow_mul_r; [| |apply N2Z.is_nonneg]. }
  assert (Hn1' : forall p, N.pos (Pos.iter (Pos.mul 16) 1%positive p) = 1%N -> False).
  { intro p; fold (16^p)%positive; rewrite H16_2; apply Hn1. }
  assert (Ht10inj : forall n m, t10 n = t10 m -> n = m).
  { intros n m H; generalize (f_equal Z.pos H); clear H.
    change (Z.pos (t10 n)) with (Z.mul 0x10 (Z.pos n)).
    change (Z.pos (t10 m)) with (Z.mul 0x10 (Z.pos m)).
    rewrite Z.mul_comm, (Z.mul_comm 0x10).
    intro H; generalize (f_equal (fun z => Z.div z 0x10) H); clear H.
    now rewrite !Z.div_mul; [|now simpl..]; intro H; inversion H. }
  assert (Ht2inj : forall n m, Pos.mul 2 n = Pos.mul 2 m -> n = m).
  { intros n m H; generalize (f_equal Z.pos H); clear H.
    change (Z.pos (Pos.mul 2 n)) with (Z.mul 2 (Z.pos n)).
    change (Z.pos (Pos.mul 2 m)) with (Z.mul 2 (Z.pos m)).
    rewrite Z.mul_comm, (Z.mul_comm 2).
    intro H; generalize (f_equal (fun z => Z.div z 2) H); clear H.
    now rewrite !Z.div_mul; [|now simpl..]; intro H; inversion H. }
  assert (Hinj : forall n m,
             Nat.iter n (Pos.mul 2) 1%positive = Nat.iter m (Pos.mul 2) 1%positive
             -> n = m).
  { induction n; [now intro m; case m|].
    intro m; case m; [now simpl|]; clear m; intro m.
    rewrite !Unsigned.nat_iter_S.
    intro H; generalize (Ht2inj _ _ H); clear H; intro H.
    now rewrite (IHn _ H). }
  change 4%Z with (Z.of_nat 4); rewrite <-Nat2Z.inj_mul.
  change 1%Z with (Z.of_nat 1); rewrite <-Nat2Z.inj_add.
  change 2%Z with (Z.of_nat 2); rewrite <-Nat2Z.inj_add.
  change 3%Z with (Z.of_nat 3); rewrite <-Nat2Z.inj_add.
  destruct Hh as [Hh|[Hh|[Hh|Hh]]]; rewrite Hh; clear h Hh.
  - case e; clear e; [|intro e]; simpl; unfold of_hexadecimal, hnorme.
    + case d; clear d; intros i f; [|intro e].
      * generalize (nb_digits_pos f).
        case f;
          [|now clear f; intro f; intros H1 H2; exfalso; revert H1 H2;
            case nb_digits;
            [intros H _; apply (lt_irrefl O), H|intros n _; apply Hn1]..].
        now intros _ _; simpl; rewrite to_of.
      * rewrite <-DecimalZ.to_of, DecimalZ.of_to.
        set (emf := (_ - _)%Z).
        case_eq emf; [|intro pemf..].
        ++ now simpl; rewrite to_of.
        ++ intros Hemf _; simpl.
           apply f_equal, f_equal2; [|reflexivity].
           rewrite !Pos2Nat.inj_iter.
           fold (Nat.iter (Pos.to_nat pemf) (Z.mul 2) (Z.of_hex_int (app_int i f))).
           fold (Nat.iter (Pos.to_nat pemf) double (norm (app_int i f))).
           induction Pos.to_nat; [now simpl; rewrite HexadecimalZ.to_of|].
           now rewrite !Unsigned.nat_iter_S, <-IHn, double_to_hex_int.
        ++ simpl Qden; intros _ H; exfalso; revert H; apply Hn1.
    + case d; clear d; intros i f; [|intro e'].
      * simpl; case_eq (nb_digits f); [|intros nf' Hnf'];
          [now simpl; intros _ H; exfalso; symmetry in H; revert H; apply Hn1'|].
        unfold Z.of_nat, Z.opp, Qnum, Qden.
        rewrite H16_2.
        fold (Pos.mul 2); fold (2^(Pos.of_succ_nat nf')~0~0)%positive.
        intro H; injection H; clear H.
        unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
        intro H; generalize (Hinj _ _ H); clear H; intro H.
        generalize (Pos2Nat.inj _ _ H); clear H; intro H; injection H.
        clear H; intro H; generalize (SuccNat2Pos.inj _ _ H); clear H.
        intros <-.
        rewrite to_of.
        rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
        do 4 apply f_equal.
        apply Pos2Nat.inj.
        rewrite SuccNat2Pos.id_succ.
        change (_~0)%positive with (4 * Pos.of_succ_nat nf')%positive.
        now rewrite Pos2Nat.inj_mul, SuccNat2Pos.id_succ.
      * set (nemf := (_ - _)%Z); intro H.
        assert (H' : exists pnemf, nemf = Z.neg pnemf); [|revert H].
        { revert H; case nemf; [|intro pnemf..]; [..|now intros _; exists pnemf];
            simpl Qden; intro H; exfalso; symmetry in H; revert H; apply Hn1'. }
        destruct H' as (pnemf,Hpnemf); rewrite Hpnemf.
        unfold Qnum, Qden.
        rewrite H16_2.
        intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
        intro H; generalize (Hinj _ _ H); clear H; intro H.
        generalize (Pos2Nat.inj _ _ H); clear H.
        intro H; revert Hpnemf; rewrite H; clear pnemf H; intro Hnemf.
        rewrite to_of.
        rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
        do 4 apply f_equal.
        apply Pos2Nat.inj.
        rewrite SuccNat2Pos.id_succ.
        change (_~0)%positive with (4 * Pos.of_succ_nat e)%positive.
        now rewrite Pos2Nat.inj_mul, SuccNat2Pos.id_succ.
  - simpl Pos.of_hex_uint.
    rewrite HN16_2.
    rewrite <-N.pow_succ_r; [|now apply N.le_0_l].
    rewrite <-N.succ_pos_spec.
    case d; clear d; intros i f; [|intro e']; unfold of_hexadecimal, hnorme.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
  - simpl Pos.of_hex_uint.
    rewrite HN16_2.
    change 4%N with (2 * 2)%N at 1; rewrite <-!N.mul_assoc.
    do 2 (rewrite <-N.pow_succ_r; [|now apply N.le_0_l]).
    rewrite <-N.succ_pos_spec.
    case d; clear d; intros i f; [|intro e']; unfold of_hexadecimal, hnorme.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite <-SuccNat2Pos.inj_succ.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite <-SuccNat2Pos.inj_succ.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
  - simpl Pos.of_hex_uint.
    rewrite HN16_2.
    change 8%N with (2 * 2 * 2)%N; rewrite <-!N.mul_assoc.
    do 3 (rewrite <-N.pow_succ_r; [|now apply N.le_0_l]).
    rewrite <-N.succ_pos_spec.
    case d; clear d; intros i f; [|intro e']; unfold of_hexadecimal, hnorme.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite <-!SuccNat2Pos.inj_succ.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
    + set (em4f := (_ - _)%Z).
      case_eq em4f; [|intros pem4f..]; intro Hpem4f;
        [now simpl; intros H; exfalso; symmetry in H; revert H; apply Hn1..|].
      unfold Qnum, Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H; intros ->.
      rewrite to_of.
      rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
      do 4 apply f_equal.
      apply Pos2Nat.inj.
      rewrite <-!SuccNat2Pos.inj_succ.
      rewrite SuccNat2Pos.id_succ.
      case e; [now simpl|intro e'']; simpl.
      unfold Pos.to_nat; simpl.
      now rewrite Pmult_nat_mult, SuccNat2Pos.id_succ, Nat.mul_comm.
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

Lemma to_hexadecimal_surj d : exists q, to_hexadecimal q = Some (hnorme d).
Proof.
  exists (of_hexadecimal d). apply to_of.
Qed.

Lemma of_hexadecimal_hnorme d : of_hexadecimal (hnorme d) = of_hexadecimal d.
Proof.
  unfold of_hexadecimal, hnorme.
  destruct d.
  - simpl Z.of_int; unfold Z.of_uint, Z.of_N, Pos.of_uint.
    rewrite Z.sub_0_l.
    set (n4f := (- _)%Z).
    case_eq n4f; [|intro pn4f..]; intro Hn4f.
    + apply f_equal2; [|reflexivity].
      rewrite app_int_nil_r.
      now rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to.
    + apply f_equal2; [|reflexivity].
      rewrite app_int_nil_r.
      generalize (app_int i f); intro i'.
      rewrite !Pos2Nat.inj_iter.
      generalize (Pos.to_nat pn4f); intro n.
      fold (Nat.iter n double (norm i')).
      fold (Nat.iter n (Z.mul 2) (Z.of_hex_int i')).
      induction n; [now simpl; rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to|].
      now rewrite !Unsigned.nat_iter_S, <-IHn, of_hex_int_double.
    + unfold nb_digits, Z.of_nat.
      rewrite Z.mul_0_r, Z.sub_0_r.
      rewrite <-DecimalZ.to_of, !DecimalZ.of_to.
      rewrite app_int_nil_r.
      now rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to.
  - set (nem4f := (_ - _)%Z).
    case_eq nem4f; [|intro pnem4f..]; intro Hnem4f.
    + apply f_equal2; [|reflexivity].
      rewrite app_int_nil_r.
      now rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to.
    + apply f_equal2; [|reflexivity].
      rewrite app_int_nil_r.
      generalize (app_int i f); intro i'.
      rewrite !Pos2Nat.inj_iter.
      generalize (Pos.to_nat pnem4f); intro n.
      fold (Nat.iter n double (norm i')).
      fold (Nat.iter n (Z.mul 2) (Z.of_hex_int i')).
      induction n; [now simpl; rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to|].
      now rewrite !Unsigned.nat_iter_S, <-IHn, of_hex_int_double.
    + unfold nb_digits, Z.of_nat.
      rewrite Z.mul_0_r, Z.sub_0_r.
      rewrite <-DecimalZ.to_of, !DecimalZ.of_to.
      rewrite app_int_nil_r.
      now rewrite <-HexadecimalZ.to_of, HexadecimalZ.of_to.
Qed.

Lemma of_inj d d' :
  of_hexadecimal d = of_hexadecimal d' -> hnorme d = hnorme d'.
Proof.
  intros.
  cut (Some (hnorme d) = Some (hnorme d')); [now intro H'; injection H'|].
  rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' :
  of_hexadecimal d = of_hexadecimal d' <-> hnorme d = hnorme d'.
Proof.
  split. apply of_inj. intros E. rewrite <- of_hexadecimal_hnorme, E.
  apply of_hexadecimal_hnorme.
Qed.
