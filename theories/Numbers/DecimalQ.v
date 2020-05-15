(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

Lemma of_to (q:Q) : forall d, to_decimal q = Some d -> of_decimal d = q.
Proof.
  cut (match to_decimal q with None => True | Some d => of_decimal d = q end).
  { now case to_decimal; [intros d <- d' Hd'; injection Hd'; intros ->|]. }
  destruct q as (num, den).
  unfold to_decimal; simpl.
  generalize (DecimalPos.Unsigned.nztail_to_uint den).
  case Decimal.nztail; intros u n.
  case u; clear u; [intros; exact I|intros; exact I|intro u|intros; exact I..].
  case u; clear u; [|intros; exact I..].
  unfold Pos.of_uint, Pos.of_uint_acc; rewrite N.mul_1_l.
  case n.
  - unfold of_decimal, app_int, app, Z.to_int; simpl.
    intro H; inversion H as (H1); clear H H1.
    case num; [reflexivity|intro pnum; fold (rev (rev (Pos.to_uint pnum)))..].
    + rewrite rev_rev; simpl.
      now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
    + rewrite rev_rev; simpl.
      now unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to.
  - clear n; intros n H.
    injection H; clear H; intros ->.
    case Nat.ltb.
    + unfold of_decimal.
      rewrite of_to.
      apply f_equal2; [|now simpl].
      unfold app_int, app, Z.to_int; simpl.
      now case num;
        [|intro pnum; fold (rev (rev (Pos.to_uint pnum)));
          rewrite rev_rev; unfold Z.of_int, Z.of_uint;
          rewrite DecimalPos.Unsigned.of_to..].
    + unfold of_decimal; case Nat.ltb_spec; intro Hn; simpl.
      * rewrite nb_digits_del_head; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply le_Sn_le].
        rewrite Z.sub_sub_distr, Z.sub_diag; simpl.
        rewrite <-(of_to num) at 4.
        now revert Hn; case Z.to_int; clear num; intros pnum Hn; simpl;
          (rewrite app_del_tail_head; [|now apply le_Sn_le]).
      * revert Hn.
        set (anum := match Z.to_int num with Pos i => i | _ => _ end).
        intro Hn.
        assert (H : exists l, nb_digits anum = S l).
        { exists (Nat.pred (nb_digits anum)); apply S_pred_pos.
          now unfold anum; case num;
            [apply Nat.lt_0_1|
             intro pnum; apply nb_digits_pos, Unsigned.to_uint_nonnil..]. }
        destruct H as (l, Hl); rewrite Hl.
        assert (H : forall n d, (nb_digits (Nat.iter n D0 d) = n + nb_digits d)%nat).
        { now intros n'; induction n'; intro d; [|simpl; rewrite IHn']. }
        rewrite H, Hl.
        rewrite Nat.add_succ_r, Nat.sub_add; [|now apply le_S_n; rewrite <-Hl].
        assert (H' : forall n d, Pos.of_uint (Nat.iter n D0 d) = Pos.of_uint d).
        { now intro n'; induction n'; intro d; [|simpl; rewrite IHn']. }
        now unfold anum; case num; simpl; [|intro pnum..];
          unfold app, Z.of_uint; simpl;
            rewrite H', ?DecimalPos.Unsigned.of_to.
Qed.

(* normalize without fractional part, for instance norme 12.3e-1 is 123e-2 *)
Definition dnorme (d:decimal) : decimal :=
  let '(i, f, e) :=
    match d with
    | Decimal i f => (i, f, Pos Nil)
    | DecimalExp i f e => (i, f, e)
    end in
  let i := norm (app_int i f) in
  let e := norm (Z.to_int (Z.of_int e - Z.of_nat (nb_digits f))) in
  match e with
  | Pos zero => Decimal i Nil
  | _ => DecimalExp i Nil e
  end.

(* normalize without exponent part, for instance norme 12.3e-1 is 1.23 *)
Definition dnormf (d:decimal) : decimal :=
  match dnorme d with
  | Decimal i _ => Decimal i Nil
  | DecimalExp i _ e =>
    match Z.of_int e with
    | Z0 => Decimal i Nil
    | Zpos e => Decimal (norm (app_int i (Pos.iter D0 Nil e))) Nil
    | Zneg e =>
      let ne := Pos.to_nat e in
      let ai := match i with Pos d | Neg d => d end in
      let ni := nb_digits ai in
      if ne <? ni then
        Decimal (del_tail_int ne i) (del_head (ni - ne) ai)
      else
        let z := match i with Pos _ => Pos zero | Neg _ => Neg zero end in
        Decimal z (Nat.iter (ne - ni) D0 ai)
    end
  end.

Lemma dnorme_spec d :
  match dnorme d with
  | Decimal i Nil => i = norm i
  | DecimalExp i Nil e => i = norm i /\ e = norm e /\ e <> Pos zero
  | _ => False
  end.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold dnorme; simpl.
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); [intros->|intro Hne'].
    + now rewrite norm_invol.
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      replace m with r; [now unfold r; rewrite !norm_invol|].
      unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
      now case e''; [|intro e'''; case e'''..].
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); [intros->|intro Hne'].
    + now rewrite norm_invol.
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      replace m with r; [now unfold r; rewrite !norm_invol|].
      unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
      now case e''; [|intro e'''; case e'''..].
Qed.

Lemma dnormf_spec d :
  match dnormf d with
  | Decimal i f => i = Neg zero \/ i = norm i
  | _ => False
  end.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold dnormf, dnorme; simpl.
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); [intros->|intro Hne'].
    + now right; rewrite norm_invol.
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite <-DecimalZ.to_of, DecimalZ.of_to.
      case_eq (Z.of_int e'); [|intros pe'..]; intro Hpe';
        [now right; rewrite norm_invol..|].
      case Nat.ltb_spec.
      * now intro H; rewrite (norm_del_tail_int_norm _ _ H); right.
      * now intros _; case norm; intros _; [right|left].
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); [intros->|intro Hne'].
    + now right; rewrite norm_invol.
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite <-DecimalZ.to_of, DecimalZ.of_to.
      case_eq (Z.of_int e'); [|intros pe'..]; intro Hpe';
        [now right; rewrite norm_invol..|].
      case Nat.ltb_spec.
      * now intro H; rewrite (norm_del_tail_int_norm _ _ H); right.
      * now intros _; case norm; intros _; [right|left].
Qed.

Lemma dnorme_invol d : dnorme (dnorme d) = dnorme d.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold dnorme; simpl.
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); intro Hne'.
    + rewrite Hne'; simpl; rewrite app_int_nil_r, norm_invol.
      revert Hne'.
      rewrite <-to_of.
      change (Pos zero) with (Z.to_int 0).
      intro H; generalize (to_int_inj _ _ H); clear H.
      unfold e'; rewrite DecimalZ.of_to.
      now case f; [rewrite app_int_nil_r|..].
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite <-DecimalZ.to_of, DecimalZ.of_to.
      unfold nb_digits, Z.of_nat; rewrite Z.sub_0_r, to_of, norm_invol.
      rewrite app_int_nil_r, norm_invol.
      set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
      now case e''; [|intro e'''; case e'''..].
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); intro Hne'.
    + rewrite Hne'; simpl; rewrite app_int_nil_r, norm_invol.
      revert Hne'.
      rewrite <-to_of.
      change (Pos zero) with (Z.to_int 0).
      intro H; generalize (to_int_inj _ _ H); clear H.
      unfold e'; rewrite DecimalZ.of_to.
      now case f; [rewrite app_int_nil_r|..].
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite <-DecimalZ.to_of, DecimalZ.of_to.
      unfold nb_digits, Z.of_nat; rewrite Z.sub_0_r, to_of, norm_invol.
      rewrite app_int_nil_r, norm_invol.
      set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
      now case e''; [|intro e'''; case e'''..].
Qed.

Lemma dnormf_invol d : dnormf (dnormf d) = dnormf d.
Proof.
  case d; clear d; intros i f; [|intro e]; unfold dnormf, dnorme; simpl.
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); intro Hne'.
    + rewrite Hne'; simpl; rewrite app_int_nil_r, norm_invol.
      revert Hne'.
      rewrite <-to_of.
      change (Pos zero) with (Z.to_int 0).
      intro H; generalize (to_int_inj _ _ H); clear H.
      unfold e'; rewrite DecimalZ.of_to.
      now case f; [rewrite app_int_nil_r|..].
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite of_int_norm.
      case_eq (Z.of_int e'); [|intro pe'..]; intro Hnpe';
        [now simpl; rewrite app_int_nil_r, norm_invol..|].
      case Nat.ltb_spec; intro Hpe'.
      * rewrite nb_digits_del_head; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply Nat.lt_le_incl].
        simpl.
        rewrite Z.sub_sub_distr, Z.sub_diag, Z.add_0_l.
        rewrite <-DecimalZ.to_of, DecimalZ.of_to.
        rewrite positive_nat_Z; simpl.
        unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        rewrite app_int_del_tail_head; [|now apply Nat.lt_le_incl].
        now rewrite norm_invol, (proj2 (Nat.ltb_lt _ _) Hpe').
      * simpl.
        rewrite nb_digits_iter_D0.
        rewrite (Nat.sub_add _ _ Hpe').
        rewrite <-DecimalZ.to_of, DecimalZ.of_to.
        rewrite positive_nat_Z; simpl.
        unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        revert Hpe'.
        set (i' := norm (app_int i f)).
        case_eq i'; intros u Hu Hpe'.
        ++ simpl; unfold app; simpl.
           rewrite unorm_D0, unorm_iter_D0.
           assert (Hu' : unorm u = u).
           { generalize (f_equal norm Hu).
             unfold i'; rewrite norm_invol; fold i'.
             now simpl; rewrite Hu; intro H; injection H. }
           now rewrite Hu', (proj2 (Nat.ltb_ge _ _) Hpe').
        ++ simpl; rewrite nzhead_iter_D0.
           assert (Hu' : nzhead u = u).
           { generalize (f_equal norm Hu).
             unfold i'; rewrite norm_invol; fold i'.
             now rewrite Hu; simpl; case (nzhead u); [|intros u' H; injection H..]. }
           rewrite Hu'.
           assert (Hu'' : u <> Nil).
           { intro H; revert Hu; rewrite H; unfold i'.
             now case app_int; intro u'; [|simpl; case nzhead]. }
           set (m := match u with Nil => Pos zero | _ => _ end).
           assert (H : m = Neg u); [|rewrite H; clear m H].
           { now revert Hu''; unfold m; case u. }
           now rewrite (proj2 (Nat.ltb_ge _ _) Hpe').
  - set (e' := Z.to_int _).
    case (int_eq_dec (norm e') (Pos zero)); intro Hne'.
    + rewrite Hne'; simpl; rewrite app_int_nil_r, norm_invol.
      revert Hne'.
      rewrite <-to_of.
      change (Pos zero) with (Z.to_int 0).
      intro H; generalize (to_int_inj _ _ H); clear H.
      unfold e'; rewrite DecimalZ.of_to.
      now case f; [rewrite app_int_nil_r|..].
    + set (r := DecimalExp _ _ _).
      set (m := match norm e' with Pos zero => _ | _ => _ end).
      assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
      { unfold m; revert Hne'; case (norm e'); intro e''; [|now simpl].
        now case e''; [|intro e'''; case e'''..]. }
      rewrite of_int_norm.
      case_eq (Z.of_int e'); [|intro pe'..]; intro Hnpe';
        [now simpl; rewrite app_int_nil_r, norm_invol..|].
      case Nat.ltb_spec; intro Hpe'.
      * rewrite nb_digits_del_head; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply Nat.le_sub_l].
        rewrite Nat2Z.inj_sub; [|now apply Nat.lt_le_incl].
        simpl.
        rewrite Z.sub_sub_distr, Z.sub_diag, Z.add_0_l.
        rewrite <-DecimalZ.to_of, DecimalZ.of_to.
        rewrite positive_nat_Z; simpl.
        unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        rewrite app_int_del_tail_head; [|now apply Nat.lt_le_incl].
        now rewrite norm_invol, (proj2 (Nat.ltb_lt _ _) Hpe').
      * simpl.
        rewrite nb_digits_iter_D0.
        rewrite (Nat.sub_add _ _ Hpe').
        rewrite <-DecimalZ.to_of, DecimalZ.of_to.
        rewrite positive_nat_Z; simpl.
        unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
        revert Hpe'.
        set (i' := norm (app_int i f)).
        case_eq i'; intros u Hu Hpe'.
        ++ simpl; unfold app; simpl.
           rewrite unorm_D0, unorm_iter_D0.
           assert (Hu' : unorm u = u).
           { generalize (f_equal norm Hu).
             unfold i'; rewrite norm_invol; fold i'.
             now simpl; rewrite Hu; intro H; injection H. }
           now rewrite Hu', (proj2 (Nat.ltb_ge _ _) Hpe').
        ++ simpl; rewrite nzhead_iter_D0.
           assert (Hu' : nzhead u = u).
           { generalize (f_equal norm Hu).
             unfold i'; rewrite norm_invol; fold i'.
             now rewrite Hu; simpl; case (nzhead u); [|intros u' H; injection H..]. }
           rewrite Hu'.
           assert (Hu'' : u <> Nil).
           { intro H; revert Hu; rewrite H; unfold i'.
             now case app_int; intro u'; [|simpl; case nzhead]. }
           set (m := match u with Nil => Pos zero | _ => _ end).
           assert (H : m = Neg u); [|rewrite H; clear m H].
           { now revert Hu''; unfold m; case u. }
           now rewrite (proj2 (Nat.ltb_ge _ _) Hpe').
Qed.

Lemma to_of (d:decimal) :
  to_decimal (of_decimal d) = Some (dnorme d)
  \/ to_decimal (of_decimal d) = Some (dnormf d).
Proof.
  unfold to_decimal.
  pose (t10 := fun y => ((y + y~0~0)~0)%positive).
  assert (H : exists e_den,
             Decimal.nztail (Pos.to_uint (Qden (of_decimal d))) = (D1 Nil, e_den)).
  { assert (H : forall p,
               Decimal.nztail (Pos.to_uint (Pos.iter t10 1%positive p))
               = (D1 Nil, Pos.to_nat p)).
    { intro p; rewrite Pos2Nat.inj_iter.
      fold (Nat.iter (Pos.to_nat p) t10 1%positive).
      induction (Pos.to_nat p); [now simpl|].
      rewrite DecimalPos.Unsigned.nat_iter_S.
      unfold Pos.to_uint.
      change (Pos.to_little_uint _)
        with (Unsigned.to_lu (10 * N.pos (Nat.iter n t10 1%positive))).
      rewrite Unsigned.to_ldec_tenfold.
      revert IHn; unfold Pos.to_uint.
      unfold Decimal.nztail; rewrite !rev_rev; simpl.
      set (f'' := _ (Pos.to_little_uint _)).
      now case f''; intros r n' H; inversion H. }
    case d; intros i f; [|intro e]; unfold of_decimal; simpl.
    - case (- Z.of_nat _)%Z; [|intro p..]; simpl; [now exists O..|].
      exists (Pos.to_nat p); apply H.
    - case (_ - _)%Z; [|intros p..]; simpl; [now exists O..|].
      exists (Pos.to_nat p); apply H. }
  generalize (DecimalPos.Unsigned.nztail_to_uint (Qden (of_decimal d))).
  destruct H as (e, He); rewrite He; clear He; simpl.
  assert (Hn1 : forall p, N.pos (Pos.iter t10 1%positive p) = 1%N -> False).
  { intro p.
    rewrite Pos2Nat.inj_iter.
    case_eq (Pos.to_nat p); [|now simpl].
    intro H; exfalso; apply (lt_irrefl O).
    rewrite <-H at 2; apply Pos2Nat.is_pos. }
  assert (Ht10inj : forall n m, t10 n = t10 m -> n = m).
  { intros n m H; generalize (f_equal Z.pos H); clear H.
    change (Z.pos (t10 n)) with (Z.mul 10 (Z.pos n)).
    change (Z.pos (t10 m)) with (Z.mul 10 (Z.pos m)).
    rewrite Z.mul_comm, (Z.mul_comm 10).
    intro H; generalize (f_equal (fun z => Z.div z 10) H); clear H.
    now rewrite !Z.div_mul; [|now simpl..]; intro H; inversion H. }
  assert (Hinj : forall n m,
             Nat.iter n t10 1%positive = Nat.iter m t10 1%positive -> n = m).
  { induction n; [now intro m; case m|].
    intro m; case m; [now simpl|]; clear m; intro m.
    rewrite !Unsigned.nat_iter_S.
    intro H; generalize (Ht10inj _ _ H); clear H; intro H.
    now rewrite (IHn _ H). }
  case e; clear e; [|intro e]; simpl; unfold of_decimal, dnormf, dnorme.
  - case d; clear d; intros i f; [|intro e]; simpl.
    + intro H; left; revert H.
      generalize (nb_digits_pos f).
      case f;
        [|now clear f; intro f; intros H1 H2; exfalso; revert H1 H2;
          case nb_digits; simpl;
          [intros H _; apply (lt_irrefl O), H|intros n _; apply Hn1]..].
      now intros _ _; simpl; rewrite to_of.
    + intro H; right; revert H.
      rewrite <-to_of, DecimalZ.of_to.
      set (emf := (_ - _)%Z).
      case_eq emf; [|intro pemf..].
      * now simpl; rewrite to_of.
      * set (r := DecimalExp _ _ _).
        set (m := match _ with Pos _ => _ | _ => r end).
        assert (H : m = r).
        { unfold m, Z.to_int.
          generalize (Unsigned.to_uint_nonzero pemf).
          now case Pos.to_uint; [|intro u; case u..]. }
        rewrite H; unfold r; clear H m r.
        rewrite DecimalZ.of_to.
        simpl Qnum.
        intros Hpemf _.
        apply f_equal; apply f_equal2; [|reflexivity].
        rewrite !Pos2Nat.inj_iter.
        set (n := _ pemf).
        fold (Nat.iter n (Z.mul 10) (Z.of_int (app_int i f))).
        fold (Nat.iter n D0 Nil).
        rewrite <-of_int_iter_D0, to_of.
        now rewrite norm_app_int_norm; [|induction n].
      * simpl Qden; intros _ H; exfalso; revert H; apply Hn1.
  - case d; clear d; intros i f; [|intro e']; simpl.
    + case_eq (nb_digits f); [|intros nf' Hnf'];
        [now simpl; intros _ H; exfalso; symmetry in H; revert H; apply Hn1|].
      unfold Z.of_nat, Z.opp.
      simpl Qden.
      intro H; injection H; clear H; unfold Pos.pow.
      rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (SuccNat2Pos.inj _ _ ((Pos2Nat.inj _ _ H))); clear H.
      intro He; rewrite <-He; clear e He.
      simpl Qnum.
      case Nat.ltb; [left|right].
      * now rewrite <-to_of, DecimalZ.of_to, to_of.
      * rewrite to_of.
        set (nif := norm _).
        set (anif := match nif with Pos i0 => i0 | _ => _ end).
        set (r := DecimalExp nif Nil _).
        set (m := match _ with Pos _ => _ | _ => r end).
        assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
        { now unfold m; rewrite <-to_of, DecimalZ.of_to. }
        rewrite <-to_of, !DecimalZ.of_to.
        fold anif.
        now rewrite SuccNat2Pos.id_succ.
    + set (nemf := (_ - _)%Z); intro H.
      assert (H' : exists pnemf, nemf = Z.neg pnemf); [|revert H].
      { revert H; case nemf; [|intro pnemf..]; [..|now intros _; exists pnemf];
          simpl Qden; intro H; exfalso; symmetry in H; revert H; apply Hn1. }
      destruct H' as (pnemf,Hpnemf); rewrite Hpnemf.
      simpl Qden.
      intro H; injection H; clear H; unfold Pos.pow; rewrite !Pos2Nat.inj_iter.
      intro H; generalize (Hinj _ _ H); clear H; intro H.
      generalize (Pos2Nat.inj _ _ H); clear H.
      intro H; revert Hpnemf; rewrite H; clear pnemf H; intro Hnemf.
      simpl Qnum.
      case Nat.ltb; [left|right].
      * now rewrite <-to_of, DecimalZ.of_to, to_of.
      * rewrite to_of.
        set (nif := norm _).
        set (anif := match nif with Pos i0 => i0 | _ => _ end).
        set (r := DecimalExp nif Nil _).
        set (m := match _ with Pos _ => _ | _ => r end).
        assert (H : m = r); [|rewrite H; unfold m, r; clear m r H].
        { now unfold m; rewrite <-to_of, DecimalZ.of_to. }
        rewrite <-to_of, !DecimalZ.of_to.
        fold anif.
        now rewrite SuccNat2Pos.id_succ.
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

Lemma to_decimal_surj d :
  exists q, to_decimal q = Some (dnorme d) \/ to_decimal q = Some (dnormf d).
Proof.
  exists (of_decimal d). apply to_of.
Qed.

Lemma of_decimal_dnorme d : of_decimal (dnorme d) = of_decimal d.
Proof.
  unfold of_decimal, dnorme.
  destruct d.
  - rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
    case_eq (nb_digits f); [|intro nf]; intro Hnf.
    + now simpl; rewrite app_int_nil_r, <-DecimalZ.to_of, DecimalZ.of_to.
    + simpl; rewrite Z.sub_0_r.
      unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
      rewrite app_int_nil_r.
      now rewrite <-DecimalZ.to_of, DecimalZ.of_to.
  - rewrite <-DecimalZ.to_of, DecimalZ.of_to; simpl.
    set (emf := (_ - _)%Z).
    case_eq emf; [|intro pemf..]; intro Hemf.
    + now simpl; rewrite app_int_nil_r, <-DecimalZ.to_of, DecimalZ.of_to.
    + simpl.
      set (r := DecimalExp _ Nil _).
      set (m := match Pos.to_uint pemf with zero => _ | _ => r end).
      assert (H : m = r); [|rewrite H; unfold r; clear m r H].
      { generalize (Unsigned.to_uint_nonzero pemf).
        now unfold m; case Pos.to_uint; [|intro u; case u|..]. }
      simpl; rewrite Z.sub_0_r.
      unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
      rewrite app_int_nil_r.
      now rewrite <-DecimalZ.to_of, DecimalZ.of_to.
    + simpl.
      unfold Z.of_uint; rewrite DecimalPos.Unsigned.of_to; simpl.
      rewrite app_int_nil_r.
      now rewrite <-DecimalZ.to_of, DecimalZ.of_to.
Qed.

Lemma of_decimal_dnormf d : of_decimal (dnormf d) = of_decimal d.
Proof.
  rewrite <-(of_decimal_dnorme d).
  unfold of_decimal, dnormf.
  assert (H : match dnorme d with Decimal _ f | DecimalExp _ f _ => f end = Nil).
  { now unfold dnorme; destruct d;
      (case norm; intro d; [case d; [|intro u; case u|..]|]). }
  revert H; generalize (dnorme d); clear d; intro d.
  destruct d; intro H; rewrite H; clear H; [now simpl|].
  case (Z.of_int e); clear e; [|intro e..].
  - now simpl.
  - simpl.
    rewrite app_int_nil_r.
    apply f_equal2; [|reflexivity].
    rewrite app_int_nil_r.
    rewrite <-DecimalZ.to_of, DecimalZ.of_to.
    rewrite !Pos2Nat.inj_iter.
    fold (Nat.iter (Pos.to_nat e) D0 Nil).
    now rewrite of_int_iter_D0.
  - simpl.
    set (ai := match i with Pos _ => _ | _ => _ end).
    rewrite app_int_nil_r.
    case Nat.ltb_spec; intro Hei; simpl.
    + rewrite nb_digits_del_head; [|now apply Nat.le_sub_l].
      rewrite Nat2Z.inj_sub; [|now apply Nat.le_sub_l].
      rewrite Nat2Z.inj_sub; [|now apply le_Sn_le].
      rewrite Z.sub_sub_distr, Z.sub_diag; simpl.
      rewrite positive_nat_Z; simpl.
      now revert Hei; unfold ai; case i; clear i ai; intros i Hei; simpl;
        (rewrite app_del_tail_head; [|now apply le_Sn_le]).
    + set (n := nb_digits _).
      assert (H : (n = Pos.to_nat e - nb_digits ai + nb_digits ai)%nat).
      { unfold n; induction (_ - _)%nat; [now simpl|].
        now rewrite Unsigned.nat_iter_S; simpl; rewrite IHn0. }
      rewrite H; clear n H.
      rewrite Nat2Z.inj_add, (Nat2Z.inj_sub _ _ Hei).
      rewrite <-Z.sub_sub_distr, Z.sub_diag, Z.sub_0_r.
      rewrite positive_nat_Z; simpl.
      rewrite <-(DecimalZ.of_to (Z.of_int (app_int _ _))), DecimalZ.to_of.
      rewrite <-(DecimalZ.of_to (Z.of_int i)), DecimalZ.to_of.
      apply f_equal2; [|reflexivity]; apply f_equal.
      now unfold ai; case i; clear i ai Hei; intro i;
        (induction (_ - _)%nat; [|rewrite <-IHn]).
Qed.
