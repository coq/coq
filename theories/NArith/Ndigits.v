(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool Morphisms Setoid Bvector BinPos BinNat PeanoNat Pnat Nnat.

Local Open Scope N_scope.

(** This file is mostly obsolete, see directly [BinNat] now. *)

(** Compatibility names for some bitwise operations *)

Notation Pxor := Pos.lxor (only parsing).
Notation Nxor := N.lxor (only parsing).
Notation Pbit := Pos.testbit_nat (only parsing).
Notation Nbit := N.testbit_nat (only parsing).

Notation Nxor_eq := N.lxor_eq (only parsing).
Notation Nxor_comm := N.lxor_comm (only parsing).
Notation Nxor_assoc := N.lxor_assoc (only parsing).
Notation Nxor_neutral_left := N.lxor_0_l (only parsing).
Notation Nxor_neutral_right := N.lxor_0_r (only parsing).
Notation Nxor_nilpotent := N.lxor_nilpotent (only parsing).

(** Equivalence of bit-testing functions,
    either with index in [N] or in [nat]. *)

Lemma Ptestbit_Pbit :
 forall p n, Pos.testbit p (N.of_nat n) = Pos.testbit_nat p n.
Proof.
 induction p as [p IH|p IH| ]; intros [|n]; simpl; trivial;
  rewrite <- IH; f_equal; rewrite (pred_Sn n) at 2; now rewrite Nat2N.inj_pred.
Qed.

Lemma Ntestbit_Nbit : forall a n, N.testbit a (N.of_nat n) = N.testbit_nat a n.
Proof.
 destruct a. trivial. apply Ptestbit_Pbit.
Qed.

Lemma Pbit_Ptestbit :
 forall p n, Pos.testbit_nat p (N.to_nat n) = Pos.testbit p n.
Proof.
 intros; now rewrite <- Ptestbit_Pbit, N2Nat.id.
Qed.

Lemma Nbit_Ntestbit :
 forall a n, N.testbit_nat a (N.to_nat n) = N.testbit a n.
Proof.
 destruct a. trivial. apply Pbit_Ptestbit.
Qed.

(** Equivalence of shifts, index in [N] or [nat] *)

Lemma Nshiftr_nat_S : forall a n,
 N.shiftr_nat a (S n) = N.div2 (N.shiftr_nat a n).
Proof.
 reflexivity.
Qed.

Lemma Nshiftl_nat_S : forall a n,
 N.shiftl_nat a (S n) = N.double (N.shiftl_nat a n).
Proof.
 reflexivity.
Qed.

Lemma Nshiftr_nat_equiv :
 forall a n, N.shiftr_nat a (N.to_nat n) = N.shiftr a n.
Proof.
 intros a [|n]; simpl. unfold N.shiftr_nat.
 trivial.
 symmetry. apply Pos2Nat.inj_iter.
Qed.

Lemma Nshiftr_equiv_nat :
 forall a n, N.shiftr a (N.of_nat n) = N.shiftr_nat a n.
Proof.
 intros. now rewrite <- Nshiftr_nat_equiv, Nat2N.id.
Qed.

Lemma Nshiftl_nat_equiv :
 forall a n, N.shiftl_nat a (N.to_nat n) = N.shiftl a n.
Proof.
 intros [|a] [|n]; simpl; unfold N.shiftl_nat; trivial.
 induction (Pos.to_nat n) as [|? H]; simpl; now try rewrite H.
 rewrite <- Pos2Nat.inj_iter. symmetry. now apply Pos.iter_swap_gen.
Qed.

Lemma Nshiftl_equiv_nat :
 forall a n, N.shiftl a (N.of_nat n) = N.shiftl_nat a n.
Proof.
 intros. now rewrite <- Nshiftl_nat_equiv, Nat2N.id.
Qed.

(** Correctness proofs for shifts, nat version *)

Lemma Nshiftr_nat_spec : forall a n m,
  N.testbit_nat (N.shiftr_nat a n) m = N.testbit_nat a (m+n).
Proof.
 induction n; intros m.
 now rewrite <- plus_n_O.
 simpl. rewrite <- plus_n_Sm, <- plus_Sn_m, <- IHn.
 destruct (N.shiftr_nat a n) as [|[p|p|]]; simpl; trivial.
Qed.

Lemma Nshiftl_nat_spec_high : forall a n m, (n<=m)%nat ->
  N.testbit_nat (N.shiftl_nat a n) m = N.testbit_nat a (m-n).
Proof.
 induction n; intros m H.
 - now rewrite Nat.sub_0_r.
 - destruct m.
   + inversion H.
   + apply le_S_n in H.
     simpl. rewrite <- IHn; trivial.
     destruct (N.shiftl_nat a n) as [|[p|p|]]; simpl; trivial.
Qed.

Lemma Nshiftl_nat_spec_low : forall a n m, (m<n)%nat ->
 N.testbit_nat (N.shiftl_nat a n) m = false.
Proof.
 induction n; intros m H. inversion H.
 rewrite Nshiftl_nat_S.
 destruct m.
 - destruct (N.shiftl_nat a n); trivial.
 - apply Lt.lt_S_n in H.
   specialize (IHn m H).
   destruct (N.shiftl_nat a n); trivial.
Qed.

(** A left shift for positive numbers (used in BigN) *)

Lemma Pshiftl_nat_0 : forall p, Pos.shiftl_nat p 0 = p.
Proof. reflexivity. Qed.

Lemma Pshiftl_nat_S :
 forall p n, Pos.shiftl_nat p (S n) = xO (Pos.shiftl_nat p n).
Proof. reflexivity. Qed.

Lemma Pshiftl_nat_N :
 forall p n, Npos (Pos.shiftl_nat p n) = N.shiftl_nat (Npos p) n.
Proof.
 unfold Pos.shiftl_nat, N.shiftl_nat.
 induction n; simpl; auto. now rewrite <- IHn.
Qed.

Lemma Pshiftl_nat_plus : forall n m p,
  Pos.shiftl_nat p (m + n) = Pos.shiftl_nat (Pos.shiftl_nat p n) m.
Proof.
 induction m; simpl; intros. reflexivity.
 now f_equal.
Qed.

(** Semantics of bitwise operations with respect to [N.testbit_nat] *)

Lemma Pxor_semantics p p' n :
 N.testbit_nat (Pos.lxor p p') n = xorb (Pos.testbit_nat p n) (Pos.testbit_nat p' n).
Proof.
 rewrite <- Ntestbit_Nbit, <- !Ptestbit_Pbit. apply N.pos_lxor_spec.
Qed.

Lemma Nxor_semantics a a' n :
 N.testbit_nat (N.lxor a a') n = xorb (N.testbit_nat a n) (N.testbit_nat a' n).
Proof.
 rewrite <- !Ntestbit_Nbit. apply N.lxor_spec.
Qed.

Lemma Por_semantics p p' n :
 Pos.testbit_nat (Pos.lor p p') n = (Pos.testbit_nat p n) || (Pos.testbit_nat p' n).
Proof.
 rewrite <- !Ptestbit_Pbit. apply N.pos_lor_spec.
Qed.

Lemma Nor_semantics a a' n :
 N.testbit_nat (N.lor a a') n = (N.testbit_nat a n) || (N.testbit_nat a' n).
Proof.
 rewrite <- !Ntestbit_Nbit. apply N.lor_spec.
Qed.

Lemma Pand_semantics p p' n :
 N.testbit_nat (Pos.land p p') n = (Pos.testbit_nat p n) && (Pos.testbit_nat p' n).
Proof.
 rewrite <- Ntestbit_Nbit, <- !Ptestbit_Pbit. apply N.pos_land_spec.
Qed.

Lemma Nand_semantics a a' n :
 N.testbit_nat (N.land a a') n = (N.testbit_nat a n) && (N.testbit_nat a' n).
Proof.
 rewrite <- !Ntestbit_Nbit. apply N.land_spec.
Qed.

Lemma Pdiff_semantics p p' n :
 N.testbit_nat (Pos.ldiff p p') n = (Pos.testbit_nat p n) && negb (Pos.testbit_nat p' n).
Proof.
 rewrite <- Ntestbit_Nbit, <- !Ptestbit_Pbit. apply N.pos_ldiff_spec.
Qed.

Lemma Ndiff_semantics a a' n :
 N.testbit_nat (N.ldiff a a') n = (N.testbit_nat a n) && negb (N.testbit_nat a' n).
Proof.
 rewrite <- !Ntestbit_Nbit. apply N.ldiff_spec.
Qed.

(** Equality over functional streams of bits *)

Definition eqf (f g:nat -> bool) := forall n:nat, f n = g n.

Program Instance eqf_equiv : Equivalence eqf.

Local Infix "==" := eqf (at level 70, no associativity).

(** If two numbers produce the same stream of bits, they are equal. *)

Local Notation Step H := (fun n => H (S n)).

Lemma Pbit_faithful_0 : forall p, ~(Pos.testbit_nat p == (fun _ => false)).
Proof.
 induction p as [p IHp|p IHp| ]; intros H; try discriminate (H O).
  apply (IHp (Step H)).
Qed.

Lemma Pbit_faithful : forall p p', Pos.testbit_nat p == Pos.testbit_nat p' -> p = p'.
Proof.
 induction p as [p IHp|p IHp| ]; intros [p'|p'|] H; trivial;
  try discriminate (H O).
 f_equal. apply (IHp _ (Step H)).
 destruct (Pbit_faithful_0 _ (Step H)).
 f_equal. apply (IHp _ (Step H)).
 symmetry in H. destruct (Pbit_faithful_0 _ (Step H)).
Qed.

Lemma Nbit_faithful : forall n n', N.testbit_nat n == N.testbit_nat n' -> n = n'.
Proof.
 intros [|p] [|p'] H; trivial.
 symmetry in H. destruct (Pbit_faithful_0 _ H).
 destruct (Pbit_faithful_0 _ H).
 f_equal. apply Pbit_faithful, H.
Qed.

Lemma Nbit_faithful_iff : forall n n', N.testbit_nat n == N.testbit_nat n' <-> n = n'.
Proof.
 split. apply Nbit_faithful. intros; now subst.
Qed.

Local Close Scope N_scope.

(** Checking whether a number is odd, i.e.
   if its lower bit is set. *)

Notation Nbit0 := N.odd (only parsing).

Definition Nodd (n:N) := N.odd n = true.
Definition Neven (n:N) := N.odd n = false.

Lemma Nbit0_correct : forall n:N, N.testbit_nat n 0 = N.odd n.
Proof.
  destruct n; trivial.
  destruct p; trivial.
Qed.

Lemma Ndouble_bit0 : forall n:N, N.odd (N.double n) = false.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_plus_one_bit0 :
 forall n:N, N.odd (N.succ_double n) = true.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndiv2_double :
 forall n:N, Neven n -> N.double (N.div2 n) = n.
Proof.
  destruct n. trivial. destruct p. intro H. discriminate H.
  intros. reflexivity.
  intro H. discriminate H.
Qed.

Lemma Ndiv2_double_plus_one :
 forall n:N, Nodd n -> N.succ_double (N.div2 n) = n.
Proof.
  destruct n. intro. discriminate H.
  destruct p. intros. reflexivity.
  intro H. discriminate H.
  intro. reflexivity.
Qed.

Lemma Ndiv2_correct :
 forall (a:N) (n:nat), N.testbit_nat (N.div2 a) n = N.testbit_nat a (S n).
Proof.
  destruct a; trivial.
  destruct p; trivial.
Qed.

Lemma Nxor_bit0 :
 forall a a':N, N.odd (N.lxor a a') = xorb (N.odd a) (N.odd a').
Proof.
  intros. rewrite <- Nbit0_correct, (Nxor_semantics a a' O).
  rewrite Nbit0_correct, Nbit0_correct. reflexivity.
Qed.

Lemma Nxor_div2 :
 forall a a':N, N.div2 (N.lxor a a') = N.lxor (N.div2 a) (N.div2 a').
Proof.
  intros. apply Nbit_faithful. unfold eqf. intro.
  rewrite (Nxor_semantics (N.div2 a) (N.div2 a') n), Ndiv2_correct, (Nxor_semantics a a' (S n)).
  rewrite 2! Ndiv2_correct.
  reflexivity.
Qed.

Lemma Nneg_bit0 :
 forall a a':N,
   N.odd (N.lxor a a') = true -> N.odd a = negb (N.odd a').
Proof.
  intros.
  rewrite <- true_xorb, <- H, Nxor_bit0, xorb_assoc, 
    xorb_nilpotent, xorb_false.
  reflexivity.
Qed.

Lemma Nneg_bit0_1 :
 forall a a':N, N.lxor a a' = Npos 1 -> N.odd a = negb (N.odd a').
Proof.
  intros. apply Nneg_bit0. rewrite H. reflexivity.
Qed.

Lemma Nneg_bit0_2 :
 forall (a a':N) (p:positive),
   N.lxor a a' = Npos (xI p) -> N.odd a = negb (N.odd a').
Proof.
  intros. apply Nneg_bit0. rewrite H. reflexivity.
Qed.

Lemma Nsame_bit0 :
 forall (a a':N) (p:positive),
   N.lxor a a' = Npos (xO p) -> N.odd a = N.odd a'.
Proof.
  intros. rewrite <- (xorb_false (N.odd a)).
  assert (H0: N.odd (Npos (xO p)) = false) by reflexivity.
  rewrite <- H0, <- H, Nxor_bit0, <- xorb_assoc, xorb_nilpotent, false_xorb.
    reflexivity.
Qed.

(** a lexicographic order on bits, starting from the lowest bit *)

Fixpoint Nless_aux (a a':N) (p:positive) : bool :=
  match p with
  | xO p' => Nless_aux (N.div2 a) (N.div2 a') p'
  | _ => andb (negb (N.odd a)) (N.odd a')
  end.

Definition Nless (a a':N) :=
  match N.lxor a a' with
  | N0 => false
  | Npos p => Nless_aux a a' p
  end.

Lemma Nbit0_less :
 forall a a',
   N.odd a = false -> N.odd a' = true -> Nless a a' = true.
Proof.
  intros. destruct (N.discr (N.lxor a a')) as [(p,H2)|H1]. unfold Nless.
  rewrite H2. destruct p. simpl. rewrite H, H0. reflexivity.
  assert (H1: N.odd (N.lxor a a') = false) by (rewrite H2; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H1. discriminate H1.
  simpl. rewrite H, H0. reflexivity.
  assert (H2: N.odd (N.lxor a a') = false) by (rewrite H1; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H2. discriminate H2.
Qed.

Lemma Nbit0_gt :
 forall a a',
   N.odd a = true -> N.odd a' = false -> Nless a a' = false.
Proof.
  intros. destruct (N.discr (N.lxor a a')) as [(p,H2)|H1]. unfold Nless.
  rewrite H2. destruct p. simpl. rewrite H, H0. reflexivity.
  assert (H1: N.odd (N.lxor a a') = false) by (rewrite H2; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H1. discriminate H1.
  simpl. rewrite H, H0. reflexivity.
  assert (H2: N.odd (N.lxor a a') = false) by (rewrite H1; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H2. discriminate H2.
Qed.

Lemma Nless_not_refl : forall a, Nless a a = false.
Proof.
  intro. unfold Nless. rewrite (N.lxor_nilpotent a). reflexivity.
Qed.

Lemma Nless_def_1 :
 forall a a', Nless (N.double a) (N.double a') = Nless a a'.
Proof.
  destruct a; destruct a'. reflexivity.
  trivial.
  unfold Nless. simpl. destruct p; trivial.
  unfold Nless. simpl. destruct (Pos.lxor p p0). reflexivity.
  trivial.
Qed.

Lemma Nless_def_2 :
 forall a a',
   Nless (N.succ_double a) (N.succ_double a') = Nless a a'.
Proof.
  destruct a; destruct a'. reflexivity.
  trivial.
  unfold Nless. simpl. destruct p; trivial.
  unfold Nless. simpl. destruct (Pos.lxor p p0). reflexivity.
  trivial.
Qed.

Lemma Nless_def_3 :
 forall a a', Nless (N.double a) (N.succ_double a') = true.
Proof.
  intros. apply Nbit0_less. apply Ndouble_bit0.
  apply Ndouble_plus_one_bit0.
Qed.

Lemma Nless_def_4 :
 forall a a', Nless (N.succ_double a) (N.double a') = false.
Proof.
  intros. apply Nbit0_gt. apply Ndouble_plus_one_bit0.
  apply Ndouble_bit0.
Qed.

Lemma Nless_z : forall a, Nless a N0 = false.
Proof.
  induction a. reflexivity.
  unfold Nless. rewrite (N.lxor_0_r (Npos p)). induction p; trivial.
Qed.

Lemma N0_less_1 :
 forall a, Nless N0 a = true -> {p : positive | a = Npos p}.
Proof.
  destruct a. discriminate.
  intros. exists p. reflexivity.
Qed.

Lemma N0_less_2 : forall a, Nless N0 a = false -> a = N0.
Proof.
  induction a as [|p]; intro H. trivial.
  exfalso. induction p as [|p IHp|]; discriminate || simpl; auto using IHp.
Qed.

Lemma Nless_trans :
 forall a a' a'',
   Nless a a' = true -> Nless a' a'' = true -> Nless a a'' = true.
Proof.
  induction a as [|a IHa|a IHa] using N.binary_ind; intros a' a'' H H0.
  - case_eq (Nless N0 a'') ; intros Heqn.
    + trivial.
    + rewrite (N0_less_2 a'' Heqn), (Nless_z a') in H0. discriminate H0.
  - induction a' as [|a' _|a' _] using N.binary_ind.
    + rewrite (Nless_z (N.double a)) in H. discriminate H.
    + rewrite (Nless_def_1 a a') in H.
      induction a'' using N.binary_ind.
      * rewrite (Nless_z (N.double a')) in H0. discriminate H0.
      * rewrite (Nless_def_1 a' a'') in H0. rewrite (Nless_def_1 a a'').
        exact (IHa _ _ H H0).
      * apply Nless_def_3.
    + induction a'' as [|a'' _|a'' _] using N.binary_ind.
      * rewrite (Nless_z (N.succ_double a')) in H0. discriminate H0.
      * rewrite (Nless_def_4 a' a'') in H0. discriminate H0.
      * apply Nless_def_3.
  - induction a' as [|a' _|a' _] using N.binary_ind.
    + rewrite (Nless_z (N.succ_double a)) in H. discriminate H.
    + rewrite (Nless_def_4 a a') in H. discriminate H.
    + induction a'' using N.binary_ind.
      * rewrite (Nless_z (N.succ_double a')) in H0. discriminate H0.
      * rewrite (Nless_def_4 a' a'') in H0. discriminate H0.
      * rewrite (Nless_def_2 a' a'') in H0. rewrite (Nless_def_2 a a') in H.
        rewrite (Nless_def_2 a a''). exact (IHa _ _ H H0).
Qed.

Lemma Nless_total :
 forall a a', {Nless a a' = true} + {Nless a' a = true} + {a = a'}.
Proof.
  induction a using N.binary_rec; intro a'.
  - case_eq (Nless N0 a') ; intros Heqb.
    + left. left. auto.
    + right. rewrite (N0_less_2 a' Heqb). reflexivity.
  - induction a' as [|a' _|a' _] using N.binary_rec.
    + case_eq (Nless N0 (N.double a)) ; intros Heqb.
      * left. right. auto.
      * right. exact (N0_less_2 _  Heqb).
    + rewrite 2!Nless_def_1. destruct (IHa a') as [ | ->].
      * left. assumption.
      * right. reflexivity.
    + left. left. apply Nless_def_3.
  - induction a' as [|a' _|a' _] using N.binary_rec.
    + left. right. destruct a; reflexivity.
    + left. right. apply Nless_def_3.
    + rewrite 2!Nless_def_2. destruct (IHa a') as [ | ->].
      * left. assumption.
      * right. reflexivity.
Qed.

(** Number of digits in a number *)

Notation Nsize := N.size_nat (only parsing).

(** conversions between N and bit vectors. *)

Fixpoint P2Bv (p:positive) : Bvector (Pos.size_nat p) :=
 match p return Bvector (Pos.size_nat p) with
   | xH => Bvect_true 1%nat
   | xO p => Bcons false (Pos.size_nat p) (P2Bv p)
   | xI p => Bcons true (Pos.size_nat p) (P2Bv p)
 end.

Definition N2Bv (n:N) : Bvector (N.size_nat n) :=
  match n as n0 return Bvector (N.size_nat n0) with
    | N0 => Bnil
    | Npos p => P2Bv p
  end.

Fixpoint P2Bv_sized (m : nat) (p : positive) : Bvector m :=
  match m with
  | O => []
  | S m =>
    match p with
    | xI p => true  :: P2Bv_sized  m p
    | xO p => false :: P2Bv_sized  m p
    | xH   => true  :: Bvect_false m
    end
  end.

Definition N2Bv_sized (m : nat) (n : N) : Bvector m :=
  match n with
  | N0     => Bvect_false m
  | Npos p => P2Bv_sized  m p
  end.

Fixpoint Bv2N (n:nat)(bv:Bvector n) : N :=
  match bv with
    | Vector.nil _ => N0
    | Vector.cons _ false n bv => N.double (Bv2N n bv)
    | Vector.cons _ true n bv => N.succ_double (Bv2N n bv)
  end.

Lemma Bv2N_N2Bv : forall n, Bv2N _ (N2Bv n) = n.
Proof.
destruct n.
simpl; auto.
induction p; simpl in *; auto; rewrite IHp; simpl; auto.
Qed.

(** The opposite composition is not so simple: if the considered
  bit vector has some zeros on its right, they will disappear during
  the return [Bv2N] translation: *)

Lemma Bv2N_Nsize : forall n (bv:Bvector n), N.size_nat (Bv2N n bv) <= n.
Proof.
induction bv; intros.
auto.
simpl.
destruct h;
 destruct (Bv2N n bv);
 simpl ; auto with arith.
Qed.

(** In the previous lemma, we can only replace the inequality by
  an equality whenever the highest bit is non-null. *)

Lemma Bv2N_Nsize_1 : forall n (bv:Bvector (S n)),
  Bsign _ bv = true <->
  N.size_nat (Bv2N _ bv) = (S n).
Proof.
apply Vector.rectS ; intros ; simpl.
destruct a ; compute ; split ; intros x ; now inversion x.
 destruct a, (Bv2N (S n) v) ;
  simpl ;intuition ; try discriminate.
Qed.

(** To state nonetheless a second result about composition of
 conversions, we define a conversion on a given number of bits : *)

#[deprecated(since = "8.9.0", note = "Use N2Bv_sized instead.")]
Fixpoint N2Bv_gen (n:nat)(a:N) : Bvector n :=
 match n return Bvector n with
   | 0 => Bnil
   | S n => match a with
       | N0 => Bvect_false (S n)
       | Npos xH => Bcons true _ (Bvect_false n)
       | Npos (xO p) => Bcons false _ (N2Bv_gen n (Npos p))
       | Npos (xI p) => Bcons true _ (N2Bv_gen n (Npos p))
      end
  end.

(** The first [N2Bv] is then a special case of [N2Bv_gen] *)

Lemma N2Bv_N2Bv_gen : forall (a:N), N2Bv a = N2Bv_gen (N.size_nat a) a.
Proof.
destruct a; simpl.
auto.
induction p; simpl; intros; auto; congruence.
Qed.

(** In fact, if [k] is large enough, [N2Bv_gen k a] contains all digits of
   [a] plus some zeros. *)

Lemma N2Bv_N2Bv_gen_above : forall (a:N)(k:nat),
 N2Bv_gen (N.size_nat a + k) a = Vector.append (N2Bv a) (Bvect_false k).
Proof.
destruct a; simpl.
destruct k; simpl; auto.
induction p; simpl; intros;unfold Bcons; f_equal; auto.
Qed.

(** Here comes now the second composition result. *)

Lemma N2Bv_Bv2N : forall n (bv:Bvector n),
   N2Bv_gen n (Bv2N n bv) = bv.
Proof.
induction bv; intros.
auto.
simpl.
generalize IHbv; clear IHbv.
unfold Bcons.
destruct (Bv2N _ bv);
 destruct h; intro H; rewrite <- H; simpl; trivial;
  induction n; simpl; auto.
Qed.

(** accessing some precise bits. *)

Lemma Nbit0_Blow : forall n, forall (bv:Bvector (S n)),
  N.odd (Bv2N _ bv) = Blow _ bv.
Proof.
apply Vector.caseS.
intros.
unfold Blow.
simpl.
destruct (Bv2N n t); simpl;
 destruct h; auto.
Qed.

Notation Bnth := (@Vector.nth_order bool).

Lemma Bnth_Nbit : forall n (bv:Bvector n) p (H:p<n),
  Bnth bv H = N.testbit_nat (Bv2N _ bv) p.
Proof.
induction bv; intros.
inversion H.
destruct p ; simpl.
  destruct (Bv2N n bv); destruct h; simpl in *; auto.
  specialize IHbv with p (Lt.lt_S_n _ _ H).
    simpl in * ; destruct (Bv2N n bv); destruct h; simpl in *; auto.
Qed.

Lemma Nbit_Nsize : forall n p, N.size_nat n <= p -> N.testbit_nat n p = false.
Proof.
destruct n as [|n].
simpl; auto.
induction n; simpl in *; intros; destruct p; auto with arith.
inversion H.
inversion H.
Qed.

Lemma Nbit_Bth: forall n p (H:p < N.size_nat n),
  N.testbit_nat n p = Bnth (N2Bv n) H.
Proof.
destruct n as [|n].
inversion H.
induction n ; destruct p ; unfold Vector.nth_order in *; simpl in * ; auto.
intros H ; destruct (Lt.lt_n_O _ (Lt.lt_S_n _ _ H)).
Qed.

(** Binary bitwise operations are the same in the two worlds. *)

Lemma Nxor_BVxor : forall n (bv bv' : Bvector n),
  Bv2N _ (BVxor _ bv bv') = N.lxor (Bv2N _ bv) (Bv2N _ bv').
Proof.
apply Vector.rect2 ; intros.
now simpl.
simpl.
destruct a, b, (Bv2N n v1), (Bv2N n v2); simpl in *; rewrite H ; now simpl.
Qed.

Lemma Nand_BVand : forall n (bv bv' : Bvector n),
  Bv2N _ (BVand _ bv bv') = N.land (Bv2N _ bv) (Bv2N _ bv').
Proof.
refine (@Vector.rect2 _ _ _ _ _); simpl; intros; auto.
rewrite H.
destruct a, b, (Bv2N n v1), (Bv2N n v2);
 simpl; auto.
Qed.

Lemma N2Bv_sized_Nsize (n : N) :
  N2Bv_sized (N.size_nat n) n = N2Bv n.
Proof with simpl; auto.
  destruct n...
  induction p...
  all: rewrite IHp...
Qed.

Lemma N2Bv_sized_Bv2N (n : nat) (v : Bvector n) :
  N2Bv_sized n (Bv2N n v) = v.
Proof with simpl; auto.
  induction v...
  destruct h;
  unfold N2Bv_sized;
  destruct (Bv2N n v) as [|[]];
  rewrite <- IHv...
Qed.

Lemma N2Bv_N2Bv_sized_above (a : N) (k : nat) :
  N2Bv_sized (N.size_nat a + k) a = N2Bv a ++ Bvect_false k.
Proof with auto.
  destruct a...
  induction p; simpl; f_equal...
Qed.
