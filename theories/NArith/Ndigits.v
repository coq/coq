(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool Morphisms Setoid Bvector BinPos BinNat Wf_nat
 Pnat Nnat Ndiv_def Compare_dec Lt Minus.

Local Open Scope positive_scope.

(** Operation over bits of a [N] number. *)

(** Logical [or] *)

Fixpoint Por (p q : positive) : positive :=
  match p, q with
    | 1, q~0 => q~1
    | 1, _ => q
    | p~0, 1 => p~1
    | _, 1 => p
    | p~0, q~0 => (Por p q)~0
    | p~0, q~1 => (Por p q)~1
    | p~1, q~0 => (Por p q)~1
    | p~1, q~1 => (Por p q)~1
  end.

Definition Nor n m :=
 match n, m with
   | N0, _ => m
   | _, N0 => n
   | Npos p, Npos q => Npos (Por p q)
 end.

(** Logical [and] *)

Fixpoint Pand (p q : positive) : N :=
  match p, q with
    | 1, q~0 => N0
    | 1, _ => Npos 1
    | p~0, 1 => N0
    | _, 1 => Npos 1
    | p~0, q~0 => Ndouble (Pand p q)
    | p~0, q~1 => Ndouble (Pand p q)
    | p~1, q~0 => Ndouble (Pand p q)
    | p~1, q~1 => Ndouble_plus_one (Pand p q)
  end.

Definition Nand n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Pand p q
 end.

(** Logical [diff] *)

Fixpoint Pdiff (p q:positive) : N :=
  match p, q with
    | 1, q~0 => Npos 1
    | 1, _ => N0
    | _~0, 1 => Npos p
    | p~1, 1 => Npos (p~0)
    | p~0, q~0 => Ndouble (Pdiff p q)
    | p~0, q~1 => Ndouble (Pdiff p q)
    | p~1, q~1 => Ndouble (Pdiff p q)
    | p~1, q~0 => Ndouble_plus_one (Pdiff p q)
  end.

Fixpoint Ndiff n m :=
 match n, m with
  | N0, _ => N0
  | _, N0 => n
  | Npos p, Npos q => Pdiff p q
 end.

(** [xor] *)

Fixpoint Pxor (p q:positive) : N :=
  match p, q with
    | 1, 1 => N0
    | 1, q~0 => Npos (q~1)
    | 1, q~1 => Npos (q~0)
    | p~0, 1 => Npos (p~1)
    | p~0, q~0 => Ndouble (Pxor p q)
    | p~0, q~1 => Ndouble_plus_one (Pxor p q)
    | p~1, 1 => Npos (p~0)
    | p~1, q~0 => Ndouble_plus_one (Pxor p q)
    | p~1, q~1 => Ndouble (Pxor p q)
  end.

Definition Nxor (n m:N) :=
  match n, m with
    | N0, _ => m
    | _, N0 => n
    | Npos p, Npos q => Pxor p q
  end.

(** For proving properties of these operations, we will use
  an equivalence with functional streams of bit, cf [eqf] below *)

(** Shift *)

Definition Nshiftl_nat (a:N)(n:nat) := iter_nat n _ Ndouble a.

Definition Nshiftr_nat (a:N)(n:nat) := iter_nat n _ Ndiv2 a.

Definition Nshiftr a n :=
  match n with
    | N0 => a
    | Npos p => iter_pos p _ Ndiv2 a
  end.

Definition Nshiftl a n :=
  match a, n with
    | _, N0 => a
    | N0, _ => a
    | Npos p, Npos q => Npos (iter_pos q _ xO p)
  end.

(** Checking whether a particular bit is set on not *)

Fixpoint Pbit (p:positive) : nat -> bool :=
  match p with
    | 1 => fun n => match n with
                      | O => true
                      | S _ => false
                    end
    | p~0 => fun n => match n with
                        | O => false
                        | S n' => Pbit p n'
                      end
    | p~1 => fun n => match n with
                        | O => true
                        | S n' => Pbit p n'
                      end
  end.

Definition Nbit (a:N) :=
  match a with
    | N0 => fun _ => false
    | Npos p => Pbit p
  end.

(** Same, but with index in N *)

Fixpoint Ptestbit p n :=
  match p, n with
    | p~0, N0 => false
    | _, N0 => true
    | 1, _ => false
    | p~0, _ => Ptestbit p (Npred n)
    | p~1, _ => Ptestbit p (Npred n)
  end.

Definition Ntestbit a n :=
  match a with
    | N0 => false
    | Npos p => Ptestbit p n
  end.

Local Close Scope positive_scope.
Local Open Scope N_scope.

(** Equivalence of Pbit and Ptestbit *)

Lemma Ptestbit_Pbit :
 forall p n, Ptestbit p (N_of_nat n) = Pbit p n.
Proof.
 induction p as [p IH|p IH| ]; intros n; simpl.
 rewrite <- N_of_pred, IH; destruct n; trivial.
 rewrite <- N_of_pred, IH; destruct n; trivial.
 destruct n; trivial.
Qed.

Lemma Ntestbit_Nbit : forall a n, Ntestbit a (N_of_nat n) = Nbit a n.
Proof.
 destruct a. trivial. apply Ptestbit_Pbit.
Qed.

Lemma Pbit_Ptestbit :
 forall p n, Pbit p (nat_of_N n) = Ptestbit p n.
Proof.
 intros; now rewrite <- Ptestbit_Pbit, N_of_nat_of_N.
Qed.

Lemma Nbit_Ntestbit :
 forall a n, Nbit a (nat_of_N n) = Ntestbit a n.
Proof.
 destruct a. trivial. apply Pbit_Ptestbit.
Qed.

(** Correctness proofs for [Ntestbit]. *)

Lemma Ntestbit_odd_0 a : Ntestbit (2*a+1) 0 = true.
Proof.
 now destruct a.
Qed.

Lemma Ntestbit_even_0 a : Ntestbit (2*a) 0 = false.
Proof.
 now destruct a.
Qed.

Lemma Ntestbit_odd_succ a n :
 Ntestbit (2*a+1) (Nsucc n) = Ntestbit a n.
Proof.
 destruct a. simpl. now destruct n.
 simpl. rewrite Npred_succ. now destruct n.
Qed.

Lemma Ntestbit_even_succ a n :
 Ntestbit (2*a) (Nsucc n) = Ntestbit a n.
Proof.
 destruct a. trivial.
 simpl. rewrite Npred_succ. now destruct n.
Qed.

(** Equivalence of shifts, N and nat versions *)

Lemma Nshiftr_nat_S : forall a n,
 Nshiftr_nat a (S n) = Ndiv2 (Nshiftr_nat a n).
Proof.
 reflexivity.
Qed.

Lemma Nshiftl_nat_S : forall a n,
 Nshiftl_nat a (S n) = Ndouble (Nshiftl_nat a n).
Proof.
 reflexivity.
Qed.

Lemma Nshiftr_nat_equiv :
 forall a n, Nshiftr_nat a (nat_of_N n) = Nshiftr a n.
Proof.
 intros a [|n]; simpl. unfold Nshiftr_nat.
 trivial.
 symmetry. apply iter_nat_of_P.
Qed.

Lemma Nshiftr_equiv_nat :
 forall a n, Nshiftr a (N_of_nat n) = Nshiftr_nat a n.
Proof.
 intros. now rewrite <- Nshiftr_nat_equiv, nat_of_N_of_nat.
Qed.

Lemma Nshiftl_nat_equiv :
 forall a n, Nshiftl_nat a (nat_of_N n) = Nshiftl a n.
Proof.
 intros [|a] [|n]; simpl; unfold Nshiftl_nat; trivial.
 apply iter_nat_invariant; intros; now subst.
 rewrite <- iter_nat_of_P. symmetry. now apply iter_pos_swap_gen.
Qed.

Lemma Nshiftl_equiv_nat :
 forall a n, Nshiftl a (N_of_nat n) = Nshiftl_nat a n.
Proof.
 intros. now rewrite <- Nshiftl_nat_equiv, nat_of_N_of_nat.
Qed.

(** Correctness proofs for shifts *)

Lemma Nshiftr_nat_spec : forall a n m,
  Nbit (Nshiftr_nat a n) m = Nbit a (m+n).
Proof.
 induction n; intros m.
 now rewrite <- plus_n_O.
 simpl. rewrite <- plus_n_Sm, <- plus_Sn_m, <- IHn, Nshiftr_nat_S.
 destruct (Nshiftr_nat a n) as [|[p|p|]]; simpl; trivial.
Qed.

Lemma Nshiftr_spec : forall a n m,
 Ntestbit (Nshiftr a n) m = Ntestbit a (m+n).
Proof.
 intros.
 rewrite <- Nshiftr_nat_equiv, <- !Nbit_Ntestbit, nat_of_Nplus.
 apply Nshiftr_nat_spec.
Qed.

Lemma Nshiftl_nat_spec_high : forall a n m, (n<=m)%nat ->
  Nbit (Nshiftl_nat a n) m = Nbit a (m-n).
Proof.
 induction n; intros m H.
 now rewrite <- minus_n_O.
 destruct m. inversion H. apply le_S_n in H.
 simpl. rewrite <- IHn, Nshiftl_nat_S; trivial.
 destruct (Nshiftl_nat a n) as [|[p|p|]]; simpl; trivial.
Qed.

Lemma Nshiftl_spec_high : forall a n m, n<=m ->
 Ntestbit (Nshiftl a n) m = Ntestbit a (m-n).
Proof.
 intros.
 rewrite <- Nshiftl_nat_equiv, <- !Nbit_Ntestbit, nat_of_Nminus.
 apply Nshiftl_nat_spec_high.
 apply nat_compare_le. now rewrite <- nat_of_Ncompare.
Qed.

Lemma Nshiftl_nat_spec_low : forall a n m, (m<n)%nat ->
 Nbit (Nshiftl_nat a n) m = false.
Proof.
 induction n; intros m H. inversion H.
 rewrite Nshiftl_nat_S.
 destruct m.
 destruct (Nshiftl_nat a n); trivial.
 specialize (IHn m (lt_S_n _ _ H)).
 destruct (Nshiftl_nat a n); trivial.
Qed.

Lemma Nshiftl_spec_low : forall a n m, m<n ->
 Ntestbit (Nshiftl a n) m = false.
Proof.
 intros.
 rewrite <- Nshiftl_nat_equiv, <- Nbit_Ntestbit.
 apply Nshiftl_nat_spec_low.
 apply nat_compare_lt. now rewrite <- nat_of_Ncompare.
Qed.

(** A left shift for positive numbers (used in BigN) *)

Definition Pshiftl_nat (p:positive)(n:nat) := iter_nat n _ xO p.

Lemma Pshiftl_nat_0 : forall p, Pshiftl_nat p 0 = p.
Proof. reflexivity. Qed.

Lemma Pshiftl_nat_S :
 forall p n, Pshiftl_nat p (S n) = xO (Pshiftl_nat p n).
Proof. reflexivity. Qed.

Lemma Pshiftl_nat_N :
 forall p n, Npos (Pshiftl_nat p n) = Nshiftl_nat (Npos p) n.
Proof.
 unfold Pshiftl_nat, Nshiftl_nat.
 induction n; simpl; auto. now rewrite <- IHn.
Qed.

Lemma Pshiftl_nat_plus : forall n m p,
  Pshiftl_nat p (m + n) = Pshiftl_nat (Pshiftl_nat p n) m.
Proof.
 induction m; simpl; intros. reflexivity.
 rewrite 2 Pshiftl_nat_S. now f_equal.
Qed.

(** Semantics of bitwise operations *)

Lemma Pxor_semantics : forall p p' n,
 Nbit (Pxor p p') n = xorb (Pbit p n) (Pbit p' n).
Proof.
 induction p as [p IHp|p IHp|]; intros [p'|p'|] [|n]; trivial; simpl;
  (specialize (IHp p'); destruct Pxor; trivial; apply (IHp n)) ||
  now destruct Pbit.
Qed.

Lemma Nxor_semantics : forall a a' n,
 Nbit (Nxor a a') n = xorb (Nbit a n) (Nbit a' n).
Proof.
 intros [|p] [|p'] n; simpl; trivial.
 now destruct Pbit.
 now destruct Pbit.
 apply Pxor_semantics.
Qed.

Lemma Nxor_spec : forall a a' n,
 Ntestbit (Nxor a a') n = xorb (Ntestbit a n) (Ntestbit a' n).
Proof.
 intros. rewrite <- !Nbit_Ntestbit. apply Nxor_semantics.
Qed.

Lemma Por_semantics : forall p p' n,
 Pbit (Por p p') n = (Pbit p n) || (Pbit p' n).
Proof.
 induction p as [p IHp|p IHp|]; intros [p'|p'|] [|n]; trivial;
  apply (IHp p' n) || now rewrite orb_false_r.
Qed.

Lemma Nor_semantics : forall a a' n,
 Nbit (Nor a a') n = (Nbit a n) || (Nbit a' n).
Proof.
 intros [|p] [|p'] n; simpl; trivial.
 now rewrite orb_false_r.
 apply Por_semantics.
Qed.

Lemma Nor_spec : forall a a' n,
 Ntestbit (Nor a a') n = (Ntestbit a n) || (Ntestbit a' n).
Proof.
 intros. rewrite <- !Nbit_Ntestbit. apply Nor_semantics.
Qed.

Lemma Pand_semantics : forall p p' n,
 Nbit (Pand p p') n = (Pbit p n) && (Pbit p' n).
Proof.
 induction p as [p IHp|p IHp|]; intros [p'|p'|] [|n]; trivial; simpl;
  (specialize (IHp p'); destruct Pand; trivial; apply (IHp n)) ||
  now rewrite andb_false_r.
Qed.

Lemma Nand_semantics : forall a a' n,
 Nbit (Nand a a') n = (Nbit a n) && (Nbit a' n).
Proof.
 intros [|p] [|p'] n; simpl; trivial.
 now rewrite andb_false_r.
 apply Pand_semantics.
Qed.

Lemma Nand_spec : forall a a' n,
 Ntestbit (Nand a a') n = (Ntestbit a n) && (Ntestbit a' n).
Proof.
 intros. rewrite <- !Nbit_Ntestbit. apply Nand_semantics.
Qed.

Lemma Pdiff_semantics : forall p p' n,
 Nbit (Pdiff p p') n = (Pbit p n) && negb (Pbit p' n).
Proof.
 induction p as [p IHp|p IHp|]; intros [p'|p'|] [|n]; trivial; simpl;
  (specialize (IHp p'); destruct Pdiff; trivial; apply (IHp n)) ||
  now rewrite andb_true_r.
Qed.

Lemma Ndiff_semantics : forall a a' n,
 Nbit (Ndiff a a') n = (Nbit a n) && negb (Nbit a' n).
Proof.
 intros [|p] [|p'] n; simpl; trivial.
 simpl. now rewrite andb_true_r.
 apply Pdiff_semantics.
Qed.

Lemma Ndiff_spec : forall a a' n,
 Ntestbit (Ndiff a a') n = (Ntestbit a n) && negb (Ntestbit a' n).
Proof.
 intros. rewrite <- !Nbit_Ntestbit. apply Ndiff_semantics.
Qed.


(** Equality over functional streams of bits *)

Definition eqf (f g:nat -> bool) := forall n:nat, f n = g n.

Program Instance eqf_equiv : Equivalence eqf.

Local Infix "==" := eqf (at level 70, no associativity).

(** If two numbers produce the same stream of bits, they are equal. *)

Local Notation Step H := (fun n => H (S n)).

Lemma Pbit_faithful_0 : forall p, ~(Pbit p == (fun _ => false)).
Proof.
 induction p as [p IHp|p IHp| ]; intros H; try discriminate (H O).
  apply (IHp (Step H)).
Qed.

Lemma Pbit_faithful : forall p p', Pbit p == Pbit p' -> p = p'.
Proof.
 induction p as [p IHp|p IHp| ]; intros [p'|p'|] H; trivial;
  try discriminate (H O).
 f_equal. apply (IHp _ (Step H)).
 destruct (Pbit_faithful_0 _ (Step H)).
 f_equal. apply (IHp _ (Step H)).
 symmetry in H. destruct (Pbit_faithful_0 _ (Step H)).
Qed.

Lemma Nbit_faithful : forall n n', Nbit n == Nbit n' -> n = n'.
Proof.
 intros [|p] [|p'] H; trivial.
 symmetry in H. destruct (Pbit_faithful_0 _ H).
 destruct (Pbit_faithful_0 _ H).
 f_equal. apply Pbit_faithful, H.
Qed.

Lemma Nbit_faithful_iff : forall n n', Nbit n == Nbit n' <-> n = n'.
Proof.
 split. apply Nbit_faithful. intros; now subst.
Qed.

Hint Rewrite Nxor_semantics Nor_semantics
 Nand_semantics Ndiff_semantics : bitwise_semantics.

Ltac bitwise_semantics :=
 apply Nbit_faithful; intro n; autorewrite with bitwise_semantics.

(** Now, we can easily deduce properties of [Nxor] and others
    from properties of [xorb] and others. *)

Lemma Nxor_eq : forall a a', Nxor a a' = 0 -> a = a'.
Proof.
 intros a a' H. bitwise_semantics. apply xorb_eq.
 now rewrite <- Nxor_semantics, H.
Qed.

Lemma Nxor_nilpotent : forall a, Nxor a a = 0.
Proof.
 intros. bitwise_semantics. apply xorb_nilpotent.
Qed.

Lemma Nxor_0_l : forall n, Nxor 0 n = n.
Proof.
 trivial.
Qed.
Notation Nxor_neutral_left := Nxor_0_l (only parsing).

Lemma Nxor_0_r : forall n, Nxor n 0 = n.
Proof.
 destruct n; trivial.
Qed.
Notation Nxor_neutral_right := Nxor_0_r (only parsing).

Lemma Nxor_comm : forall a a', Nxor a a' = Nxor a' a.
Proof.
 intros. bitwise_semantics. apply xorb_comm.
Qed.

Lemma Nxor_assoc :
 forall a a' a'', Nxor (Nxor a a') a'' = Nxor a (Nxor a' a'').
Proof.
 intros. bitwise_semantics. apply xorb_assoc.
Qed.

Lemma Nor_0_l : forall n, Nor 0 n = n.
Proof.
 trivial.
Qed.

Lemma Nor_0_r : forall n, Nor n 0 = n.
Proof.
 destruct n; trivial.
Qed.

Lemma Nor_comm : forall a a', Nor a a' = Nor a' a.
Proof.
 intros. bitwise_semantics. apply orb_comm.
Qed.

Lemma Nor_assoc :
 forall a a' a'', Nor a (Nor a' a'') = Nor (Nor a a') a''.
Proof.
 intros. bitwise_semantics. apply orb_assoc.
Qed.

Lemma Nor_diag : forall a, Nor a a = a.
Proof.
 intros. bitwise_semantics. apply orb_diag.
Qed.

Lemma Nand_0_l : forall n, Nand 0 n = 0.
Proof.
 trivial.
Qed.

Lemma Nand_0_r : forall n, Nand n 0 = 0.
Proof.
 destruct n; trivial.
Qed.

Lemma Nand_comm : forall a a', Nand a a' = Nand a' a.
Proof.
 intros. bitwise_semantics. apply andb_comm.
Qed.

Lemma Nand_assoc :
 forall a a' a'', Nand a (Nand a' a'') = Nand (Nand a a') a''.
Proof.
 intros. bitwise_semantics. apply andb_assoc.
Qed.

Lemma Nand_diag : forall a, Nand a a = a.
Proof.
 intros. bitwise_semantics. apply andb_diag.
Qed.

Lemma Ndiff_0_l : forall n, Ndiff 0 n = 0.
Proof.
 trivial.
Qed.

Lemma Ndiff_0_r : forall n, Ndiff n 0 = n.
Proof.
 destruct n; trivial.
Qed.

Lemma Ndiff_diag : forall a, Ndiff a a = 0.
Proof.
 intros. bitwise_semantics. apply andb_negb_r.
Qed.

Lemma Nor_and_distr_l : forall a b c,
 Nor (Nand a b) c = Nand (Nor a c) (Nor b c).
Proof.
 intros. bitwise_semantics. apply orb_andb_distrib_l.
Qed.

Lemma Nor_and_distr_r : forall a b c,
 Nor a (Nand b c) = Nand (Nor a b) (Nor a c).
Proof.
 intros. bitwise_semantics. apply orb_andb_distrib_r.
Qed.

Lemma Nand_or_distr_l : forall a b c,
 Nand (Nor a b) c = Nor (Nand a c) (Nand b c).
Proof.
 intros. bitwise_semantics. apply andb_orb_distrib_l.
Qed.

Lemma Nand_or_distr_r : forall a b c,
 Nand a (Nor b c) = Nor (Nand a b) (Nand a c).
Proof.
 intros. bitwise_semantics. apply andb_orb_distrib_r.
Qed.

Lemma Ndiff_diff_l : forall a b c,
 Ndiff (Ndiff a b) c = Ndiff a (Nor b c).
Proof.
 intros. bitwise_semantics. now rewrite negb_orb, andb_assoc.
Qed.

Lemma Nor_diff_and : forall a b,
 Nor (Ndiff a b) (Nand a b) = a.
Proof.
 intros. bitwise_semantics.
 now rewrite <- andb_orb_distrib_r, orb_comm, orb_negb_r, andb_true_r.
Qed.

Lemma Nand_diff : forall a b,
 Nand (Ndiff a b) b = 0.
Proof.
 intros. bitwise_semantics.
 now rewrite <-andb_assoc, (andb_comm (negb _)), andb_negb_r, andb_false_r.
Qed.

Local Close Scope N_scope.

(** Checking whether a number is odd, i.e.
   if its lower bit is set. *)

Definition Nbit0 (n:N) :=
  match n with
  | N0 => false
  | Npos (_~0) => false
  | _ => true
  end.

Definition Nodd (n:N) := Nbit0 n = true.
Definition Neven (n:N) := Nbit0 n = false.

Lemma Nbit0_correct : forall n:N, Nbit n 0 = Nbit0 n.
Proof.
  destruct n; trivial.
  destruct p; trivial.
Qed.

Lemma Ndouble_bit0 : forall n:N, Nbit0 (Ndouble n) = false.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_plus_one_bit0 :
 forall n:N, Nbit0 (Ndouble_plus_one n) = true.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndiv2_double :
 forall n:N, Neven n -> Ndouble (Ndiv2 n) = n.
Proof.
  destruct n. trivial. destruct p. intro H. discriminate H.
  intros. reflexivity.
  intro H. discriminate H.
Qed.

Lemma Ndiv2_double_plus_one :
 forall n:N, Nodd n -> Ndouble_plus_one (Ndiv2 n) = n.
Proof.
  destruct n. intro. discriminate H.
  destruct p. intros. reflexivity.
  intro H. discriminate H.
  intro. reflexivity.
Qed.

Lemma Ndiv2_correct :
 forall (a:N) (n:nat), Nbit (Ndiv2 a) n = Nbit a (S n).
Proof.
  destruct a; trivial.
  destruct p; trivial.
Qed.

Lemma Nxor_bit0 :
 forall a a':N, Nbit0 (Nxor a a') = xorb (Nbit0 a) (Nbit0 a').
Proof.
  intros. rewrite <- Nbit0_correct, (Nxor_semantics a a' O).
  rewrite Nbit0_correct, Nbit0_correct. reflexivity.
Qed.

Lemma Nxor_div2 :
 forall a a':N, Ndiv2 (Nxor a a') = Nxor (Ndiv2 a) (Ndiv2 a').
Proof.
  intros. apply Nbit_faithful. unfold eqf. intro.
  rewrite (Nxor_semantics (Ndiv2 a) (Ndiv2 a') n), Ndiv2_correct, (Nxor_semantics a a' (S n)).
  rewrite 2! Ndiv2_correct.
  reflexivity.
Qed.

Lemma Nneg_bit0 :
 forall a a':N,
   Nbit0 (Nxor a a') = true -> Nbit0 a = negb (Nbit0 a').
Proof.
  intros.
  rewrite <- true_xorb, <- H, Nxor_bit0, xorb_assoc, 
    xorb_nilpotent, xorb_false.
  reflexivity.
Qed.

Lemma Nneg_bit0_1 :
 forall a a':N, Nxor a a' = Npos 1 -> Nbit0 a = negb (Nbit0 a').
Proof.
  intros. apply Nneg_bit0. rewrite H. reflexivity.
Qed.

Lemma Nneg_bit0_2 :
 forall (a a':N) (p:positive),
   Nxor a a' = Npos (xI p) -> Nbit0 a = negb (Nbit0 a').
Proof.
  intros. apply Nneg_bit0. rewrite H. reflexivity.
Qed.

Lemma Nsame_bit0 :
 forall (a a':N) (p:positive),
   Nxor a a' = Npos (xO p) -> Nbit0 a = Nbit0 a'.
Proof.
  intros. rewrite <- (xorb_false (Nbit0 a)).
  assert (H0: Nbit0 (Npos (xO p)) = false) by reflexivity.
  rewrite <- H0, <- H, Nxor_bit0, <- xorb_assoc, xorb_nilpotent, false_xorb.
    reflexivity.
Qed.

(** a lexicographic order on bits, starting from the lowest bit *)

Fixpoint Nless_aux (a a':N) (p:positive) : bool :=
  match p with
  | xO p' => Nless_aux (Ndiv2 a) (Ndiv2 a') p'
  | _ => andb (negb (Nbit0 a)) (Nbit0 a')
  end.

Definition Nless (a a':N) :=
  match Nxor a a' with
  | N0 => false
  | Npos p => Nless_aux a a' p
  end.

Lemma Nbit0_less :
 forall a a',
   Nbit0 a = false -> Nbit0 a' = true -> Nless a a' = true.
Proof.
  intros. destruct (Ndiscr (Nxor a a')) as [(p,H2)|H1]. unfold Nless.
  rewrite H2. destruct p. simpl. rewrite H, H0. reflexivity.
  assert (H1: Nbit0 (Nxor a a') = false) by (rewrite H2; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H1. discriminate H1.
  simpl. rewrite H, H0. reflexivity.
  assert (H2: Nbit0 (Nxor a a') = false) by (rewrite H1; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H2. discriminate H2.
Qed.

Lemma Nbit0_gt :
 forall a a',
   Nbit0 a = true -> Nbit0 a' = false -> Nless a a' = false.
Proof.
  intros. destruct (Ndiscr (Nxor a a')) as [(p,H2)|H1]. unfold Nless.
  rewrite H2. destruct p. simpl. rewrite H, H0. reflexivity.
  assert (H1: Nbit0 (Nxor a a') = false) by (rewrite H2; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H1. discriminate H1.
  simpl. rewrite H, H0. reflexivity.
  assert (H2: Nbit0 (Nxor a a') = false) by (rewrite H1; reflexivity).
  rewrite (Nxor_bit0 a a'), H, H0 in H2. discriminate H2.
Qed.

Lemma Nless_not_refl : forall a, Nless a a = false.
Proof.
  intro. unfold Nless. rewrite (Nxor_nilpotent a). reflexivity.
Qed.

Lemma Nless_def_1 :
 forall a a', Nless (Ndouble a) (Ndouble a') = Nless a a'.
Proof.
  destruct a; destruct a'. reflexivity.
  trivial.
  unfold Nless. simpl. destruct p; trivial.
  unfold Nless. simpl. destruct (Pxor p p0). reflexivity.
  trivial.
Qed.

Lemma Nless_def_2 :
 forall a a',
   Nless (Ndouble_plus_one a) (Ndouble_plus_one a') = Nless a a'.
Proof.
  destruct a; destruct a'. reflexivity.
  trivial.
  unfold Nless. simpl. destruct p; trivial.
  unfold Nless. simpl. destruct (Pxor p p0). reflexivity.
  trivial.
Qed.

Lemma Nless_def_3 :
 forall a a', Nless (Ndouble a) (Ndouble_plus_one a') = true.
Proof.
  intros. apply Nbit0_less. apply Ndouble_bit0.
  apply Ndouble_plus_one_bit0.
Qed.

Lemma Nless_def_4 :
 forall a a', Nless (Ndouble_plus_one a) (Ndouble a') = false.
Proof.
  intros. apply Nbit0_gt. apply Ndouble_plus_one_bit0.
  apply Ndouble_bit0.
Qed.

Lemma Nless_z : forall a, Nless a N0 = false.
Proof.
  induction a. reflexivity.
  unfold Nless. rewrite (Nxor_neutral_right (Npos p)). induction p; trivial.
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
  induction a as [|a IHa|a IHa] using N_ind_double; intros a' a'' H H0.
    case_eq (Nless N0 a'') ; intros Heqn. trivial.
     rewrite (N0_less_2 a'' Heqn), (Nless_z a') in H0. discriminate H0.
    induction a' as [|a' _|a' _] using N_ind_double.
      rewrite (Nless_z (Ndouble a)) in H. discriminate H.
      rewrite (Nless_def_1 a a') in H.
       induction a'' using N_ind_double.
         rewrite (Nless_z (Ndouble a')) in H0. discriminate H0.
         rewrite (Nless_def_1 a' a'') in H0. rewrite (Nless_def_1 a a'').
          exact (IHa _ _ H H0).
         apply Nless_def_3.
      induction a'' as [|a'' _|a'' _] using N_ind_double.
        rewrite (Nless_z (Ndouble_plus_one a')) in H0. discriminate H0.
        rewrite (Nless_def_4 a' a'') in H0. discriminate H0.
        apply Nless_def_3.
    induction a' as [|a' _|a' _] using N_ind_double.
      rewrite (Nless_z (Ndouble_plus_one a)) in H. discriminate H.
      rewrite (Nless_def_4 a a') in H. discriminate H.
      induction a'' using N_ind_double.
        rewrite (Nless_z (Ndouble_plus_one a')) in H0. discriminate H0.
        rewrite (Nless_def_4 a' a'') in H0. discriminate H0.
        rewrite (Nless_def_2 a' a'') in H0. rewrite (Nless_def_2 a a') in H.
          rewrite (Nless_def_2 a a''). exact (IHa _ _ H H0).
Qed.

Lemma Nless_total :
 forall a a', {Nless a a' = true} + {Nless a' a = true} + {a = a'}.
Proof.
  induction a using N_rec_double; intro a'.
    case_eq (Nless N0 a') ; intros Heqb. left. left. auto.
     right. rewrite (N0_less_2 a' Heqb). reflexivity.
    induction a' as [|a' _|a' _] using N_rec_double.
      case_eq (Nless N0 (Ndouble a)) ; intros Heqb. left. right. auto.
       right. exact (N0_less_2 _  Heqb).
      rewrite 2!Nless_def_1. destruct (IHa a') as [ | ->].
        left. assumption.
        right. reflexivity.
    left. left. apply Nless_def_3.
    induction a' as [|a' _|a' _] using N_rec_double.
      left. right. destruct a; reflexivity.
      left. right. apply Nless_def_3.
      rewrite 2!Nless_def_2. destruct (IHa a') as [ | ->].
        left. assumption.
        right. reflexivity.
Qed.

(** Number of digits in a number *)

Definition Nsize (n:N) : nat := match n with
  | N0 => O
  | Npos p => Psize p
 end.


(** conversions between N and bit vectors. *)

Fixpoint P2Bv (p:positive) : Bvector (Psize p) :=
 match p return Bvector (Psize p) with
   | xH => Bvect_true 1%nat
   | xO p => Bcons false (Psize p) (P2Bv p)
   | xI p => Bcons true (Psize p) (P2Bv p)
 end.

Definition N2Bv (n:N) : Bvector (Nsize n) :=
  match n as n0 return Bvector (Nsize n0) with
    | N0 => Bnil
    | Npos p => P2Bv p
  end.

Fixpoint Bv2N (n:nat)(bv:Bvector n) : N :=
  match bv with
    | Vector.nil => N0
    | Vector.cons false n bv => Ndouble (Bv2N n bv)
    | Vector.cons true n bv => Ndouble_plus_one (Bv2N n bv)
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

Lemma Bv2N_Nsize : forall n (bv:Bvector n), Nsize (Bv2N n bv) <= n.
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
  Nsize (Bv2N _ bv) = (S n).
Proof.
apply Vector.rectS ; intros ; simpl.
destruct a ; compute ; split ; intros x ; now inversion x.
 destruct a, (Bv2N (S n) v) ;
  simpl ;intuition ; try discriminate.
Qed.

(** To state nonetheless a second result about composition of
 conversions, we define a conversion on a given number of bits : *)

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

Lemma N2Bv_N2Bv_gen : forall (a:N), N2Bv a = N2Bv_gen (Nsize a) a.
Proof.
destruct a; simpl.
auto.
induction p; simpl; intros; auto; congruence.
Qed.

(** In fact, if [k] is large enough, [N2Bv_gen k a] contains all digits of
   [a] plus some zeros. *)

Lemma N2Bv_N2Bv_gen_above : forall (a:N)(k:nat),
 N2Bv_gen (Nsize a + k) a = Vector.append (N2Bv a) (Bvect_false k).
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
  Nbit0 (Bv2N _ bv) = Blow _ bv.
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
  Bnth bv H = Nbit (Bv2N _ bv) p.
Proof.
induction bv; intros.
inversion H.
destruct p ; simpl.
  destruct (Bv2N n bv); destruct h; simpl in *; auto.
  specialize IHbv with p (lt_S_n _ _ H).
    simpl in * ; destruct (Bv2N n bv); destruct h; simpl in *; auto.
Qed.

Lemma Nbit_Nsize : forall n p, Nsize n <= p -> Nbit n p = false.
Proof.
destruct n as [|n].
simpl; auto.
induction n; simpl in *; intros; destruct p; auto with arith.
inversion H.
inversion H.
Qed.

Lemma Nbit_Bth: forall n p (H:p < Nsize n), Nbit n p = Bnth (N2Bv n) H.
Proof.
destruct n as [|n].
inversion H.
induction n ; destruct p ; unfold Vector.nth_order in *; simpl in * ; auto.
intros H ; destruct (lt_n_O _ (lt_S_n _ _ H)).
Qed.

(** Binary bitwise operations are the same in the two worlds. *)

Lemma Nxor_BVxor : forall n (bv bv' : Bvector n),
  Bv2N _ (BVxor _ bv bv') = Nxor (Bv2N _ bv) (Bv2N _ bv').
Proof.
apply Vector.rect2 ; intros.
now simpl.
simpl.
destruct a, b, (Bv2N n v1), (Bv2N n v2); simpl in *; rewrite H ; now simpl.
Qed.

Lemma Nand_BVand : forall n (bv bv' : Bvector n),
  Bv2N _ (BVand _ bv bv') = Nand (Bv2N _ bv) (Bv2N _ bv').
Proof.
refine (Vector.rect2 _ _ _); simpl; intros; auto.
rewrite H.
destruct a, b, (Bv2N n v1), (Bv2N n v2);
 simpl; auto.
Qed.
