(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Bool.
Require Import Bvector.
Require Import BinPos.
Require Import BinNat.

(** Operation over bits of a [N] number. *)

(** [xor] *)

Fixpoint Pxor (p1 p2:positive) {struct p1} : N :=
  match p1, p2 with
  | xH, xH => N0
  | xH, xO p2 => Npos (xI p2)
  | xH, xI p2 => Npos (xO p2)
  | xO p1, xH => Npos (xI p1)
  | xO p1, xO p2 => Ndouble (Pxor p1 p2)
  | xO p1, xI p2 => Ndouble_plus_one (Pxor p1 p2)
  | xI p1, xH => Npos (xO p1)
  | xI p1, xO p2 => Ndouble_plus_one (Pxor p1 p2)
  | xI p1, xI p2 => Ndouble (Pxor p1 p2) 
  end.

Definition Nxor (n n':N) :=
  match n, n' with
  | N0, _ => n'
  | _, N0 => n
  | Npos p, Npos p' => Pxor p p'
  end.

Lemma Nxor_neutral_left : forall n:N, Nxor N0 n = n.
Proof.
  trivial.
Qed.

Lemma Nxor_neutral_right : forall n:N, Nxor n N0 = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Nxor_comm : forall n n':N, Nxor n n' = Nxor n' n.
Proof.
  destruct n; destruct n'; simpl; auto.
  generalize p0; clear p0; induction p as [p Hrecp| p Hrecp| ]; simpl;
   auto.
  destruct p0; trivial; rewrite Hrecp; trivial.
  destruct p0; trivial; rewrite Hrecp; trivial.
  destruct p0 as [p| p| ]; simpl; auto.
Qed.

Lemma Nxor_nilpotent : forall n:N, Nxor n n = N0.
Proof.
  destruct n; trivial.
  simpl. induction p as [p IHp| p IHp| ]; trivial.
  simpl. rewrite IHp; reflexivity.
  simpl. rewrite IHp; reflexivity.
Qed.

(** Checking whether a particular bit is set on not *) 

Fixpoint Pbit (p:positive) : nat -> bool :=
  match p with
  | xH => fun n:nat => match n with
                       | O => true
                       | S _ => false
                       end
  | xO p =>
      fun n:nat => match n with
                   | O => false
                   | S n' => Pbit p n'
                   end
  | xI p => fun n:nat => match n with
                         | O => true
                         | S n' => Pbit p n'
                         end
  end.

Definition Nbit (a:N) :=
  match a with
  | N0 => fun _ => false
  | Npos p => Pbit p
  end.

(** Auxiliary results about streams of bits *)

Definition eqf (f g:nat -> bool) := forall n:nat, f n = g n.

Lemma eqf_sym : forall f f':nat -> bool, eqf f f' -> eqf f' f.
Proof.
  unfold eqf. intros. rewrite H. reflexivity.
Qed.

Lemma eqf_refl : forall f:nat -> bool, eqf f f.
Proof.
  unfold eqf. trivial.
Qed.

Lemma eqf_trans :
 forall f f' f'':nat -> bool, eqf f f' -> eqf f' f'' -> eqf f f''.
Proof.
  unfold eqf. intros. rewrite H. exact (H0 n).
Qed.

Definition xorf (f g:nat -> bool) (n:nat) := xorb (f n) (g n).

Lemma xorf_eq :
 forall f f', eqf (xorf f f') (fun n => false) -> eqf f f'.
Proof.
  unfold eqf, xorf. intros. apply xorb_eq, H.
Qed.

Lemma xorf_assoc :
 forall f f' f'',
   eqf (xorf (xorf f f') f'') (xorf f (xorf f' f'')).
Proof.
  unfold eqf, xorf. intros. apply xorb_assoc.
Qed.

Lemma eqf_xorf :
 forall f f' f'' f''',
   eqf f f' -> eqf f'' f''' -> eqf (xorf f f'') (xorf f' f''').
Proof.
  unfold eqf, xorf. intros. rewrite H. rewrite H0. reflexivity.
Qed.

(** End of auxilliary results *)

(** This part is aimed at proving that if two numbers produce 
  the same stream of bits, then they are equal. *)

Lemma Nbit_faithful_1 : forall a:N, eqf (Nbit N0) (Nbit a) -> N0 = a.
Proof.
  destruct a. trivial.
  induction p as [p IHp| p IHp| ]; intro H. 
  absurd (N0 = Npos p). discriminate.
  exact (IHp (fun n => H (S n))).
  absurd (N0 = Npos p). discriminate.
  exact (IHp (fun n => H (S n))).
  absurd (false = true). discriminate.
  exact (H 0).
Qed.

Lemma Nbit_faithful_2 :
 forall a:N, eqf (Nbit (Npos 1)) (Nbit a) -> Npos 1 = a.
Proof.
  destruct a. intros. absurd (true = false). discriminate.
  exact (H 0).
  destruct p. intro H. absurd (N0 = Npos p). discriminate.
  exact (Nbit_faithful_1 (Npos p) (fun n:nat => H (S n))).
  intros. absurd (true = false). discriminate.
  exact (H 0).
  trivial.
Qed.

Lemma Nbit_faithful_3 :
 forall (a:N) (p:positive),
   (forall p':positive, eqf (Nbit (Npos p)) (Nbit (Npos p')) -> p = p') ->
   eqf (Nbit (Npos (xO p))) (Nbit a) -> Npos (xO p) = a.
Proof.
  destruct a; intros. cut (eqf (Nbit N0) (Nbit (Npos (xO p)))).
  intro. rewrite (Nbit_faithful_1 (Npos (xO p)) H1). reflexivity.
  unfold eqf. intro. unfold eqf in H0. rewrite H0. reflexivity.
  destruct p. discriminate (H0 O).
  rewrite (H p (fun n => H0 (S n))). reflexivity.
  discriminate (H0 0).
Qed.

Lemma Nbit_faithful_4 :
 forall (a:N) (p:positive),
   (forall p':positive, eqf (Nbit (Npos p)) (Nbit (Npos p')) -> p = p') ->
   eqf (Nbit (Npos (xI p))) (Nbit a) -> Npos (xI p) = a.
Proof.
  destruct a; intros. cut (eqf (Nbit N0) (Nbit (Npos (xI p)))).
  intro. rewrite (Nbit_faithful_1 (Npos (xI p)) H1). reflexivity.
  intro. rewrite H0. reflexivity.
  destruct p. rewrite (H p (fun n:nat => H0 (S n))). reflexivity.
  discriminate (H0 0).
  cut (eqf (Nbit (Npos 1)) (Nbit (Npos (xI p0)))).
  intro. discriminate (Nbit_faithful_1 (Npos p0) (fun n:nat => H1 (S n))).
  intro. rewrite H0. reflexivity.
Qed.

Lemma Nbit_faithful : forall a a':N, eqf (Nbit a) (Nbit a') -> a = a'.
Proof.
  destruct a. exact Nbit_faithful_1.
  induction p. intros a' H. apply Nbit_faithful_4. intros.
  assert (Npos p = Npos p') by exact (IHp (Npos p') H0).
  inversion H1. reflexivity.
  assumption.
  intros. apply Nbit_faithful_3. intros. 
  assert (Npos p = Npos p') by exact (IHp (Npos p') H0).
  inversion H1. reflexivity.
  assumption.
  exact Nbit_faithful_2.
Qed.

(** We now describe the semantics of [Nxor] in terms of bit streams. *)

Lemma Nxor_sem_1 : forall a':N, Nbit (Nxor N0 a') 0 = Nbit a' 0.
Proof.
  trivial.
Qed.

Lemma Nxor_sem_2 :
 forall a':N, Nbit (Nxor (Npos 1) a') 0 = negb (Nbit a' 0).
Proof.
  intro. destruct a'. trivial.
  destruct p; trivial.
Qed.

Lemma Nxor_sem_3 :
 forall (p:positive) (a':N),
   Nbit (Nxor (Npos (xO p)) a') 0 = Nbit a' 0.
Proof.
  intros. destruct a'. trivial.
  simpl. destruct p0; trivial.
  destruct (Pxor p p0); trivial.
  destruct (Pxor p p0); trivial.
Qed.

Lemma Nxor_sem_4 :
 forall (p:positive) (a':N),
   Nbit (Nxor (Npos (xI p)) a') 0 = negb (Nbit a' 0).
Proof.
  intros. destruct a'. trivial.
  simpl. destruct p0; trivial.
  destruct (Pxor p p0); trivial.
  destruct (Pxor p p0); trivial.
Qed.

Lemma Nxor_sem_5 :
 forall a a':N, Nbit (Nxor a a') 0 = xorf (Nbit a) (Nbit a') 0.
Proof.
  destruct a; intro. change (Nbit a' 0 = xorb false (Nbit a' 0)). rewrite false_xorb. trivial.
  destruct p. apply Nxor_sem_4.
  change (Nbit (Nxor (Npos (xO p)) a') 0 = xorb false (Nbit a' 0)).
  rewrite false_xorb. apply Nxor_sem_3. apply Nxor_sem_2.
Qed.

Lemma Nxor_sem_6 :
 forall n:nat,
   (forall a a':N, Nbit (Nxor a a') n = xorf (Nbit a) (Nbit a') n) ->
   forall a a':N,
     Nbit (Nxor a a') (S n) = xorf (Nbit a) (Nbit a') (S n).
Proof.
  intros.
(* pose proof (fun p1 p2 => H (Npos p1) (Npos p2)) as H'. clear H. rename H' into H.*)
  generalize (fun p1 p2 => H (Npos p1) (Npos p2)); clear H; intro H.
  unfold xorf in *.
  destruct a as [|p]. simpl Nbit; rewrite false_xorb. reflexivity.
  destruct a' as [|p0]. 
  simpl Nbit; rewrite xorb_false. reflexivity.
  destruct p. destruct p0; simpl Nbit in *.
  rewrite <- H; simpl; case (Pxor p p0); trivial.
  rewrite <- H; simpl; case (Pxor p p0); trivial.
  rewrite xorb_false. reflexivity.
  destruct p0; simpl Nbit in *.
  rewrite <- H; simpl; case (Pxor p p0); trivial.
  rewrite <- H; simpl; case (Pxor p p0); trivial.
  rewrite xorb_false. reflexivity.
  simpl Nbit. rewrite false_xorb. destruct p0; trivial.
Qed.

Lemma Nxor_semantics :
 forall a a':N, eqf (Nbit (Nxor a a')) (xorf (Nbit a) (Nbit a')).
Proof.
  unfold eqf. intros; generalize a, a'. induction n. 
  apply Nxor_sem_5. apply Nxor_sem_6; assumption.
Qed.

(** Consequences: 
       - only equal numbers lead to a null xor
       - xor is associative 
*)

Lemma Nxor_eq : forall a a':N, Nxor a a' = N0 -> a = a'.
Proof.
  intros. apply Nbit_faithful, xorf_eq. apply eqf_trans with (f' := Nbit (Nxor a a')).
  apply eqf_sym, Nxor_semantics.
  rewrite H. unfold eqf. trivial.
Qed.

Lemma Nxor_assoc :
 forall a a' a'':N, Nxor (Nxor a a') a'' = Nxor a (Nxor a' a'').
Proof.
  intros. apply Nbit_faithful.
  apply eqf_trans with (xorf (xorf (Nbit a) (Nbit a')) (Nbit a'')).
  apply eqf_trans with (xorf (Nbit (Nxor a a')) (Nbit a'')).
  apply Nxor_semantics.
  apply eqf_xorf. apply Nxor_semantics.
  apply eqf_refl.
  apply eqf_trans with (xorf (Nbit a) (xorf (Nbit a') (Nbit a''))).
  apply xorf_assoc.
  apply eqf_trans with (xorf (Nbit a) (Nbit (Nxor a' a''))).
  apply eqf_xorf. apply eqf_refl.
  apply eqf_sym, Nxor_semantics.
  apply eqf_sym, Nxor_semantics.
Qed.

(** Checking whether a number is odd, i.e. 
   if its lower bit is set. *)

Definition Nbit0 (n:N) :=
  match n with
  | N0 => false
  | Npos (xO _) => false
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
  intros. rewrite <- Nbit0_correct, (Nxor_semantics a a' 0).
  unfold xorf. rewrite Nbit0_correct, Nbit0_correct. reflexivity.
Qed.

Lemma Nxor_div2 :
 forall a a':N, Ndiv2 (Nxor a a') = Nxor (Ndiv2 a) (Ndiv2 a').
Proof.
  intros. apply Nbit_faithful. unfold eqf. intro.
  rewrite (Nxor_semantics (Ndiv2 a) (Ndiv2 a') n), Ndiv2_correct, (Nxor_semantics a a' (S n)).
  unfold xorf. rewrite 2! Ndiv2_correct.
  reflexivity.
Qed.

Lemma Nneg_bit0 :
 forall a a':N,
   Nbit0 (Nxor a a') = true -> Nbit0 a = negb (Nbit0 a').
Proof.
  intros. 
  rewrite <- true_xorb, <- H, Nxor_bit0, xorb_assoc, xorb_nilpotent, xorb_false. 
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
  rewrite <- H0, <- H, Nxor_bit0, <- xorb_assoc, xorb_nilpotent, false_xorb. reflexivity.
Qed.

(** a lexicographic order on bits, starting from the lowest bit *)

Fixpoint Nless_aux (a a':N) (p:positive) {struct p} : bool :=
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
  elimtype False. induction p as [|p IHp|]; discriminate || simpl; auto using IHp.
Qed.

Lemma Nless_trans :
 forall a a' a'',
   Nless a a' = true -> Nless a' a'' = true -> Nless a a'' = true.
Proof.
  induction a as [|a IHa|a IHa] using N_ind_double; intros a' a'' H H0.
    destruct (Nless N0 a'') as Heqb in *. trivial.
     rewrite (N0_less_2 a'' Heqb), (Nless_z a') in H0. discriminate H0.
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
    destruct (Nless N0 a') as Heqb in *. left. left. auto.
     right. rewrite (N0_less_2 a' Heqb). reflexivity.
    induction a' as [|a' _|a' _] using N_rec_double.
      destruct (Nless N0 (Ndouble a)) as Heqb in *. left. right. auto.
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
  | N0 => 0%nat
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

Fixpoint Bv2N (n:nat)(bv:Bvector n) {struct bv} : N := 
  match bv with 
    | Vnil => N0
    | Vcons false n bv => Ndouble (Bv2N n bv)
    | Vcons true n bv => Ndouble_plus_one (Bv2N n bv) 
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
induction n; intros.
rewrite (V0_eq _ bv); simpl; auto.
rewrite (VSn_eq _ _ bv); simpl.
specialize IHn with (Vtail _ _ bv).
destruct (Vhead _ _ bv); 
 destruct (Bv2N n (Vtail bool n bv)); 
  simpl; auto with arith.
Qed.

(** In the previous lemma, we can only replace the inequality by
  an equality whenever the highest bit is non-null. *)

Lemma Bv2N_Nsize_1 : forall n (bv:Bvector (S n)), 
  Bsign _ bv = true <-> 
  Nsize (Bv2N _ bv) = (S n).
Proof.
induction n; intro.
rewrite (VSn_eq _ _ bv); simpl.
rewrite (V0_eq _ (Vtail _ _ bv)); simpl.
destruct (Vhead _ _ bv); simpl; intuition; try discriminate.
rewrite (VSn_eq _ _ bv); simpl.
generalize (IHn (Vtail _ _ bv)); clear IHn.
destruct (Vhead _ _ bv); 
 destruct (Bv2N (S n) (Vtail bool (S n) bv)); 
  simpl; intuition; try discriminate.
Qed.

(** To state nonetheless a second result about composition of 
 conversions, we define a conversion on a given number of bits : *) 

Fixpoint N2Bv_gen (n:nat)(a:N) { struct n } : Bvector n := 
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
 N2Bv_gen (Nsize a + k) a = Vextend _ _ _ (N2Bv a) (Bvect_false k).
Proof.
destruct a; simpl.
destruct k; simpl; auto.
induction p; simpl; intros;unfold Bcons; f_equal; auto.
Qed.

(** Here comes now the second composition result. *)

Lemma N2Bv_Bv2N : forall n (bv:Bvector n), 
   N2Bv_gen n (Bv2N n bv) = bv.
Proof.
induction n; intros.
rewrite (V0_eq _ bv); simpl; auto.
rewrite (VSn_eq _ _ bv); simpl.
generalize (IHn (Vtail _ _ bv)); clear IHn.
unfold Bcons.
destruct (Bv2N _ (Vtail _ _ bv)); 
 destruct (Vhead _ _ bv); intro H; rewrite <- H; simpl; trivial; 
  induction n; simpl; auto.
Qed.

(** accessing some precise bits. *)

Lemma Nbit0_Blow : forall n, forall (bv:Bvector (S n)), 
  Nbit0 (Bv2N _ bv) = Blow _ bv.
Proof.
intros.
unfold Blow.
rewrite (VSn_eq _ _ bv) at 1.
simpl.
destruct (Bv2N n (Vtail bool n bv)); simpl; 
 destruct (Vhead bool n bv); auto.
Qed.

Definition Bnth (n:nat)(bv:Bvector n)(p:nat) : p<n -> bool.
Proof.
 induction 1.
 intros.
 elimtype False; inversion H.
 intros.
 destruct p.
 exact a.
 apply (IHbv p); auto with arith.
Defined.

Lemma Bnth_Nbit : forall n (bv:Bvector n) p (H:p<n), 
  Bnth _ bv p H = Nbit (Bv2N _ bv) p.
Proof.
induction bv; intros.
inversion H.
destruct p; simpl; destruct (Bv2N n bv); destruct a; simpl in *; auto.
Qed.

Lemma Nbit_Nsize : forall n p, Nsize n <= p -> Nbit n p = false.
Proof.
destruct n as [|n].
simpl; auto.
induction n; simpl in *; intros; destruct p; auto with arith.
inversion H.
inversion H.
Qed.

Lemma Nbit_Bth: forall n p (H:p < Nsize n), Nbit n p = Bnth _ (N2Bv n) p H.
Proof.
destruct n as [|n].
inversion H.
induction n; simpl in *; intros; destruct p; auto with arith.
inversion H; inversion H1.
Qed.

(** Xor is the same in the two worlds. *)

Lemma Nxor_BVxor : forall n (bv bv' : Bvector n), 
  Bv2N _ (BVxor _ bv bv') = Nxor (Bv2N _ bv) (Bv2N _ bv').
Proof.
induction n.
intros.
rewrite (V0_eq _ bv), (V0_eq _ bv'); simpl; auto.
intros.
rewrite (VSn_eq _ _ bv), (VSn_eq _ _ bv'); simpl; auto.
rewrite IHn.
destruct (Vhead bool n bv); destruct (Vhead bool n bv'); 
 destruct (Bv2N n (Vtail bool n bv)); destruct (Bv2N n (Vtail bool n bv')); simpl; auto.
Qed.

