(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Representation of adresses by the [positive] type of binary numbers *)

Require Import Bool.
Require Import ZArith.

Inductive ad : Set :=
  | ad_z : ad
  | ad_x : positive -> ad.

Lemma ad_sum : forall a:ad, {p : positive | a = ad_x p} + {a = ad_z}.
Proof.
  destruct a; auto.
  left; exists p; trivial.
Qed.

Fixpoint p_xor (p p2:positive) {struct p} : ad :=
  match p with
  | xH =>
      match p2 with
      | xH => ad_z
      | xO p'2 => ad_x (xI p'2)
      | xI p'2 => ad_x (xO p'2)
      end
  | xO p' =>
      match p2 with
      | xH => ad_x (xI p')
      | xO p'2 =>
          match p_xor p' p'2 with
          | ad_z => ad_z
          | ad_x p'' => ad_x (xO p'')
          end
      | xI p'2 =>
          match p_xor p' p'2 with
          | ad_z => ad_x 1
          | ad_x p'' => ad_x (xI p'')
          end
      end
  | xI p' =>
      match p2 with
      | xH => ad_x (xO p')
      | xO p'2 =>
          match p_xor p' p'2 with
          | ad_z => ad_x 1
          | ad_x p'' => ad_x (xI p'')
          end
      | xI p'2 =>
          match p_xor p' p'2 with
          | ad_z => ad_z
          | ad_x p'' => ad_x (xO p'')
          end
      end
  end.

Definition ad_xor (a a':ad) :=
  match a with
  | ad_z => a'
  | ad_x p => match a' with
              | ad_z => a
              | ad_x p' => p_xor p p'
              end
  end.

Lemma ad_xor_neutral_left : forall a:ad, ad_xor ad_z a = a.
Proof.
  trivial.
Qed.

Lemma ad_xor_neutral_right : forall a:ad, ad_xor a ad_z = a.
Proof.
  destruct a; trivial.
Qed.

Lemma ad_xor_comm : forall a a':ad, ad_xor a a' = ad_xor a' a.
Proof.
  destruct a; destruct a'; simpl in |- *; auto.
  generalize p0; clear p0; induction p as [p Hrecp| p Hrecp| ]; simpl in |- *;
   auto.
  destruct p0; simpl in |- *; trivial; intros.
  rewrite Hrecp; trivial.
  rewrite Hrecp; trivial.
  destruct p0; simpl in |- *; trivial; intros.
  rewrite Hrecp; trivial.
  rewrite Hrecp; trivial.
  destruct p0 as [p| p| ]; simpl in |- *; auto.
Qed.

Lemma ad_xor_nilpotent : forall a:ad, ad_xor a a = ad_z.
Proof.
  destruct a; trivial.
  simpl in |- *. induction p as [p IHp| p IHp| ]; trivial.
  simpl in |- *. rewrite IHp; reflexivity.
  simpl in |- *. rewrite IHp; reflexivity.
Qed.

Fixpoint ad_bit_1 (p:positive) : nat -> bool :=
  match p with
  | xH => fun n:nat => match n with
                       | O => true
                       | S _ => false
                       end
  | xO p =>
      fun n:nat => match n with
                   | O => false
                   | S n' => ad_bit_1 p n'
                   end
  | xI p => fun n:nat => match n with
                         | O => true
                         | S n' => ad_bit_1 p n'
                         end
  end.

Definition ad_bit (a:ad) :=
  match a with
  | ad_z => fun _:nat => false
  | ad_x p => ad_bit_1 p
  end.

Definition eqf (f g:nat -> bool) := forall n:nat, f n = g n.

Lemma ad_faithful_1 : forall a:ad, eqf (ad_bit ad_z) (ad_bit a) -> ad_z = a.
Proof.
  destruct a. trivial.
  induction p as [p IHp| p IHp| ]; intro H. absurd (ad_z = ad_x p). discriminate.
  exact (IHp (fun n:nat => H (S n))).
  absurd (ad_z = ad_x p). discriminate.
  exact (IHp (fun n:nat => H (S n))).
  absurd (false = true). discriminate.
  exact (H 0).
Qed.

Lemma ad_faithful_2 :
 forall a:ad, eqf (ad_bit (ad_x 1)) (ad_bit a) -> ad_x 1 = a.
Proof.
  destruct a. intros. absurd (true = false). discriminate.
  exact (H 0).
  destruct p. intro H. absurd (ad_z = ad_x p). discriminate.
  exact (ad_faithful_1 (ad_x p) (fun n:nat => H (S n))).
  intros. absurd (true = false). discriminate.
  exact (H 0).
  trivial.
Qed.

Lemma ad_faithful_3 :
 forall (a:ad) (p:positive),
   (forall p':positive, eqf (ad_bit (ad_x p)) (ad_bit (ad_x p')) -> p = p') ->
   eqf (ad_bit (ad_x (xO p))) (ad_bit a) -> ad_x (xO p) = a.
Proof.
  destruct a. intros. cut (eqf (ad_bit ad_z) (ad_bit (ad_x (xO p)))).
  intro. rewrite (ad_faithful_1 (ad_x (xO p)) H1). reflexivity.
  unfold eqf in |- *. intro. unfold eqf in H0. rewrite H0. reflexivity.
  case p. intros. absurd (false = true). discriminate.
  exact (H0 0).
  intros. rewrite (H p0 (fun n:nat => H0 (S n))). reflexivity.
  intros. absurd (false = true). discriminate.
  exact (H0 0).
Qed.

Lemma ad_faithful_4 :
 forall (a:ad) (p:positive),
   (forall p':positive, eqf (ad_bit (ad_x p)) (ad_bit (ad_x p')) -> p = p') ->
   eqf (ad_bit (ad_x (xI p))) (ad_bit a) -> ad_x (xI p) = a.
Proof.
  destruct a. intros. cut (eqf (ad_bit ad_z) (ad_bit (ad_x (xI p)))).
  intro. rewrite (ad_faithful_1 (ad_x (xI p)) H1). reflexivity.
  unfold eqf in |- *. intro. unfold eqf in H0. rewrite H0. reflexivity.
  case p. intros. rewrite (H p0 (fun n:nat => H0 (S n))). reflexivity.
  intros. absurd (true = false). discriminate.
  exact (H0 0).
  intros. absurd (ad_z = ad_x p0). discriminate.
  cut (eqf (ad_bit (ad_x 1)) (ad_bit (ad_x (xI p0)))).
  intro. exact (ad_faithful_1 (ad_x p0) (fun n:nat => H1 (S n))).
  unfold eqf in |- *. unfold eqf in H0. intro. rewrite H0. reflexivity.
Qed.

Lemma ad_faithful : forall a a':ad, eqf (ad_bit a) (ad_bit a') -> a = a'.
Proof.
  destruct a. exact ad_faithful_1.
  induction p. intros a' H. apply ad_faithful_4. intros. cut (ad_x p = ad_x p').
  intro. inversion H1. reflexivity.
  exact (IHp (ad_x p') H0).
  assumption.
  intros. apply ad_faithful_3. intros. cut (ad_x p = ad_x p'). intro. inversion H1. reflexivity.
  exact (IHp (ad_x p') H0).
  assumption.
  exact ad_faithful_2.
Qed.

Definition adf_xor (f g:nat -> bool) (n:nat) := xorb (f n) (g n).

Lemma ad_xor_sem_1 : forall a':ad, ad_bit (ad_xor ad_z a') 0 = ad_bit a' 0.
Proof.
  trivial.
Qed.

Lemma ad_xor_sem_2 :
 forall a':ad, ad_bit (ad_xor (ad_x 1) a') 0 = negb (ad_bit a' 0).
Proof.
  intro. case a'. trivial.
  simpl in |- *. intro. 
  case p; trivial.
Qed.

Lemma ad_xor_sem_3 :
 forall (p:positive) (a':ad),
   ad_bit (ad_xor (ad_x (xO p)) a') 0 = ad_bit a' 0.
Proof.
  intros. case a'. trivial.
  simpl in |- *. intro. 
  case p0; trivial. intro. 
  case (p_xor p p1); trivial.
  intro. case (p_xor p p1); trivial.
Qed.

Lemma ad_xor_sem_4 :
 forall (p:positive) (a':ad),
   ad_bit (ad_xor (ad_x (xI p)) a') 0 = negb (ad_bit a' 0).
Proof.
  intros. case a'. trivial.
  simpl in |- *. intro. case p0; trivial. intro. 
  case (p_xor p p1); trivial.
  intro. 
  case (p_xor p p1); trivial.
Qed.

Lemma ad_xor_sem_5 :
 forall a a':ad, ad_bit (ad_xor a a') 0 = adf_xor (ad_bit a) (ad_bit a') 0.
Proof.
  destruct a. intro. change (ad_bit a' 0 = xorb false (ad_bit a' 0)) in |- *. rewrite false_xorb. trivial.
  case p. exact ad_xor_sem_4.
  intros. change (ad_bit (ad_xor (ad_x (xO p0)) a') 0 = xorb false (ad_bit a' 0))
  in |- *.
  rewrite false_xorb. apply ad_xor_sem_3. exact ad_xor_sem_2.
Qed.

Lemma ad_xor_sem_6 :
 forall n:nat,
   (forall a a':ad, ad_bit (ad_xor a a') n = adf_xor (ad_bit a) (ad_bit a') n) ->
   forall a a':ad,
     ad_bit (ad_xor a a') (S n) = adf_xor (ad_bit a) (ad_bit a') (S n).
Proof.
  intros. case a. unfold adf_xor in |- *. unfold ad_bit at 2 in |- *. rewrite false_xorb. reflexivity.
  case a'. unfold adf_xor in |- *. unfold ad_bit at 3 in |- *. intro. rewrite xorb_false. reflexivity.
  intros. case p0. case p. intros.
  change
    (ad_bit (ad_xor (ad_x (xI p2)) (ad_x (xI p1))) (S n) =
     adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n) 
   in |- *.
  rewrite <- H. simpl in |- *. 
  case (p_xor p2 p1); trivial.
  intros.
  change
    (ad_bit (ad_xor (ad_x (xI p2)) (ad_x (xO p1))) (S n) =
     adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n) 
   in |- *.
  rewrite <- H. simpl in |- *. 
  case (p_xor p2 p1); trivial.
  intro. unfold adf_xor in |- *. unfold ad_bit at 3 in |- *. unfold ad_bit_1 in |- *. rewrite xorb_false. reflexivity.
  case p. intros.
  change
    (ad_bit (ad_xor (ad_x (xO p2)) (ad_x (xI p1))) (S n) =
     adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n) 
   in |- *.
  rewrite <- H. simpl in |- *. 
  case (p_xor p2 p1); trivial.
  intros.
  change
    (ad_bit (ad_xor (ad_x (xO p2)) (ad_x (xO p1))) (S n) =
     adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n) 
   in |- *.
  rewrite <- H. simpl in |- *. 
  case (p_xor p2 p1); trivial.
  intro. unfold adf_xor in |- *. unfold ad_bit at 3 in |- *. unfold ad_bit_1 in |- *. rewrite xorb_false. reflexivity.
  unfold adf_xor in |- *. unfold ad_bit at 2 in |- *. unfold ad_bit_1 in |- *. rewrite false_xorb. simpl in |- *.   case p; trivial.
Qed.

Lemma ad_xor_semantics :
 forall a a':ad, eqf (ad_bit (ad_xor a a')) (adf_xor (ad_bit a) (ad_bit a')).
Proof.
  unfold eqf in |- *. intros. generalize a a'. elim n. exact ad_xor_sem_5.
  exact ad_xor_sem_6.
Qed.

Lemma eqf_sym : forall f f':nat -> bool, eqf f f' -> eqf f' f.
Proof.
  unfold eqf in |- *. intros. rewrite H. reflexivity.
Qed.

Lemma eqf_refl : forall f:nat -> bool, eqf f f.
Proof.
  unfold eqf in |- *. trivial.
Qed.

Lemma eqf_trans :
 forall f f' f'':nat -> bool, eqf f f' -> eqf f' f'' -> eqf f f''.
Proof.
  unfold eqf in |- *. intros. rewrite H. exact (H0 n).
Qed.

Lemma adf_xor_eq :
 forall f f':nat -> bool, eqf (adf_xor f f') (fun n:nat => false) -> eqf f f'.
Proof.
  unfold eqf in |- *. unfold adf_xor in |- *. intros. apply xorb_eq. apply H.
Qed.

Lemma ad_xor_eq : forall a a':ad, ad_xor a a' = ad_z -> a = a'.
Proof.
  intros. apply ad_faithful. apply adf_xor_eq. apply eqf_trans with (f' := ad_bit (ad_xor a a')).
  apply eqf_sym. apply ad_xor_semantics.
  rewrite H. unfold eqf in |- *. trivial.
Qed.

Lemma adf_xor_assoc :
 forall f f' f'':nat -> bool,
   eqf (adf_xor (adf_xor f f') f'') (adf_xor f (adf_xor f' f'')).
Proof.
  unfold eqf in |- *. unfold adf_xor in |- *. intros. apply xorb_assoc.
Qed.

Lemma eqf_xor_1 :
 forall f f' f'' f''':nat -> bool,
   eqf f f' -> eqf f'' f''' -> eqf (adf_xor f f'') (adf_xor f' f''').
Proof.
  unfold eqf in |- *. intros. unfold adf_xor in |- *. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma ad_xor_assoc :
 forall a a' a'':ad, ad_xor (ad_xor a a') a'' = ad_xor a (ad_xor a' a'').
Proof.
  intros. apply ad_faithful.
  apply eqf_trans with
   (f' := adf_xor (adf_xor (ad_bit a) (ad_bit a')) (ad_bit a'')).
  apply eqf_trans with (f' := adf_xor (ad_bit (ad_xor a a')) (ad_bit a'')).
  apply ad_xor_semantics.
  apply eqf_xor_1. apply ad_xor_semantics.
  apply eqf_refl.
  apply eqf_trans with
   (f' := adf_xor (ad_bit a) (adf_xor (ad_bit a') (ad_bit a''))).
  apply adf_xor_assoc.
  apply eqf_trans with (f' := adf_xor (ad_bit a) (ad_bit (ad_xor a' a''))).
  apply eqf_xor_1. apply eqf_refl.
  apply eqf_sym. apply ad_xor_semantics.
  apply eqf_sym. apply ad_xor_semantics.
Qed.

Definition ad_double (a:ad) :=
  match a with
  | ad_z => ad_z
  | ad_x p => ad_x (xO p)
  end.

Definition ad_double_plus_un (a:ad) :=
  match a with
  | ad_z => ad_x 1
  | ad_x p => ad_x (xI p)
  end.

Definition ad_div_2 (a:ad) :=
  match a with
  | ad_z => ad_z
  | ad_x xH => ad_z
  | ad_x (xO p) => ad_x p
  | ad_x (xI p) => ad_x p
  end.

Lemma ad_double_div_2 : forall a:ad, ad_div_2 (ad_double a) = a.
Proof.
  destruct a; trivial.
Qed.

Lemma ad_double_plus_un_div_2 :
 forall a:ad, ad_div_2 (ad_double_plus_un a) = a.
Proof.
  destruct a; trivial.
Qed.

Lemma ad_double_inj : forall a0 a1:ad, ad_double a0 = ad_double a1 -> a0 = a1.
Proof.
  intros. rewrite <- (ad_double_div_2 a0). rewrite H. apply ad_double_div_2.
Qed.

Lemma ad_double_plus_un_inj :
 forall a0 a1:ad, ad_double_plus_un a0 = ad_double_plus_un a1 -> a0 = a1.
Proof.
  intros. rewrite <- (ad_double_plus_un_div_2 a0). rewrite H. apply ad_double_plus_un_div_2.
Qed.

Definition ad_bit_0 (a:ad) :=
  match a with
  | ad_z => false
  | ad_x (xO _) => false
  | _ => true
  end.

Lemma ad_double_bit_0 : forall a:ad, ad_bit_0 (ad_double a) = false.
Proof.
  destruct a; trivial.
Qed.

Lemma ad_double_plus_un_bit_0 :
 forall a:ad, ad_bit_0 (ad_double_plus_un a) = true.
Proof.
  destruct a; trivial.
Qed.

Lemma ad_div_2_double :
 forall a:ad, ad_bit_0 a = false -> ad_double (ad_div_2 a) = a.
Proof.
  destruct a. trivial. destruct p. intro H. discriminate H.
  intros. reflexivity.
  intro H. discriminate H.
Qed.

Lemma ad_div_2_double_plus_un :
 forall a:ad, ad_bit_0 a = true -> ad_double_plus_un (ad_div_2 a) = a.
Proof.
  destruct a. intro. discriminate H.
  destruct p. intros. reflexivity.
  intro H. discriminate H.
  intro. reflexivity.
Qed.

Lemma ad_bit_0_correct : forall a:ad, ad_bit a 0 = ad_bit_0 a.
Proof.
  destruct a; trivial.
  destruct p; trivial.
Qed.

Lemma ad_div_2_correct :
 forall (a:ad) (n:nat), ad_bit (ad_div_2 a) n = ad_bit a (S n).
Proof.
  destruct a; trivial.
  destruct p; trivial.
Qed.

Lemma ad_xor_bit_0 :
 forall a a':ad, ad_bit_0 (ad_xor a a') = xorb (ad_bit_0 a) (ad_bit_0 a').
Proof.
  intros. rewrite <- ad_bit_0_correct. rewrite (ad_xor_semantics a a' 0).
  unfold adf_xor in |- *. rewrite ad_bit_0_correct. rewrite ad_bit_0_correct. reflexivity.
Qed.

Lemma ad_xor_div_2 :
 forall a a':ad, ad_div_2 (ad_xor a a') = ad_xor (ad_div_2 a) (ad_div_2 a').
Proof.
  intros. apply ad_faithful. unfold eqf in |- *. intro.
  rewrite (ad_xor_semantics (ad_div_2 a) (ad_div_2 a') n).
  rewrite ad_div_2_correct.
  rewrite (ad_xor_semantics a a' (S n)).
  unfold adf_xor in |- *. rewrite ad_div_2_correct. rewrite ad_div_2_correct.
  reflexivity.
Qed.

Lemma ad_neg_bit_0 :
 forall a a':ad,
   ad_bit_0 (ad_xor a a') = true -> ad_bit_0 a = negb (ad_bit_0 a').
Proof.
  intros. rewrite <- true_xorb. rewrite <- H. rewrite ad_xor_bit_0.
  rewrite xorb_assoc. rewrite xorb_nilpotent. rewrite xorb_false. reflexivity.
Qed.

Lemma ad_neg_bit_0_1 :
 forall a a':ad, ad_xor a a' = ad_x 1 -> ad_bit_0 a = negb (ad_bit_0 a').
Proof.
  intros. apply ad_neg_bit_0. rewrite H. reflexivity.
Qed.

Lemma ad_neg_bit_0_2 :
 forall (a a':ad) (p:positive),
   ad_xor a a' = ad_x (xI p) -> ad_bit_0 a = negb (ad_bit_0 a').
Proof.
  intros. apply ad_neg_bit_0. rewrite H. reflexivity.
Qed.

Lemma ad_same_bit_0 :
 forall (a a':ad) (p:positive),
   ad_xor a a' = ad_x (xO p) -> ad_bit_0 a = ad_bit_0 a'.
Proof.
  intros. rewrite <- (xorb_false (ad_bit_0 a)). cut (ad_bit_0 (ad_x (xO p)) = false).
  intro. rewrite <- H0. rewrite <- H. rewrite ad_xor_bit_0. rewrite <- xorb_assoc.
  rewrite xorb_nilpotent. rewrite false_xorb. reflexivity.
  reflexivity.
Qed.