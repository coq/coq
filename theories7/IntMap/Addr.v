(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Representation of adresses by the [positive] type of binary numbers *)

Require Bool.
Require ZArith.

Inductive ad : Set :=
    ad_z : ad
  | ad_x : positive -> ad.

Lemma ad_sum : (a:ad) {p:positive | a=(ad_x p)}+{a=ad_z}.
Proof.
  NewDestruct a; Auto.
  Left; Exists p; Trivial.
Qed.

Fixpoint p_xor [p:positive] : positive -> ad :=
  [p2] Cases p of
      xH => Cases p2 of
	        xH => ad_z
	      | (xO p'2) => (ad_x (xI p'2))
	      | (xI p'2) => (ad_x (xO p'2))
	    end
    | (xO p') => Cases p2 of
                     xH => (ad_x (xI p'))
		   | (xO p'2) => Cases (p_xor p' p'2) of
		                     ad_z => ad_z
				   | (ad_x p'') => (ad_x (xO p''))
				 end
		   | (xI p'2) => Cases (p_xor p' p'2) of
		                     ad_z => (ad_x xH)
				   | (ad_x p'') => (ad_x (xI p''))
				 end
                 end
    | (xI p') => Cases p2 of
		     xH => (ad_x (xO p'))
		   | (xO p'2) => Cases (p_xor p' p'2) of
		                     ad_z => (ad_x xH)
				   | (ad_x p'') => (ad_x (xI p''))
				 end
		   | (xI p'2) => Cases (p_xor p' p'2) of
		                     ad_z => ad_z
				   | (ad_x p'') => (ad_x (xO p''))
				 end
                 end
  end.

Definition ad_xor := [a,a':ad]
  Cases a of
      ad_z => a'
    | (ad_x p) => Cases a' of
                      ad_z => a
	            | (ad_x p') => (p_xor p p')
                  end
  end.

Lemma ad_xor_neutral_left : (a:ad) (ad_xor ad_z a)=a.
Proof.
  Trivial.
Qed.

Lemma ad_xor_neutral_right : (a:ad) (ad_xor a ad_z)=a.
Proof.
  NewDestruct a; Trivial.
Qed.

Lemma ad_xor_comm : (a,a':ad) (ad_xor a a')=(ad_xor a' a).
Proof.
  NewDestruct a; NewDestruct a'; Simpl; Auto.
  Generalize p0; Clear p0; NewInduction p as [p Hrecp|p Hrecp|]; Simpl; Auto.
  NewDestruct p0; Simpl; Trivial; Intros.
  Rewrite Hrecp; Trivial.
  Rewrite Hrecp; Trivial.
  NewDestruct p0; Simpl; Trivial; Intros.
  Rewrite Hrecp; Trivial.
  Rewrite Hrecp; Trivial.
  NewDestruct p0; Simpl; Auto.
Qed.

Lemma ad_xor_nilpotent : (a:ad) (ad_xor a a)=ad_z.
Proof.
  NewDestruct a; Trivial.
  Simpl. NewInduction p as [p IHp|p IHp|]; Trivial.
  Simpl. Rewrite IHp; Reflexivity.
  Simpl. Rewrite IHp; Reflexivity.
Qed.

Fixpoint ad_bit_1 [p:positive] : nat -> bool :=
  Cases p of
      xH => [n:nat] Cases n of
                        O => true
		      | (S _) => false
		    end
    | (xO p) => [n:nat] Cases n of
                            O => false
			  | (S n') => (ad_bit_1 p n')
		        end
    | (xI p) => [n:nat] Cases n of
                            O => true
			  | (S n') => (ad_bit_1 p n')
		        end
  end.

Definition ad_bit := [a:ad]
  Cases a of
      ad_z => [_:nat] false
    | (ad_x p) => (ad_bit_1 p)
  end.

Definition eqf := [f,g:nat->bool] (n:nat) (f n)=(g n).

Lemma ad_faithful_1 : (a:ad) (eqf (ad_bit ad_z) (ad_bit a)) -> ad_z=a.
Proof.
  NewDestruct a. Trivial.
  NewInduction p as [p IHp|p IHp|];Intro H. Absurd ad_z=(ad_x p). Discriminate.
  Exact (IHp [n:nat](H (S n))).
  Absurd ad_z=(ad_x p). Discriminate.
  Exact (IHp [n:nat](H (S n))).
  Absurd false=true. Discriminate.
  Exact (H O).
Qed.

Lemma ad_faithful_2 : (a:ad) (eqf (ad_bit (ad_x xH)) (ad_bit a)) -> (ad_x xH)=a.
Proof.
  NewDestruct a. Intros. Absurd true=false. Discriminate.
  Exact (H O).
  NewDestruct p. Intro H. Absurd ad_z=(ad_x p). Discriminate.
  Exact (ad_faithful_1 (ad_x p) [n:nat](H (S n))).
  Intros. Absurd true=false. Discriminate.
  Exact (H O).
  Trivial.
Qed.

Lemma ad_faithful_3 :
    (a:ad) (p:positive)
      ((p':positive) (eqf (ad_bit (ad_x p)) (ad_bit (ad_x p'))) -> p=p') ->
        (eqf (ad_bit (ad_x (xO p))) (ad_bit a)) ->
          (ad_x (xO p))=a.
Proof.
  NewDestruct a. Intros. Cut (eqf (ad_bit ad_z) (ad_bit (ad_x (xO p)))).
  Intro. Rewrite (ad_faithful_1 (ad_x (xO p)) H1). Reflexivity.
  Unfold eqf. Intro. Unfold eqf in H0. Rewrite H0. Reflexivity.
  Case p. Intros. Absurd false=true. Discriminate.
  Exact (H0 O).
  Intros. Rewrite (H p0 [n:nat](H0 (S n))). Reflexivity.
  Intros. Absurd false=true. Discriminate.
  Exact (H0 O).
Qed.

Lemma ad_faithful_4 :
    (a:ad) (p:positive)
      ((p':positive) (eqf (ad_bit (ad_x p)) (ad_bit (ad_x p'))) -> p=p') ->
        (eqf (ad_bit (ad_x (xI p))) (ad_bit a)) ->
          (ad_x (xI p))=a.
Proof.
  NewDestruct a. Intros. Cut (eqf (ad_bit ad_z) (ad_bit (ad_x (xI p)))).
  Intro. Rewrite (ad_faithful_1 (ad_x (xI p)) H1). Reflexivity.
  Unfold eqf. Intro. Unfold eqf in H0. Rewrite H0. Reflexivity.
  Case p. Intros. Rewrite (H p0 [n:nat](H0 (S n))). Reflexivity.
  Intros. Absurd true=false. Discriminate.
  Exact (H0 O).
  Intros. Absurd ad_z=(ad_x p0). Discriminate.
  Cut (eqf (ad_bit (ad_x xH)) (ad_bit (ad_x (xI p0)))).
  Intro. Exact (ad_faithful_1 (ad_x p0) [n:nat](H1 (S n))).
  Unfold eqf. Unfold eqf in H0. Intro. Rewrite H0. Reflexivity.
Qed.

Lemma ad_faithful : (a,a':ad) (eqf (ad_bit a) (ad_bit a')) -> a=a'.
Proof.
  NewDestruct a. Exact ad_faithful_1.
  NewInduction p. Intros a' H. Apply ad_faithful_4. Intros. Cut (ad_x p)=(ad_x p').
  Intro. Inversion H1. Reflexivity.
  Exact (IHp (ad_x p') H0).
  Assumption.
  Intros. Apply ad_faithful_3. Intros. Cut (ad_x p)=(ad_x p'). Intro. Inversion H1. Reflexivity.
  Exact (IHp (ad_x p') H0).
  Assumption.
  Exact ad_faithful_2.
Qed.

Definition adf_xor := [f,g:nat->bool; n:nat] (xorb (f n) (g n)).

Lemma ad_xor_sem_1 : (a':ad) (ad_bit (ad_xor ad_z a') O)=(ad_bit a' O).
Proof.
  Trivial.
Qed.

Lemma ad_xor_sem_2 : (a':ad) (ad_bit (ad_xor (ad_x xH) a') O)=(negb (ad_bit a' O)).
Proof.
  Intro. Case a'. Trivial.
  Simpl. Intro. 
  Case p; Trivial.
Qed.

Lemma ad_xor_sem_3 :
    (p:positive) (a':ad) (ad_bit (ad_xor (ad_x (xO p)) a') O)=(ad_bit a' O).
Proof.
  Intros. Case a'. Trivial.
  Simpl. Intro. 
  Case p0; Trivial. Intro. 
  Case (p_xor p p1); Trivial.
  Intro. Case (p_xor p p1); Trivial.
Qed.

Lemma ad_xor_sem_4 : (p:positive) (a':ad)
    (ad_bit (ad_xor (ad_x (xI p)) a') O)=(negb (ad_bit a' O)).
Proof.
  Intros. Case a'. Trivial.
  Simpl. Intro. Case p0; Trivial. Intro. 
  Case (p_xor p p1); Trivial.
  Intro. 
  Case (p_xor p p1); Trivial.
Qed.

Lemma ad_xor_sem_5 :
    (a,a':ad) (ad_bit (ad_xor a a') O)=(adf_xor (ad_bit a) (ad_bit a') O).
Proof.
  NewDestruct a. Intro. Change (ad_bit a' O)=(xorb false (ad_bit a' O)). Rewrite false_xorb. Trivial.
  Case p. Exact ad_xor_sem_4.
  Intros. Change (ad_bit (ad_xor (ad_x (xO p0)) a') O)=(xorb false (ad_bit a' O)).
  Rewrite false_xorb. Apply ad_xor_sem_3. Exact ad_xor_sem_2.
Qed.

Lemma ad_xor_sem_6 : (n:nat)
    ((a,a':ad) (ad_bit (ad_xor a a') n)=(adf_xor (ad_bit a) (ad_bit a') n)) ->
      (a,a':ad) (ad_bit (ad_xor a a') (S n))=(adf_xor (ad_bit a) (ad_bit a') (S n)).
Proof.
  Intros. Case a. Unfold adf_xor. Unfold 2 ad_bit. Rewrite false_xorb. Reflexivity.
  Case a'. Unfold adf_xor. Unfold 3 ad_bit. Intro. Rewrite xorb_false. Reflexivity.
  Intros. Case p0. Case p. Intros.
  Change (ad_bit (ad_xor (ad_x (xI p2)) (ad_x (xI p1))) (S n))
        =(adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n).
  Rewrite <- H. Simpl. 
  Case (p_xor p2 p1); Trivial.
  Intros.
  Change (ad_bit (ad_xor (ad_x (xI p2)) (ad_x (xO p1))) (S n))
        =(adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n).
  Rewrite <- H. Simpl. 
  Case (p_xor p2 p1); Trivial.
  Intro. Unfold adf_xor. Unfold 3 ad_bit. Unfold ad_bit_1. Rewrite xorb_false. Reflexivity.
  Case p. Intros.
  Change (ad_bit (ad_xor (ad_x (xO p2)) (ad_x (xI p1))) (S n))
        =(adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n).
  Rewrite <- H. Simpl. 
  Case (p_xor p2 p1); Trivial.
  Intros.
  Change (ad_bit (ad_xor (ad_x (xO p2)) (ad_x (xO p1))) (S n))
        =(adf_xor (ad_bit (ad_x p2)) (ad_bit (ad_x p1)) n).
  Rewrite <- H. Simpl. 
  Case (p_xor p2 p1); Trivial.
  Intro. Unfold adf_xor. Unfold 3 ad_bit. Unfold ad_bit_1. Rewrite xorb_false. Reflexivity.
  Unfold adf_xor. Unfold 2 ad_bit. Unfold ad_bit_1. Rewrite false_xorb. Simpl.   Case p; Trivial.
Qed.

Lemma ad_xor_semantics :
    (a,a':ad) (eqf (ad_bit (ad_xor a a')) (adf_xor (ad_bit a) (ad_bit a'))).
Proof.
  Unfold eqf. Intros. Generalize a a'. Elim n. Exact ad_xor_sem_5.
  Exact ad_xor_sem_6.
Qed.

Lemma eqf_sym : (f,f':nat->bool) (eqf f f') -> (eqf f' f).
Proof.
  Unfold eqf. Intros. Rewrite H. Reflexivity.
Qed.

Lemma eqf_refl :  (f:nat->bool) (eqf f f).
Proof.
  Unfold eqf. Trivial.
Qed.

Lemma eqf_trans : (f,f',f'':nat->bool) (eqf f f') -> (eqf f' f'') -> (eqf f f'').
Proof.
  Unfold eqf. Intros. Rewrite H. Exact (H0 n).
Qed.

Lemma adf_xor_eq : (f,f':nat->bool) (eqf (adf_xor f f') [n:nat] false) -> (eqf f f').
Proof.
  Unfold eqf. Unfold adf_xor. Intros. Apply xorb_eq. Apply H.
Qed.

Lemma ad_xor_eq : (a,a':ad) (ad_xor a a')=ad_z -> a=a'.
Proof.
  Intros. Apply ad_faithful. Apply adf_xor_eq. Apply eqf_trans with f':=(ad_bit (ad_xor a a')).
  Apply eqf_sym. Apply ad_xor_semantics.
  Rewrite H. Unfold eqf. Trivial.
Qed.

Lemma adf_xor_assoc : (f,f',f'':nat->bool)
    (eqf (adf_xor (adf_xor f f') f'') (adf_xor f (adf_xor f' f''))).
Proof.
  Unfold eqf. Unfold adf_xor. Intros. Apply xorb_assoc.
Qed.

Lemma eqf_xor_1 : (f,f',f'',f''':nat->bool) (eqf f f') -> (eqf f'' f''') ->
    (eqf (adf_xor f f'') (adf_xor f' f''')).
Proof.
  Unfold eqf. Intros. Unfold adf_xor. Rewrite H. Rewrite H0. Reflexivity.
Qed.

Lemma ad_xor_assoc :
    (a,a',a'':ad) (ad_xor (ad_xor a a') a'')=(ad_xor a (ad_xor a' a'')).
Proof.
  Intros. Apply ad_faithful.
  Apply eqf_trans with f':=(adf_xor (adf_xor (ad_bit a) (ad_bit a')) (ad_bit a'')).
  Apply eqf_trans with f':=(adf_xor (ad_bit (ad_xor a a')) (ad_bit a'')).
  Apply ad_xor_semantics.
  Apply eqf_xor_1. Apply ad_xor_semantics.
  Apply eqf_refl.
  Apply eqf_trans with f':=(adf_xor (ad_bit a) (adf_xor (ad_bit a') (ad_bit a''))).
  Apply adf_xor_assoc.
  Apply eqf_trans with f':=(adf_xor (ad_bit a) (ad_bit (ad_xor a' a''))).
  Apply eqf_xor_1. Apply eqf_refl.
  Apply eqf_sym. Apply ad_xor_semantics.
  Apply eqf_sym. Apply ad_xor_semantics.
Qed.

Definition ad_double := [a:ad]
  Cases a of
      ad_z => ad_z
    | (ad_x p) => (ad_x (xO p))
  end.

Definition ad_double_plus_un := [a:ad]
  Cases a of
      ad_z => (ad_x xH)
    | (ad_x p) => (ad_x (xI p))
  end.

Definition ad_div_2 := [a:ad]
  Cases a of
      ad_z => ad_z
    | (ad_x xH) => ad_z
    | (ad_x (xO p)) => (ad_x p)
    | (ad_x (xI p)) => (ad_x p)
  end.

Lemma ad_double_div_2 : (a:ad) (ad_div_2 (ad_double a))=a.
Proof.
  NewDestruct a; Trivial.
Qed.

Lemma ad_double_plus_un_div_2 : (a:ad) (ad_div_2 (ad_double_plus_un a))=a.
Proof.
  NewDestruct a; Trivial.
Qed.

Lemma ad_double_inj : (a0,a1:ad) (ad_double a0)=(ad_double a1) -> a0=a1.
Proof.
  Intros. Rewrite <- (ad_double_div_2 a0). Rewrite H. Apply ad_double_div_2.
Qed.

Lemma ad_double_plus_un_inj :
    (a0,a1:ad) (ad_double_plus_un a0)=(ad_double_plus_un a1) -> a0=a1.
Proof.
  Intros. Rewrite <- (ad_double_plus_un_div_2 a0). Rewrite H. Apply ad_double_plus_un_div_2.
Qed.

Definition ad_bit_0 := [a:ad]
  Cases a of
      ad_z => false
    | (ad_x (xO _)) => false
    | _ => true
  end.

Lemma ad_double_bit_0 : (a:ad) (ad_bit_0 (ad_double a))=false.
Proof.
  NewDestruct a; Trivial.
Qed.

Lemma ad_double_plus_un_bit_0 : (a:ad) (ad_bit_0 (ad_double_plus_un a))=true.
Proof.
  NewDestruct a; Trivial.
Qed.

Lemma ad_div_2_double : (a:ad) (ad_bit_0 a)=false -> (ad_double (ad_div_2 a))=a.
Proof.
  NewDestruct a. Trivial. NewDestruct p. Intro H. Discriminate H.
  Intros. Reflexivity.
  Intro H. Discriminate H.
Qed.

Lemma ad_div_2_double_plus_un :
    (a:ad) (ad_bit_0 a)=true -> (ad_double_plus_un (ad_div_2 a))=a.
Proof.
  NewDestruct a. Intro. Discriminate H.
  NewDestruct p. Intros. Reflexivity.
  Intro H. Discriminate H.
  Intro. Reflexivity.
Qed.

Lemma ad_bit_0_correct : (a:ad) (ad_bit a O)=(ad_bit_0 a).
Proof.
  NewDestruct a; Trivial.
  NewDestruct p; Trivial.
Qed.

Lemma ad_div_2_correct : (a:ad) (n:nat) (ad_bit (ad_div_2 a) n)=(ad_bit a (S n)).
Proof.
  NewDestruct a; Trivial.
  NewDestruct p; Trivial.
Qed.

Lemma ad_xor_bit_0 :
    (a,a':ad) (ad_bit_0 (ad_xor a a'))=(xorb (ad_bit_0 a) (ad_bit_0 a')).
Proof.
  Intros. Rewrite <- ad_bit_0_correct. Rewrite (ad_xor_semantics a a' O).
  Unfold adf_xor. Rewrite ad_bit_0_correct. Rewrite ad_bit_0_correct. Reflexivity.
Qed.

Lemma ad_xor_div_2 :
    (a,a':ad) (ad_div_2 (ad_xor a a'))=(ad_xor (ad_div_2 a) (ad_div_2 a')).
Proof.
  Intros. Apply ad_faithful. Unfold eqf. Intro.
  Rewrite (ad_xor_semantics (ad_div_2 a) (ad_div_2 a') n).
  Rewrite ad_div_2_correct.
  Rewrite (ad_xor_semantics a a' (S n)).
  Unfold adf_xor. Rewrite ad_div_2_correct. Rewrite ad_div_2_correct.
  Reflexivity.
Qed.

Lemma ad_neg_bit_0 : (a,a':ad) (ad_bit_0 (ad_xor a a'))=true ->
    (ad_bit_0 a)=(negb (ad_bit_0 a')).
Proof.
  Intros. Rewrite <- true_xorb. Rewrite <- H. Rewrite ad_xor_bit_0.
  Rewrite xorb_assoc. Rewrite xorb_nilpotent. Rewrite xorb_false. Reflexivity.
Qed.

Lemma ad_neg_bit_0_1 :
    (a,a':ad) (ad_xor a a')=(ad_x xH) -> (ad_bit_0 a)=(negb (ad_bit_0 a')).
Proof.
  Intros. Apply ad_neg_bit_0. Rewrite H. Reflexivity.
Qed.

Lemma ad_neg_bit_0_2 : (a,a':ad) (p:positive) (ad_xor a a')=(ad_x (xI p)) ->
    (ad_bit_0 a)=(negb (ad_bit_0 a')).
Proof.
  Intros. Apply ad_neg_bit_0. Rewrite H. Reflexivity.
Qed.

Lemma ad_same_bit_0 : (a,a':ad) (p:positive) (ad_xor a a')=(ad_x (xO p)) ->
    (ad_bit_0 a)=(ad_bit_0 a').
Proof.
  Intros. Rewrite <- (xorb_false (ad_bit_0 a)). Cut (ad_bit_0 (ad_x (xO p)))=false.
  Intro. Rewrite <- H0. Rewrite <- H. Rewrite ad_xor_bit_0. Rewrite <- xorb_assoc.
  Rewrite xorb_nilpotent. Rewrite false_xorb. Reflexivity.
  Reflexivity.
Qed.
