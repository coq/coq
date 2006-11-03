(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Bit vectors interpreted as integers. 
    Contribution by Jean Duprat (ENS Lyon). *)

Require Import Bvector.
Require Import ZArith.
Require Export Zpower.
Require Import Omega.

(** L'�valuation des vecteurs de bool�ens se font � la fois en binaire et
    en compl�ment � deux. Le nombre appartient � Z. 
    On utilise donc Omega pour faire les calculs dans Z.
    De plus, on utilise les fonctions 2^n o� n est un naturel, ici la longueur.
	two_power_nat = [n:nat](POS (shift_nat n xH))
     		: nat->Z
	two_power_nat_S
	     : (n:nat)`(two_power_nat (S n)) = 2*(two_power_nat n)`
	Z_lt_ge_dec
	     : (x,y:Z){`x < y`}+{`x >= y`}
*)


Section VALUE_OF_BOOLEAN_VECTORS.

(** Les calculs sont effectu�s dans la convention positive usuelle.
    Les valeurs correspondent soit � l'�criture binaire (nat), 
    soit au compl�ment � deux (int).
    On effectue le calcul suivant le sch�ma de Horner.
    Le compl�ment � deux n'a de sens que sur les vecteurs de taille 
    sup�rieure ou �gale � un, le bit de signe �tant �valu� n�gativement.
*)

  Definition bit_value (b:bool) : Z :=
    match b with
      | true => 1%Z
      | false => 0%Z
    end.
  
  Lemma binary_value : forall n:nat, Bvector n -> Z.
  Proof.
    simple induction n; intros.
    exact 0%Z.
    
    inversion H0.
    exact (bit_value a + 2 * H H2)%Z.
  Defined.

  Lemma two_compl_value : forall n:nat, Bvector (S n) -> Z.
  Proof.
    simple induction n; intros.
    inversion H.
    exact (- bit_value a)%Z.

    inversion H0.
    exact (bit_value a + 2 * H H2)%Z.
  Defined.

End VALUE_OF_BOOLEAN_VECTORS.

Section ENCODING_VALUE.

(** On calcule la valeur binaire selon un schema de Horner.
    Le calcul s'arrete � la longueur du vecteur sans v�rification.
    On definit une fonction Zmod2 calquee sur Zdiv2 mais donnant le quotient
    de la division z=2q+r avec 0<=r<=1.
    La valeur en compl�ment � deux est calcul�e selon un schema de Horner
    avec Zmod2, le param�tre est la taille moins un.
*)

  Definition Zmod2 (z:Z) :=
    match z with
      | Z0 => 0%Z
      | Zpos p => match p with
		    | xI q => Zpos q
		    | xO q => Zpos q
		    | xH => 0%Z
		  end
      | Zneg p =>
	match p with
	  | xI q => (Zneg q - 1)%Z
	  | xO q => Zneg q
	  | xH => (-1)%Z
	end
    end.


  Lemma Zmod2_twice :
    forall z:Z, z = (2 * Zmod2 z + bit_value (Zeven.Zodd_bool z))%Z.
  Proof.
    destruct z; simpl in |- *.
    trivial.
    
    destruct p; simpl in |- *; trivial.
    
    destruct p; simpl in |- *.
    destruct p as [p| p| ]; simpl in |- *.
    rewrite <- (Pdouble_minus_one_o_succ_eq_xI p); trivial.

    trivial.
    
    trivial.
    
    trivial.
    
    trivial.
  Qed.

  Lemma Z_to_binary : forall n:nat, Z -> Bvector n.
  Proof.
    simple induction n; intros.
    exact Bnil.
    
    exact (Bcons (Zeven.Zodd_bool H0) n0 (H (Zeven.Zdiv2 H0))).
  Defined.

  Lemma Z_to_two_compl : forall n:nat, Z -> Bvector (S n).
  Proof.
    simple induction n; intros.
    exact (Bcons (Zeven.Zodd_bool H) 0 Bnil).
    
    exact (Bcons (Zeven.Zodd_bool H0) (S n0) (H (Zmod2 H0))).
  Defined.

End ENCODING_VALUE.

Section Z_BRIC_A_BRAC.

  (** Bibliotheque de lemmes utiles dans la section suivante.
      Utilise largement ZArith.
      M�riterait d'�tre r�crite.
  *)

  Lemma binary_value_Sn :
    forall (n:nat) (b:bool) (bv:Bvector n),
      binary_value (S n) (Vcons bool b n bv) =
      (bit_value b + 2 * binary_value n bv)%Z.
  Proof.
    intros; auto.
  Qed.

  Lemma Z_to_binary_Sn :
    forall (n:nat) (b:bool) (z:Z),
      (z >= 0)%Z ->
      Z_to_binary (S n) (bit_value b + 2 * z) = Bcons b n (Z_to_binary n z).
  Proof.
    destruct b; destruct z; simpl in |- *; auto.
    intro H; elim H; trivial.
  Qed.

  Lemma binary_value_pos :
    forall (n:nat) (bv:Bvector n), (binary_value n bv >= 0)%Z.
  Proof.
    induction bv as [| a n v IHbv]; simpl in |- *.
    omega.

    destruct a; destruct (binary_value n v); simpl in |- *; auto.
    auto with zarith.
  Qed.

  Lemma two_compl_value_Sn :
    forall (n:nat) (bv:Bvector (S n)) (b:bool),
      two_compl_value (S n) (Bcons b (S n) bv) =
      (bit_value b + 2 * two_compl_value n bv)%Z.
  Proof.
    intros; auto.
  Qed.

  Lemma Z_to_two_compl_Sn :
    forall (n:nat) (b:bool) (z:Z),
      Z_to_two_compl (S n) (bit_value b + 2 * z) =
      Bcons b (S n) (Z_to_two_compl n z).
  Proof.
    destruct b; destruct z as [| p| p]; auto.
    destruct p as [p| p| ]; auto.
    destruct p as [p| p| ]; simpl in |- *; auto.
    intros; rewrite (Psucc_o_double_minus_one_eq_xO p); trivial.
  Qed.

  Lemma Z_to_binary_Sn_z :
    forall (n:nat) (z:Z),
      Z_to_binary (S n) z =
      Bcons (Zeven.Zodd_bool z) n (Z_to_binary n (Zeven.Zdiv2 z)).
  Proof.
    intros; auto.
  Qed.

  Lemma Z_div2_value :
    forall z:Z,
      (z >= 0)%Z -> (bit_value (Zeven.Zodd_bool z) + 2 * Zeven.Zdiv2 z)%Z = z.
  Proof.
    destruct z as [| p| p]; auto.
    destruct p; auto.
    intro H; elim H; trivial.
  Qed.

  Lemma Pdiv2 : forall z:Z, (z >= 0)%Z -> (Zeven.Zdiv2 z >= 0)%Z.
  Proof.
    destruct z as [| p| p].
    auto.
    
    destruct p; auto.
    simpl in |- *; intros; omega.
    
    intro H; elim H; trivial.
  Qed.

  Lemma Zdiv2_two_power_nat :
    forall (z:Z) (n:nat),
      (z >= 0)%Z ->
      (z < two_power_nat (S n))%Z -> (Zeven.Zdiv2 z < two_power_nat n)%Z.
  Proof.
    intros.
    cut (2 * Zeven.Zdiv2 z < 2 * two_power_nat n)%Z; intros.
    omega.
    
    rewrite <- two_power_nat_S.
    destruct (Zeven.Zeven_odd_dec z); intros.
    rewrite <- Zeven.Zeven_div2; auto.
    
    generalize (Zeven.Zodd_div2 z H z0); omega.
  Qed.

  Lemma Z_to_two_compl_Sn_z :
    forall (n:nat) (z:Z),
      Z_to_two_compl (S n) z =
      Bcons (Zeven.Zodd_bool z) (S n) (Z_to_two_compl n (Zmod2 z)).
  Proof.
    intros; auto.
  Qed.
  
  Lemma Zeven_bit_value :
    forall z:Z, Zeven.Zeven z -> bit_value (Zeven.Zodd_bool z) = 0%Z.
  Proof.
    destruct z; unfold bit_value in |- *; auto.
    destruct p; tauto || (intro H; elim H).
    destruct p; tauto || (intro H; elim H).
  Qed.
  
  Lemma Zodd_bit_value :
    forall z:Z, Zeven.Zodd z -> bit_value (Zeven.Zodd_bool z) = 1%Z.
  Proof.
    destruct z; unfold bit_value in |- *; auto.
    intros; elim H.
    destruct p; tauto || (intros; elim H).
    destruct p; tauto || (intros; elim H).
  Qed.
  
  Lemma Zge_minus_two_power_nat_S :
    forall (n:nat) (z:Z),
      (z >= - two_power_nat (S n))%Z -> (Zmod2 z >= - two_power_nat n)%Z.
  Proof.
    intros n z; rewrite (two_power_nat_S n).
    generalize (Zmod2_twice z).
    destruct (Zeven.Zeven_odd_dec z) as [H| H].
    rewrite (Zeven_bit_value z H); intros; omega.

    rewrite (Zodd_bit_value z H); intros; omega.
  Qed.
  
  Lemma Zlt_two_power_nat_S :
    forall (n:nat) (z:Z),
      (z < two_power_nat (S n))%Z -> (Zmod2 z < two_power_nat n)%Z.
  Proof.
    intros n z; rewrite (two_power_nat_S n).
    generalize (Zmod2_twice z).
    destruct (Zeven.Zeven_odd_dec z) as [H| H].
    rewrite (Zeven_bit_value z H); intros; omega.

    rewrite (Zodd_bit_value z H); intros; omega.
  Qed.

End Z_BRIC_A_BRAC.

Section COHERENT_VALUE.

(** On v�rifie que dans l'intervalle de d�finition les fonctions sont 
    r�ciproques l'une de l'autre. Elles utilisent les lemmes du bric-a-brac.
*)

  Lemma binary_to_Z_to_binary :
    forall (n:nat) (bv:Bvector n), Z_to_binary n (binary_value n bv) = bv.
  Proof.
    induction bv as [| a n bv IHbv].
    auto.
    
    rewrite binary_value_Sn.
    rewrite Z_to_binary_Sn.
    rewrite IHbv; trivial.
    
    apply binary_value_pos.
  Qed.
  
  Lemma two_compl_to_Z_to_two_compl :
    forall (n:nat) (bv:Bvector n) (b:bool),
      Z_to_two_compl n (two_compl_value n (Bcons b n bv)) = Bcons b n bv.
  Proof.
    induction bv as [| a n bv IHbv]; intro b.
    destruct b; auto.
    
    rewrite two_compl_value_Sn.
    rewrite Z_to_two_compl_Sn.
    rewrite IHbv; trivial.
  Qed.
  
  Lemma Z_to_binary_to_Z :
    forall (n:nat) (z:Z),
      (z >= 0)%Z ->
      (z < two_power_nat n)%Z -> binary_value n (Z_to_binary n z) = z.
  Proof.
    induction n as [| n IHn].
    unfold two_power_nat, shift_nat in |- *; simpl in |- *; intros; omega.
    
    intros; rewrite Z_to_binary_Sn_z.
    rewrite binary_value_Sn.
    rewrite IHn.
    apply Z_div2_value; auto.
    
    apply Pdiv2; trivial.
    
    apply Zdiv2_two_power_nat; trivial.
  Qed.
  
  Lemma Z_to_two_compl_to_Z :
    forall (n:nat) (z:Z),
      (z >= - two_power_nat n)%Z ->
      (z < two_power_nat n)%Z -> two_compl_value n (Z_to_two_compl n z) = z.
  Proof.
    induction n as [| n IHn].
    unfold two_power_nat, shift_nat in |- *; simpl in |- *; intros.
    assert (z = (-1)%Z \/ z = 0%Z). omega.
    intuition; subst z; trivial.

    intros; rewrite Z_to_two_compl_Sn_z.
    rewrite two_compl_value_Sn.
    rewrite IHn.
    generalize (Zmod2_twice z); omega.

    apply Zge_minus_two_power_nat_S; auto.
    
    apply Zlt_two_power_nat_S; auto.
  Qed.

End COHERENT_VALUE.
