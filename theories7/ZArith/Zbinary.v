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

Require Bvector.
Require ZArith.
Require Export Zpower.
Require Omega.

(*
L'évaluation des vecteurs de booléens se font à la fois en binaire et
en complément à deux. Le nombre appartient à Z. 
On utilise donc Omega pour faire les calculs dans Z.
De plus, on utilise les fonctions 2^n où n est un naturel, ici la longueur.
	two_power_nat = [n:nat](POS (shift_nat n xH))
     		: nat->Z
	two_power_nat_S
	     : (n:nat)`(two_power_nat (S n)) = 2*(two_power_nat n)`
	Z_lt_ge_dec
	     : (x,y:Z){`x < y`}+{`x >= y`}
*)


Section VALUE_OF_BOOLEAN_VECTORS.

(*
Les calculs sont effectués dans la convention positive usuelle.
Les valeurs correspondent soit à l'écriture binaire (nat), 
soit au complément à deux (int).
On effectue le calcul suivant le schéma de Horner.
Le complément à deux n'a de sens que sur les vecteurs de taille 
supérieure ou égale à un, le bit de signe étant évalué négativement.
*)

Definition bit_value [b:bool] : Z :=
Cases b of
	| true => `1`
	| false => `0`
end.

Lemma binary_value  : (n:nat) (Bvector n) -> Z.
Proof.
	Induction n; Intros.
	Exact `0`.

	Inversion H0.
	Exact (Zplus (bit_value a) (Zmult `2` (H H2))).
Defined.

Lemma two_compl_value : (n:nat) (Bvector (S n)) -> Z.
Proof.
	Induction n; Intros.
	Inversion H.
	Exact (Zopp (bit_value a)).

	Inversion H0.
	Exact (Zplus (bit_value a) (Zmult `2` (H H2))).
Defined.

(*
Coq < Eval Compute in (binary_value (3) (Bcons true (2) (Bcons false (1) (Bcons true (0) Bnil)))).
     = `5`
     : Z
*)

(*
Coq < Eval Compute in (two_compl_value (3) (Bcons true (3) (Bcons false (2) (Bcons true (1) (Bcons true (0) Bnil))))).
     = `-3`
     : Z
*)

End VALUE_OF_BOOLEAN_VECTORS.

Section ENCODING_VALUE.

(*
On calcule la valeur binaire selon un schema de Horner.
Le calcul s'arrete à la longueur du vecteur sans vérification.
On definit une fonction Zmod2 calquee sur Zdiv2 mais donnant le quotient
de la division z=2q+r avec 0<=r<=1.
La valeur en complément à deux est calculée selon un schema de Horner
avec Zmod2, le paramètre est la taille moins un.
*)

Definition Zmod2 := [z:Z] Cases z of
  	|  ZERO => `0`
 	| ((POS p)) => Cases p of
      		| (xI q) => (POS q)
    		| (xO q) => (POS q)
    		| xH => `0`
    		end
 	| ((NEG p)) => Cases p of
      		| (xI q) => `(NEG q) - 1`
    		| (xO q) => (NEG q)
    		| xH => `-1`
    		end
 	end.

V7only [
Notation double_moins_un_add_un :=
  [p](sym_eq ? ? ? (double_moins_un_add_un_xI p)).
].

Lemma Zmod2_twice : (z:Z)
	`z = (2*(Zmod2 z) + (bit_value (Zodd_bool z)))`.
Proof.
	NewDestruct z; Simpl.
	Trivial.

	NewDestruct p; Simpl; Trivial.

	NewDestruct p; Simpl.
	NewDestruct p as [p|p|]; Simpl.
	Rewrite <- (double_moins_un_add_un_xI p); Trivial.

	Trivial.

	Trivial.

	Trivial.

	Trivial.
Save.

Lemma Z_to_binary : (n:nat) Z -> (Bvector n).
Proof.
	Induction n; Intros.
	Exact Bnil.

	Exact (Bcons (Zodd_bool H0) n0 (H (Zdiv2 H0))).
Defined.

(*
Eval Compute in (Z_to_binary (5) `5`).
     = (Vcons bool true (4)
          (Vcons bool false (3)
            (Vcons bool true (2)
              (Vcons bool false (1) (Vcons bool false (0) (Vnil bool))))))
     :  (Bvector (5))
*)

Lemma Z_to_two_compl : (n:nat) Z -> (Bvector (S n)).
Proof.
	Induction n; Intros.
	Exact (Bcons (Zodd_bool H) (0) Bnil).

	Exact (Bcons (Zodd_bool H0) (S n0) (H (Zmod2 H0))).
Defined.

(*
Eval Compute in (Z_to_two_compl (3) `0`).
     =  (Vcons bool false (3)
          (Vcons bool false (2)
            (Vcons bool false (1) (Vcons bool false (0) (Vnil bool)))))
     :  (vector bool (4))

Eval Compute in (Z_to_two_compl (3) `5`).
     = (Vcons bool true (3)
          (Vcons bool false (2)
            (Vcons bool true (1) (Vcons bool false (0) (Vnil bool)))))
     :  (vector bool (4))

Eval Compute in (Z_to_two_compl (3) `-5`).
     =  (Vcons bool true (3)
          (Vcons bool true (2)
            (Vcons bool false (1) (Vcons bool true (0) (Vnil bool)))))
     :  (vector bool (4))
*)	

End ENCODING_VALUE.

Section Z_BRIC_A_BRAC.

(*
Bibliotheque de lemmes utiles dans la section suivante.
Utilise largement ZArith.
Meriterait d'etre reecrite.
*)

Lemma binary_value_Sn : (n:nat) (b:bool) (bv : (Bvector n))
	(binary_value (S n) (Vcons bool b n bv))=`(bit_value b) + 2*(binary_value n bv)`.
Proof.
	Intros; Auto.
Save.

Lemma Z_to_binary_Sn : (n:nat) (b:bool) (z:Z)
	`z>=0`->
	(Z_to_binary (S n) `(bit_value b) + 2*z`)=(Bcons b n (Z_to_binary n z)).
Proof.
	NewDestruct b; NewDestruct z; Simpl; Auto.
	Intro H; Elim H; Trivial.
Save.

Lemma binary_value_pos : (n:nat) (bv:(Bvector n))
	`(binary_value n bv) >= 0`.
Proof.
	NewInduction bv as [|a n v IHbv]; Simpl.
	Omega.

	NewDestruct a; NewDestruct (binary_value n v); Simpl; Auto.
	Auto with zarith.
Save.

V7only [Notation add_un_double_moins_un_xO := is_double_moins_un.].

Lemma two_compl_value_Sn : (n:nat) (bv : (Bvector (S n))) (b:bool)
	(two_compl_value (S n) (Bcons b (S n) bv)) =
		`(bit_value b) + 2*(two_compl_value n bv)`.
Proof.
	Intros; Auto.
Save.

Lemma Z_to_two_compl_Sn : (n:nat) (b:bool) (z:Z) 
	(Z_to_two_compl (S n) `(bit_value b) + 2*z`) =
		(Bcons b (S n) (Z_to_two_compl n z)).
Proof.
	NewDestruct b; NewDestruct z as [|p|p]; Auto.
	NewDestruct p as [p|p|]; Auto.
	NewDestruct p as [p|p|]; Simpl; Auto.
	Intros; Rewrite (add_un_double_moins_un_xO p); Trivial.
Save.

Lemma Z_to_binary_Sn_z : (n:nat) (z:Z)
	(Z_to_binary (S n) z)=(Bcons (Zodd_bool z) n (Z_to_binary n (Zdiv2 z))).
Proof.
	Intros; Auto.
Save.

Lemma Z_div2_value : (z:Z)
	` z>=0 `->
	 `(bit_value (Zodd_bool z))+2*(Zdiv2 z) = z`.
Proof.
	NewDestruct z as [|p|p]; Auto.
	NewDestruct p; Auto.
  Intro H; Elim H; Trivial.
Save.

Lemma Zdiv2_pos : (z:Z)
	` z >= 0 ` ->
	`(Zdiv2 z) >= 0 `.
Proof.
	NewDestruct z as [|p|p].
	Auto.

	NewDestruct p; Auto.
	Simpl; Intros; Omega.

  Intro H; Elim H; Trivial.

Save.

Lemma Zdiv2_two_power_nat : (z:Z) (n:nat)
	` z >= 0 ` ->
	` z < (two_power_nat (S n)) ` ->
	`(Zdiv2 z) < (two_power_nat n) `.
Proof.
	Intros.
	Cut (Zlt (Zmult `2` (Zdiv2 z)) (Zmult `2` (two_power_nat n))); Intros.
	Omega.

	Rewrite <- two_power_nat_S.
	NewDestruct (Zeven_odd_dec z); Intros.
	Rewrite <- Zeven_div2; Auto.

	Generalize (Zodd_div2 z H z0); Omega.
Save.

(*

Lemma Z_minus_one_or_zero : (z:Z)
	`z >= -1` ->
	`z < 1` ->
	{`z=-1`} + {`z=0`}.
Proof.
	NewDestruct z; Auto.
	NewDestruct p; Auto.
	Tauto.

	Tauto.

	Intros.
	Right; Omega.

	NewDestruct p.
	Tauto.

	Tauto.

	Intros; Left; Omega.
Save.
*)

Lemma Z_to_two_compl_Sn_z : (n:nat) (z:Z)
	(Z_to_two_compl (S n) z)=(Bcons (Zodd_bool z) (S n) (Z_to_two_compl n (Zmod2 z))).
Proof.
	Intros; Auto.
Save.

Lemma Zeven_bit_value : (z:Z)
	(Zeven z) ->
	`(bit_value (Zodd_bool z))=0`.
Proof.
	NewDestruct z; Unfold bit_value; Auto.
	NewDestruct p; Tauto Orelse (Intro H; Elim H).
 	NewDestruct p; Tauto Orelse (Intro H; Elim H).
Save.

Lemma Zodd_bit_value : (z:Z)
	(Zodd z) ->
	`(bit_value (Zodd_bool z))=1`.
Proof.
	NewDestruct z; Unfold bit_value; Auto.
  Intros; Elim H.
  NewDestruct p; Tauto Orelse (Intros; Elim H).
  NewDestruct p; Tauto Orelse (Intros; Elim H).
Save.

Lemma Zge_minus_two_power_nat_S : (n:nat) (z:Z)
	`z >= (-(two_power_nat (S n)))`->
	`(Zmod2 z) >= (-(two_power_nat n))`.
Proof.
	Intros n z; Rewrite (two_power_nat_S n).
	Generalize (Zmod2_twice z).
	NewDestruct (Zeven_odd_dec z) as [H|H].
	Rewrite (Zeven_bit_value z H); Intros; Omega.

        Rewrite (Zodd_bit_value z H); Intros; Omega.
Save.

Lemma Zlt_two_power_nat_S : (n:nat) (z:Z)
	`z < (two_power_nat (S n))`->
	`(Zmod2 z) < (two_power_nat n)`.
Proof.
	Intros n z; Rewrite (two_power_nat_S n).
	Generalize (Zmod2_twice z).
	NewDestruct (Zeven_odd_dec z) as [H|H].
	Rewrite (Zeven_bit_value z H); Intros; Omega.

	Rewrite (Zodd_bit_value z H); Intros; Omega.
Save.

End Z_BRIC_A_BRAC.

Section COHERENT_VALUE.

(*
On vérifie que dans l'intervalle de définition les fonctions sont 
réciproques l'une de l'autre.
Elles utilisent les lemmes du bric-a-brac.
*)

Lemma binary_to_Z_to_binary : (n:nat) (bv : (Bvector n))
	(Z_to_binary n (binary_value n bv))=bv.
Proof.
	NewInduction bv as [|a n bv IHbv].
	Auto.

	Rewrite binary_value_Sn.
	Rewrite Z_to_binary_Sn.
	Rewrite IHbv; Trivial.

	Apply binary_value_pos.
Save.
		
Lemma two_compl_to_Z_to_two_compl : (n:nat) (bv : (Bvector n)) (b:bool)
	(Z_to_two_compl n (two_compl_value n (Bcons b n bv)))=
		(Bcons b n bv).
Proof.
	NewInduction bv as [|a n bv IHbv]; Intro b.
	NewDestruct b; Auto.

	Rewrite two_compl_value_Sn.
	Rewrite Z_to_two_compl_Sn.
	Rewrite IHbv; Trivial.
Save.

Lemma Z_to_binary_to_Z : (n:nat) (z : Z)
	`z >= 0 `->
	`z < (two_power_nat n) `->
	 (binary_value n (Z_to_binary n z))=z.
Proof.
	NewInduction n as [|n IHn].
	Unfold two_power_nat shift_nat; Simpl; Intros; Omega.

	Intros; Rewrite Z_to_binary_Sn_z.
	Rewrite binary_value_Sn.
	Rewrite IHn.
	Apply Z_div2_value; Auto.

	Apply Zdiv2_pos; Trivial.

	Apply Zdiv2_two_power_nat; Trivial.
Save.

Lemma Z_to_two_compl_to_Z : (n:nat) (z : Z)
	`z >= -(two_power_nat n) `->
	`z < (two_power_nat n) `->
	(two_compl_value n (Z_to_two_compl n  z))=z.
Proof.
	NewInduction n as [|n IHn].
	Unfold two_power_nat shift_nat; Simpl; Intros.
	Assert `z=-1`\/`z=0`. Omega.
Intuition; Subst z; Trivial.

	Intros; Rewrite Z_to_two_compl_Sn_z.
	Rewrite two_compl_value_Sn.
	Rewrite IHn.
	Generalize (Zmod2_twice z); Omega.

	Apply Zge_minus_two_power_nat_S; Auto.

	Apply Zlt_two_power_nat_S; Auto.
Save.

End COHERENT_VALUE.

