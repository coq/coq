(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require fast_integer.
Require zarith_aux.
Require auxiliary.
Require Zsyntax.
Require Bool.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(** Overview of the sections of this file:
    - logic: Logic complements.
    - numbers: a few very simple lemmas for manipulating the
      constructors [POS], [NEG], [ZERO] and [xI], [xO], [xH]
    - registers: defining arrays of bits and their relation with integers.
    - iter: the n-th iterate of a function is defined for [n:nat] and 
      [n:positive].
      The two notions are identified and an invariant conservation theorem
      is proved.
    - recursors: Here a nat-like recursor is built.
    - arith: lemmas about [< <= ?= + *]
*)

Section logic.

Lemma rename : (A:Set)(P:A->Prop)(x:A) ((y:A)(x=y)->(P y)) -> (P x).
Auto with arith. 
Qed.

End logic.

Section numbers.

Definition entier_of_Z :=
  [z:Z]Cases z of ZERO => Nul | (POS p) => (Pos p) | (NEG p) => (Pos p) end.
Definition Z_of_entier :=
  [x:entier]Cases x of Nul => ZERO | (Pos p) => (POS p) end.
 
(* Coercion Z_of_entier : entier >-> Z. *)

Lemma POS_xI : (p:positive) (POS (xI p))=`2*(POS p) + 1`.
Intro; Apply refl_equal.
Qed.
Lemma POS_xO : (p:positive) (POS (xO p))=`2*(POS p)`.
Intro; Apply refl_equal.
Qed.
Lemma NEG_xI : (p:positive) (NEG (xI p))=`2*(NEG p) - 1`.
Intro; Apply refl_equal.
Qed.
Lemma NEG_xO : (p:positive) (NEG (xO p))=`2*(NEG p)`.
Intro; Apply refl_equal.
Qed.

Lemma POS_add : (p,p':positive)`(POS (add p p'))=(POS p)+(POS p')`.
Induction p; Induction p'; Simpl; Auto with arith.
Qed.

Lemma NEG_add : (p,p':positive)`(NEG (add p p'))=(NEG p)+(NEG p')`.
Induction p; Induction p'; Simpl; Auto with arith.
Qed.

(** Boolean comparisons *)

Definition Zle_bool := 
  [x,y:Z]Cases `x ?= y` of SUPERIEUR => false | _ => true end.
Definition Zge_bool := 
  [x,y:Z]Cases `x ?= y` of INFERIEUR => false | _ => true end.
Definition Zlt_bool := 
  [x,y:Z]Cases `x ?= y` of INFERIEUR => true | _ => false end.
Definition Zgt_bool := 
  [x,y:Z]Cases ` x ?= y` of SUPERIEUR => true | _ => false end.
Definition Zeq_bool := 
  [x,y:Z]Cases `x ?= y` of EGAL => true | _ => false end.
Definition Zneq_bool := 
  [x,y:Z]Cases `x ?= y` of EGAL => false | _ => true end.

Lemma Zle_cases : (x,y:Z)if (Zle_bool x y) then `x<=y` else `x>y`.
Proof.
Intros x y; Unfold Zle_bool Zle Zgt.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zlt_cases : (x,y:Z)if (Zlt_bool x y) then `x<y` else `x>=y`.
Proof.
Intros x y; Unfold Zlt_bool Zlt Zge.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zge_cases : (x,y:Z)if (Zge_bool x y) then `x>=y` else `x<y`.
Proof.
Intros x y; Unfold Zge_bool Zge Zlt.
Case (Zcompare x y); Auto; Discriminate.
Qed.

Lemma Zgt_cases : (x,y:Z)if (Zgt_bool x y) then `x>y` else `x<=y`.
Proof.
Intros x y; Unfold Zgt_bool Zgt Zle.
Case (Zcompare x y); Auto; Discriminate.
Qed.

End numbers.

Section iterate.

(** [n]th iteration of the function [f] *)
Fixpoint iter_nat[n:nat]  : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
      O => x
    | (S n') => (f (iter_nat n' A f x))
    end.

Fixpoint iter_pos[n:positive] : (A:Set)(f:A->A)A->A :=
  [A:Set][f:A->A][x:A]
    Cases n of
     	xH => (f x)
      | (xO n') => (iter_pos n' A f (iter_pos n' A f x))
      | (xI n') => (f (iter_pos n' A f (iter_pos n' A f x)))
    end.

Definition iter :=
  [n:Z][A:Set][f:A->A][x:A]Cases n of
    ZERO => x
  | (POS p) => (iter_pos p A f x)
  | (NEG p) => x
  end.

Theorem iter_nat_plus :
  (n,m:nat)(A:Set)(f:A->A)(x:A)
    (iter_nat (plus n m) A f x)=(iter_nat n A f (iter_nat m A f x)).
    
Induction n;
[ Simpl; Auto with arith
| Intros; Simpl; Apply f_equal with f:=f; Apply H
].  
Qed.

Theorem iter_convert : (n:positive)(A:Set)(f:A->A)(x:A)
  (iter_pos n A f x) = (iter_nat (convert n) A f x).

Induction n;
[ Intros; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry; Apply f_equal with f:=f;
  Apply iter_nat_plus
| Intros; Unfold convert; Simpl; Rewrite -> (H A f x);
  Rewrite -> (H A f (iter_nat (convert p) A f x));
  Rewrite -> (ZL6 p); Symmetry;
  Apply iter_nat_plus
| Simpl; Auto with arith
].
Qed.

Theorem iter_pos_add :
  (n,m:positive)(A:Set)(f:A->A)(x:A)
    (iter_pos (add n m) A f x)=(iter_pos n A f (iter_pos m A f x)).

Intros.
Rewrite -> (iter_convert m A f x).
Rewrite -> (iter_convert n A f (iter_nat (convert m) A f x)).
Rewrite -> (iter_convert (add n m) A f x).
Rewrite -> (convert_add n m).
Apply iter_nat_plus.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv], 
    then the iterates of [f] also preserve it. *)

Theorem iter_nat_invariant :
  (n:nat)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_nat n A f x)).
Induction n; Intros;
[ Trivial with arith
| Simpl; Apply H0 with x:=(iter_nat n0 A f x); Apply H; Trivial with arith].
Qed.

Theorem iter_pos_invariant :
  (n:positive)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_pos n A f x)).
Intros; Rewrite iter_convert; Apply iter_nat_invariant; Trivial with arith.
Qed.

End iterate.


Section arith.

Lemma POS_gt_ZERO : (p:positive) `(POS p) > 0`.
Unfold Zgt; Trivial.
Qed.

(* weaker but useful (in [Zpower] for instance) *)
Lemma ZERO_le_POS : (p:positive) `0 <= (POS p)`.
Intro; Unfold Zle; Unfold Zcompare; Discriminate.
Qed.

Lemma Zlt_ZERO_pred_le_ZERO : (x:Z) `0 < x` -> `0 <= (Zpred x)`.
Intros.
Rewrite (Zs_pred x) in H.
Apply Zgt_S_le.
Apply Zlt_gt.
Assumption.
Qed.

Lemma NEG_lt_ZERO : (p:positive)`(NEG p) < 0`.
Unfold Zlt; Trivial.
Qed.


(** [Zeven], [Zodd], [Zdiv2] and their related properties *)

Definition Zeven := 
  [z:Z]Cases z of ZERO => True
                | (POS (xO _)) => True
		| (NEG (xO _)) => True
		| _ => False
               end.

Definition Zodd := 
  [z:Z]Cases z of (POS xH) => True
                | (NEG xH) => True
                | (POS (xI _)) => True
		| (NEG (xI _)) => True
		| _ => False
               end.

Definition Zeven_bool :=
  [z:Z]Cases z of ZERO => true
                | (POS (xO _)) => true
		| (NEG (xO _)) => true
		| _ => false
               end.

Definition Zodd_bool := 
  [z:Z]Cases z of ZERO => false
                | (POS (xO _)) => false
		| (NEG (xO _)) => false
		| _ => true
               end.

Definition Zeven_odd_dec : (z:Z) { (Zeven z) }+{ (Zodd z) }.
Proof.
  Intro z. Case z;
  [ Left; Compute; Trivial
  | Intro p; Case p; Intros; 
    (Right; Compute; Exact I) Orelse (Left; Compute; Exact I)
  | Intro p; Case p; Intros; 
    (Right; Compute; Exact I) Orelse (Left; Compute; Exact I) ].
  (*i was 
  Realizer Zeven_bool.
  Repeat Program; Compute; Trivial.
  i*)
Defined.

Definition Zeven_dec : (z:Z) { (Zeven z) }+{ ~(Zeven z) }.
Proof.
  Intro z. Case z;
  [ Left; Compute; Trivial
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) 
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) ].
  (*i was 
  Realizer Zeven_bool.
  Repeat Program; Compute; Trivial.
  i*)
Defined.

Definition Zodd_dec : (z:Z) { (Zodd z) }+{ ~(Zodd z) }.
Proof.
  Intro z. Case z;
  [ Right; Compute; Trivial
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) 
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) ].
  (*i was 
  Realizer Zodd_bool.
  Repeat Program; Compute; Trivial.
  i*)
Defined.

Lemma Zeven_not_Zodd : (z:Z)(Zeven z) -> ~(Zodd z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Lemma Zodd_not_Zeven : (z:Z)(Zodd z) -> ~(Zeven z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Hints Unfold Zeven Zodd : zarith.

(** [Zdiv2] is defined on all [Z], but notice that for odd negative integers
    it is not the euclidean quotient: in that case we have [n = 2*(n/2)-1] *)

Definition Zdiv2_pos :=
  [z:positive]Cases z of xH => xH
                       | (xO p) => p
		       | (xI p) => p
		      end.

Definition Zdiv2 :=
  [z:Z]Cases z of ZERO => ZERO
                | (POS xH) => ZERO
                | (POS p) => (POS (Zdiv2_pos p))
		| (NEG xH) => ZERO
		| (NEG p) => (NEG (Zdiv2_pos p))
	       end.

Lemma Zeven_div2 : (x:Z) (Zeven x) -> `x = 2*(Zdiv2 x)`.
Proof.
NewDestruct x.
Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zeven (POS (xI p))); Red; Auto with arith.
Intros. Absurd (Zeven `1`); Red; Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zeven (NEG (xI p))); Red; Auto with arith.
Intros. Absurd (Zeven `-1`); Red; Auto with arith.
Qed.

Lemma Zodd_div2 : (x:Z) `x >= 0` -> (Zodd x) -> `x = 2*(Zdiv2 x)+1`.
Proof.
NewDestruct x.
Intros. Absurd (Zodd `0`); Red; Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zodd (POS (xO p))); Red; Auto with arith.
Intros. Absurd `(NEG p) >= 0`; Red; Auto with arith.
Qed.

Lemma Z_modulo_2 : (x:Z) `x >= 0` -> { y:Z | `x=2*y` }+{ y:Z | `x=2*y+1` }.
Proof.
Intros x Hx.
Elim (Zeven_odd_dec x); Intro.
Left. Split with (Zdiv2 x). Exact (Zeven_div2 x a).
Right. Split with (Zdiv2 x). Exact (Zodd_div2 x Hx b).
Qed.

(* Very simple *)
Lemma Zminus_Zplus_compatible :
  (x,y,n:Z) `(x+n) - (y+n) = x - y`.
Intros.
Unfold Zminus.
Rewrite -> Zopp_Zplus.
Rewrite -> (Zplus_sym (Zopp y) (Zopp n)).
Rewrite -> Zplus_assoc.
Rewrite <- (Zplus_assoc x n (Zopp n)).
Rewrite -> (Zplus_inverse_r n).
Rewrite <- Zplus_n_O.
Reflexivity.
Qed.

(** Decompose an egality between two [?=] relations into 3 implications *)
Theorem Zcompare_egal_dec :
   (x1,y1,x2,y2:Z)
    (`x1 < y1`->`x2 < y2`)
     ->(`x1 ?= y1`=EGAL -> `x2 ?= y2`=EGAL)
        ->(`x1 > y1`->`x2 > y2`)->`x1 ?= y1`=`x2 ?= y2`.
Intros x1 y1 x2 y2.
Unfold Zgt; Unfold Zlt;
Case `x1 ?= y1`; Case `x2 ?= y2`; Auto with arith; Symmetry; Auto with arith.
Qed.

Theorem Zcompare_elim :
  (c1,c2,c3:Prop)(x,y:Z)
    ((x=y) -> c1) ->(`x < y` -> c2) ->(`x > y`-> c3)
       -> Cases `x ?= y`of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.

Intros.
Apply rename with x:=`x ?= y`; Intro r; Elim r;
[ Intro; Apply H; Apply (let (h1, h2)=(Zcompare_EGAL x y) in h1); Assumption
| Unfold Zlt in H0; Assumption
| Unfold Zgt in H1; Assumption ].
Qed.

Lemma Zcompare_x_x : (x:Z) `x ?= x` = EGAL.
Intro; Apply let (h1,h2) = (Zcompare_EGAL x x) in h2.
Apply refl_equal.
Qed.

Lemma Zlt_not_eq : (x,y:Z)`x < y` -> ~x=y.
Proof.
Intros.
Unfold Zlt in H.
Unfold not.
Intro.
Generalize (proj2 ? ? (Zcompare_EGAL x y) H0).
Intro.
Rewrite H1 in H.
Discriminate H.
Qed.

Lemma Zcompare_eq_case : 
  (c1,c2,c3:Prop)(x,y:Z) c1 -> x=y ->
  Cases `x ?= y` of EGAL => c1 | INFERIEUR => c2 | SUPERIEUR => c3 end.
Intros.
Rewrite -> (Case (Zcompare_EGAL x y) of [h1,h2: ?]h2 end H0).
Assumption.
Qed.

(** Four very basic lemmas about [Zle], [Zlt], [Zge], [Zgt] *)
Lemma Zle_Zcompare :
  (x,y:Z)`x <= y` ->
  Cases `x ?= y` of EGAL => True | INFERIEUR => True | SUPERIEUR => False end.
Intros x y; Unfold Zle; Elim `x ?=y`; Auto with arith.
Qed.

Lemma Zlt_Zcompare :
  (x,y:Z)`x < y`  ->
  Cases `x ?= y` of EGAL => False | INFERIEUR => True | SUPERIEUR => False end.
Intros x y; Unfold Zlt; Elim `x ?=y`; Intros; Discriminate Orelse Trivial with arith.
Qed.

Lemma Zge_Zcompare :
  (x,y:Z)` x >= y`->
  Cases `x ?= y` of EGAL => True | INFERIEUR => False | SUPERIEUR => True end.
Intros x y; Unfold Zge; Elim `x ?=y`; Auto with arith. 
Qed.

Lemma Zgt_Zcompare :
  (x,y:Z)`x > y` ->
  Cases `x ?= y` of EGAL => False | INFERIEUR => False | SUPERIEUR => True end.
Intros x y; Unfold Zgt; Elim `x ?= y`; Intros; Discriminate Orelse Trivial with arith.
Qed.

(** Lemmas about [Zmin] *)

Lemma Zmin_plus : (x,y,n:Z) `(Zmin (x+n)(y+n))=(Zmin x y)+n`.
Intros; Unfold Zmin.
Rewrite (Zplus_sym x n);
Rewrite (Zplus_sym y n);
Rewrite (Zcompare_Zplus_compatible x y n).
Case `x ?= y`; Apply Zplus_sym.
Qed.

(** Lemmas about [absolu] *)

Lemma absolu_lt : (x,y:Z) `0 <= x < y` -> (lt (absolu x) (absolu y)).
Proof.
Intros x y. Case x; Simpl. Case y; Simpl.

Intro. Absurd `0 < 0`. Compute. Intro H0. Discriminate H0. Intuition.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.

Case y; Simpl.
Intros. Absurd `(POS p) < 0`. Compute. Intro H0. Discriminate H0. Intuition.
Intros. Change (gt (convert p) (convert p0)).
Apply compare_convert_SUPERIEUR.
Elim H; Auto with arith. Intro. Exact (ZC2 p0 p).

Intros. Absurd `(POS p0) < (NEG p)`.
Compute. Intro H0. Discriminate H0. Intuition.

Intros. Absurd `0 <= (NEG p)`. Compute. Auto with arith. Intuition.
Qed.

(** Lemmas on [Zle_bool] used in contrib/graphs *)

Lemma Zle_bool_imp_le : (x,y:Z) (Zle_bool x y)=true -> (Zle x y).
Proof.
  Unfold Zle_bool Zle. Intros x y. Unfold not. 
  Case (Zcompare x y); Intros; Discriminate.
Qed.

Lemma Zle_imp_le_bool : (x,y:Z) (Zle x y) -> (Zle_bool x y)=true.
Proof.
  Unfold Zle Zle_bool. Intros x y. Case (Zcompare x y); Trivial. Intro. Elim (H (refl_equal ? ?)).
Qed.

Lemma Zle_bool_refl : (x:Z) (Zle_bool x x)=true.
Proof.
  Intro. Apply Zle_imp_le_bool. Apply Zle_refl. Reflexivity.
Qed.

Lemma Zle_bool_antisym : (x,y:Z) (Zle_bool x y)=true -> (Zle_bool y x)=true -> x=y.
Proof.
  Intros. Apply Zle_antisym. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Lemma Zle_bool_trans : (x,y,z:Z) (Zle_bool x y)=true -> (Zle_bool y z)=true -> (Zle_bool x z)=true.
Proof.
  Intros. Apply Zle_imp_le_bool. Apply Zle_trans with m:=y. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Definition Zle_bool_total : (x,y:Z) {(Zle_bool x y)=true}+{(Zle_bool y x)=true}.
Proof.
  Intros. Unfold Zle_bool. Cut (Zcompare x y)=SUPERIEUR<->(Zcompare y x)=INFERIEUR.
  Case (Zcompare x y). Left . Reflexivity.
  Left . Reflexivity.
  Right . Rewrite (proj1 ? ? H (refl_equal ? ?)). Reflexivity.
  Apply Zcompare_ANTISYM.
Defined.

Lemma Zle_bool_plus_mono : (x,y,z,t:Z) (Zle_bool x y)=true -> (Zle_bool z t)=true ->
                                (Zle_bool (Zplus x z) (Zplus y t))=true.
Proof.
  Intros. Apply Zle_imp_le_bool. Apply Zle_plus_plus. Apply Zle_bool_imp_le. Assumption.
  Apply Zle_bool_imp_le. Assumption.
Qed.

Lemma Zone_pos : (Zle_bool `1` `0`)=false.
Proof.
  Reflexivity.
Qed.

Lemma Zone_min_pos : (x:Z) (Zle_bool x `0`)=false -> (Zle_bool `1` x)=true.
Proof.
  Intros. Apply Zle_imp_le_bool. Change (Zle (Zs ZERO) x). Apply Zgt_le_S. Generalize H.
  Unfold Zle_bool Zgt. Case (Zcompare x ZERO). Intro H0. Discriminate H0.
  Intro H0. Discriminate H0.
  Reflexivity.
Qed.


 Lemma Zle_is_le_bool : (x,y:Z) (Zle x y) <-> (Zle_bool x y)=true.
  Proof.
    Intros. Split. Intro. Apply Zle_imp_le_bool. Assumption.
    Intro. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zge_is_le_bool : (x,y:Z) (Zge x y) <-> (Zle_bool y x)=true.
  Proof.
    Intros. Split. Intro. Apply Zle_imp_le_bool. Apply Zge_le. Assumption.
    Intro. Apply Zle_ge. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zlt_is_le_bool : (x,y:Z) (Zlt x y) <-> (Zle_bool x `y-1`)=true.
  Proof.
    Intros. Split. Intro. Apply Zle_imp_le_bool. Apply Zlt_n_Sm_le. Rewrite (Zs_pred y) in H.
    Assumption.
    Intro. Rewrite (Zs_pred y). Apply Zle_lt_n_Sm. Apply Zle_bool_imp_le. Assumption.
  Qed.

  Lemma Zgt_is_le_bool : (x,y:Z) (Zgt x y) <-> (Zle_bool y `x-1`)=true.
  Proof.
    Intros. Apply iff_trans with b:=`y < x`. Split. Exact (Zgt_lt x y).
    Exact (Zlt_gt y x).
    Exact (Zlt_is_le_bool y x).
  Qed.

End arith.

(** Equivalence between inequalities used in contrib/graph *)


  Lemma Zle_plus_swap : (x,y,z:Z) `x+z<=y` <-> `x<=y-z`.
  Proof.
    Intros. Split. Intro. Rewrite <- (Zero_right x). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_l. Exact (Zle_reg_r ? ? ? H).
    Intro. Rewrite <- (Zero_right y). Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_l.
    Apply Zle_reg_r. Assumption.
  Qed.

  Lemma Zge_iff_le : (x,y:Z) `x>=y` <-> `y<=x`.
  Proof.
    Intros. Split. Intro. Apply Zge_le. Assumption.
    Intro. Apply Zle_ge. Assumption.
  Qed.

  Lemma Zlt_plus_swap : (x,y,z:Z) `x+z<y` <-> `x<y-z`.
  Proof.
    Intros. Split. Intro. Unfold Zminus. Rewrite Zplus_sym. Rewrite <- (Zero_left x).
    Rewrite <- (Zplus_inverse_l z). Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym.
    Assumption.
    Intro. Rewrite Zplus_sym. Rewrite <- (Zero_left y). Rewrite <- (Zplus_inverse_r z).
    Rewrite Zplus_assoc_r. Apply Zlt_reg_l. Rewrite Zplus_sym. Assumption.
  Qed.

  Lemma Zgt_iff_lt : (x,y:Z) `x>y` <-> `y<x`.
  Proof.
    Intros. Split. Intro. Apply Zgt_lt. Assumption.
    Intro. Apply Zlt_gt. Assumption.
  Qed.

  Lemma Zeq_plus_swap : (x,y,z:Z) `x+z=y` <-> `x=y-z`.
  Proof.
    Intros. Split. Intro. Rewrite <- H. Unfold Zminus. Rewrite Zplus_assoc_r.
    Rewrite Zplus_inverse_r. Apply sym_eq. Apply Zero_right.
    Intro. Rewrite H. Unfold Zminus. Rewrite Zplus_assoc_r. Rewrite Zplus_inverse_l.
    Apply Zero_right.
  Qed.
