(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(********************************************************)
(* Module Zmisc.v :           				*)
(* Definitions et lemmes complementaires		*)
(* Division euclidienne					*)
(* Patrick Loiseleur, avril 1997			*)
(********************************************************)

Require fast_integer.
Require zarith_aux.
Require auxiliary.
Require Zsyntax.
Require Bool.

(************************************************************************)
(*
 Overview of the sections of this file :
 \begin{itemize}
 \item logic : Logic complements.
 \item numbers : a few very simple lemmas for manipulating the
   constructors [POS], [NEG], [ZERO] and [xI], [xO], [xH]
 \item registers : defining arrays of bits and their relation with integers.
 \item iter : the n-th iterate of a function is defined for n:nat and 
   n:positive.
   
   The two notions are identified and an invariant conservation theorem
   is proved.
 \item recursors : Here a nat-like recursor is built.
 \item arith : lemmas about [< <= ?= + *] ...
 \end{itemize}
*)
(************************************************************************)

Section logic.

Lemma rename : (A:Set)(P:A->Prop)(x:A) ((y:A)(x=y)->(P y)) -> (P x).
Auto with arith. 
Save.

End logic.

Section numbers.

Definition entier_of_Z := [z:Z]Case z of Nul Pos Pos end.
Definition Z_of_entier := [x:entier]Case x of ZERO POS end.
 
(*i Coercion Z_of_entier : entier >-> Z. i*)

Lemma POS_xI : (p:positive) (POS (xI p))=`2*(POS p) + 1`.
Intro; Apply refl_equal.
Save.
Lemma POS_xO : (p:positive) (POS (xO p))=`2*(POS p)`.
Intro; Apply refl_equal.
Save.
Lemma NEG_xI : (p:positive) (NEG (xI p))=`2*(NEG p) - 1`.
Intro; Apply refl_equal.
Save.
Lemma NEG_xO : (p:positive) (NEG (xO p))=`2*(NEG p)`.
Intro; Apply refl_equal.
Save.

Lemma POS_add : (p,p':positive)`(POS (add p p'))=(POS p)+(POS p')`.
Induction p; Induction p'; Simpl; Auto with arith.
Save.

Lemma NEG_add : (p,p':positive)`(NEG (add p p'))=(NEG p)+(NEG p')`.
Induction p; Induction p'; Simpl; Auto with arith.
Save.

Definition Zle_bool := [x,y:Z]Case `x ?= y` of true true false end.
Definition Zge_bool := [x,y:Z]Case `x ?= y` of true false true end.
Definition Zlt_bool := [x,y:Z]Case `x ?= y` of false true false end.
Definition Zgt_bool := [x,y:Z]Case ` x ?= y` of false false true end.
Definition Zeq_bool := [x,y:Z]Cases `x ?= y` of EGAL => true | _ => false end.
Definition Zneq_bool := [x,y:Z]Cases `x ?= y` of EGAL =>false | _ => true end.

End numbers.

Section iterate.

(* [n]th iteration of the function [f] *)
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
Save.

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
Save.

Theorem iter_pos_add :
  (n,m:positive)(A:Set)(f:A->A)(x:A)
    (iter_pos (add n m) A f x)=(iter_pos n A f (iter_pos m A f x)).

Intros.
Rewrite -> (iter_convert m A f x).
Rewrite -> (iter_convert n A f (iter_nat (convert m) A f x)).
Rewrite -> (iter_convert (add n m) A f x).
Rewrite -> (convert_add n m).
Apply iter_nat_plus.
Save.

(* Preservation of invariants : if f : A->A preserves the invariant Inv, 
  then the iterates of f also preserve it. *)

Theorem iter_nat_invariant :
  (n:nat)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_nat n A f x)).
Induction n; Intros;
[ Trivial with arith
| Simpl; Apply H0 with x:=(iter_nat n0 A f x); Apply H; Trivial with arith].
Save.

Theorem iter_pos_invariant :
  (n:positive)(A:Set)(f:A->A)(Inv:A->Prop)
  ((x:A)(Inv x)->(Inv (f x)))->(x:A)(Inv x)->(Inv (iter_pos n A f x)).
Intros; Rewrite iter_convert; Apply iter_nat_invariant; Trivial with arith.
Save.

End iterate.


Section arith.

Lemma ZERO_le_POS : (p:positive) `0 <= (POS p)`.
Intro; Unfold Zle; Unfold Zcompare; Discriminate.
Save.

Lemma POS_gt_ZERO : (p:positive) `(POS p) > 0`.
Intro; Unfold Zgt; Simpl; Trivial with arith.
Save.

Lemma Zlt_ZERO_pred_le_ZERO : (x:Z) `0 < x` -> `0 <= (Zpred x)`.
Intros.
Rewrite (Zs_pred x) in H.
Apply Zgt_S_le.
Apply Zlt_gt.
Assumption.
Save.

(* Zeven, Zodd, Zdiv2 and their related properties *)

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

Lemma Zeven_odd_dec : (z:Z) { (Zeven z) }+{ (Zodd z) }.
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
Save.

Lemma Zeven_dec : (z:Z) { (Zeven z) }+{ ~(Zeven z) }.
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
Save.

Lemma Zodd_dec : (z:Z) { (Zodd z) }+{ ~(Zodd z) }.
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
Save.

Lemma Zeven_not_Zodd : (z:Z)(Zeven z) -> ~(Zodd z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Save.

Lemma Zodd_not_Zeven : (z:Z)(Zodd z) -> ~(Zeven z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Save.

Hints Unfold Zeven Zodd : zarith.

(* Zdiv2 is defined on all Z, but notice that for odd negative integers
 * it is not the euclidean quotient: in that case we have n = 2*(n/2)-1
 *)

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
Save.

Lemma Zodd_div2 : (x:Z) `x >= 0` -> (Zodd x) -> `x = 2*(Zdiv2 x)+1`.
Proof.
NewDestruct x.
Intros. Absurd (Zodd `0`); Red; Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zodd (POS (xO p))); Red; Auto with arith.
Intros. Absurd `(NEG p) >= 0`; Red; Auto with arith.
Save.

Lemma Z_modulo_2 : (x:Z) `x >= 0` -> { y:Z | `x=2*y` }+{ y:Z | `x=2*y+1` }.
Proof.
Intros x Hx.
Elim (Zeven_odd_dec x); Intro.
Left. Split with (Zdiv2 x). Exact (Zeven_div2 x a).
Right. Split with (Zdiv2 x). Exact (Zodd_div2 x Hx b).
Save.

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
Save.

(* Decompose an egality between two ?= relations into 3 implications *)
Theorem Zcompare_egal_dec :
   (x1,y1,x2,y2:Z)
    (`x1 < y1`->`x2 < y2`)
     ->(`x1 ?= y1`=EGAL -> `x2 ?= y2`=EGAL)
        ->(`x1 > y1`->`x2 > y2`)->`x1 ?= y1`=`x2 ?= y2`.
Intros x1 y1 x2 y2.
Unfold Zgt; Unfold Zlt;
Case `x1 ?= y1`; Case `x2 ?= y2`; Auto with arith; Symmetry; Auto with arith.
Save.

Theorem Zcompare_elim :
  (c1,c2,c3:Prop)(x,y:Z)
    ((x=y) -> c1) ->(`x < y` -> c2) ->(`x > y`-> c3)
       -> Case `x ?= y`of c1 c2 c3 end.

Intros.
Apply rename with x:=`x ?= y`; Intro r; Elim r;
[ Intro; Apply H; Apply (let (h1, h2)=(Zcompare_EGAL x y) in h1); Assumption
| Unfold Zlt in H0; Assumption
| Unfold Zgt in H1; Assumption ].
Save.

Lemma Zcompare_x_x : (x:Z) `x ?= x` = EGAL.
Intro; Apply Case (Zcompare_EGAL x x) of [h1,h2: ?]h2 end.
Apply refl_equal.
Save.

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
Save.

Lemma Zcompare_eq_case : 
  (c1,c2,c3:Prop)(x,y:Z) c1 -> x=y -> (Case `x ?= y` of c1 c2 c3 end).
Intros.
Rewrite -> (Case (Zcompare_EGAL x y) of [h1,h2: ?]h2 end H0).
Assumption.
Save.

(* Four very basic lemmas about Zle, Zlt, Zge, Zgt *)
Lemma Zle_Zcompare :
  (x,y:Z)`x <= y` -> Case `x ?= y` of True True False end.
Intros x y; Unfold Zle; Elim `x ?=y`; Auto with arith.
Save.

Lemma Zlt_Zcompare :
  (x,y:Z)`x < y`  -> Case `x ?= y` of False True False end.
Intros x y; Unfold Zlt; Elim `x ?=y`; Intros; Discriminate Orelse Trivial with arith.
Save.

Lemma Zge_Zcompare :
  (x,y:Z)` x >= y`-> Case `x ?= y` of True False True end.
Intros x y; Unfold Zge; Elim `x ?=y`; Auto with arith. 
Save.

Lemma Zgt_Zcompare :
  (x,y:Z)`x > y` -> Case `x ?= y` of False False True end.
Intros x y; Unfold Zgt; Elim `x ?= y`; Intros; Discriminate Orelse Trivial with arith.
Save.

(* Lemmas about Zmin *)

Lemma Zmin_plus : (x,y,n:Z) `(Zmin (x+n)(y+n))=(Zmin x y)+n`.
Intros; Unfold Zmin.
Rewrite (Zplus_sym x n);
Rewrite (Zplus_sym y n);
Rewrite (Zcompare_Zplus_compatible x y n).
Case `x ?= y`; Apply Zplus_sym.
Save.

(* Lemmas about absolu *)

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
Save.


End arith.

