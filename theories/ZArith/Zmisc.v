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

(**********************************************************************)
(** Boolean comparisons of binary integers *)

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
    Intros. Apply iff_trans with `y < x`. Split. Exact (Zgt_lt x y).
    Exact (Zlt_gt y x).
    Exact (Zlt_is_le_bool y x).
  Qed.

(**********************************************************************)
(** Iterators *)

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


(**********************************************************************)
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
Defined.

Definition Zeven_dec : (z:Z) { (Zeven z) }+{ ~(Zeven z) }.
Proof.
  Intro z. Case z;
  [ Left; Compute; Trivial
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) 
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) ].
Defined.

Definition Zodd_dec : (z:Z) { (Zodd z) }+{ ~(Zodd z) }.
Proof.
  Intro z. Case z;
  [ Right; Compute; Trivial
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) 
  | Intro p; Case p; Intros; 
    (Left; Compute; Exact I) Orelse (Right; Compute; Trivial) ].
Defined.

Lemma Zeven_not_Zodd : (z:Z)(Zeven z) -> ~(Zodd z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Lemma Zodd_not_Zeven : (z:Z)(Zodd z) -> ~(Zeven z).
Proof.
  NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Lemma Zeven_Sn : (z:Z)(Zodd z) -> (Zeven (Zs z)).
Proof.
 NewDestruct z; Unfold Zs; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zodd_Sn : (z:Z)(Zeven z) -> (Zodd (Zs z)).
Proof.
 NewDestruct z; Unfold Zs; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zeven_pred : (z:Z)(Zodd z) -> (Zeven (Zpred z)).
Proof.
 NewDestruct z; Unfold Zpred; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zodd_pred : (z:Z)(Zeven z) -> (Zodd (Zpred z)).
Proof.
 NewDestruct z; Unfold Zpred; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Hints Unfold Zeven Zodd : zarith.

(**********************************************************************)
(** [Zdiv2] is defined on all [Z], but notice that for odd negative
    integers it is not the euclidean quotient: in that case we have [n =
    2*(n/2)-1] *)

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

Lemma Zodd_div2_neg : (x:Z) `x <= 0` -> (Zodd x) -> `x = 2*(Zdiv2 x)-1`.
Proof.
NewDestruct x.
Intros. Absurd (Zodd `0`); Red; Auto with arith.
Intros. Absurd `(NEG p) >= 0`; Red; Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zodd (NEG (xO p))); Red; Auto with arith.
Qed.

Lemma Z_modulo_2 : (x:Z) { y:Z | `x=2*y` }+{ y:Z | `x=2*y+1` }.
Proof.
Intros x.
Elim (Zeven_odd_dec x); Intro.
Left. Split with (Zdiv2 x). Exact (Zeven_div2 x a).
Right. Generalize b; Clear b; Case x.
Intro b; Inversion b.
Intro p; Split with (Zdiv2 (POS p)). Apply (Zodd_div2 (POS p)); Trivial.
Unfold Zge Zcompare; Simpl; Discriminate.
Intro p; Split with (Zdiv2 (Zpred (NEG p))).
Pattern 1 (NEG p); Rewrite (Zs_pred (NEG p)).
Pattern 1 (Zpred (NEG p)); Rewrite (Zeven_div2 (Zpred (NEG p))).
Reflexivity.
Apply Zeven_pred; Assumption.
Qed.

Lemma Zsplit2 :  (x:Z) { p : Z*Z | let (x1,x2)=p in (`x=x1+x2` /\ (x1=x2 \/ `x2=x1+1`)) }.
Proof.
Intros x.
Elim (Z_modulo_2 x); Intros (y,Hy); Rewrite Zmult_sym in Hy; Rewrite <- Zred_factor1 in Hy.
Exists (y,y); Split. 
Assumption.
Left; Reflexivity.
Exists (y,y+`1`); Split.
Rewrite Zplus_assoc; Assumption.
Right; Reflexivity.
Qed.

