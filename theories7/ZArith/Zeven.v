(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require BinInt.
Require Zsyntax.

(**********************************************************************)
(** About parity: even and odd predicates on Z, division by 2 on Z *)

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
  Intro z; NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Lemma Zodd_not_Zeven : (z:Z)(Zodd z) -> ~(Zeven z).
Proof.
  Intro z; NewDestruct z; [ Idtac | NewDestruct p | NewDestruct p  ]; Compute; Trivial.
Qed.

Lemma Zeven_Sn : (z:Z)(Zodd z) -> (Zeven (Zs z)).
Proof.
 Intro z; NewDestruct z; Unfold Zs; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zodd_Sn : (z:Z)(Zeven z) -> (Zodd (Zs z)).
Proof.
 Intro z; NewDestruct z; Unfold Zs; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zeven_pred : (z:Z)(Zodd z) -> (Zeven (Zpred z)).
Proof.
 Intro z; NewDestruct z; Unfold Zpred; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
 Unfold double_moins_un; Case p; Simpl; Auto.
Qed.

Lemma Zodd_pred : (z:Z)(Zeven z) -> (Zodd (Zpred z)).
Proof.
 Intro z; NewDestruct z; Unfold Zpred; [ Idtac | NewDestruct p | NewDestruct p  ]; Simpl; Trivial. 
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
Intro x; NewDestruct x.
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
Intro x; NewDestruct x.
Intros. Absurd (Zodd `0`); Red; Auto with arith.
NewDestruct p; Auto with arith.
Intros. Absurd (Zodd (POS (xO p))); Red; Auto with arith.
Intros. Absurd `(NEG p) >= 0`; Red; Auto with arith.
Qed.

Lemma Zodd_div2_neg : (x:Z) `x <= 0` -> (Zodd x) -> `x = 2*(Zdiv2 x)-1`.
Proof.
Intro x; NewDestruct x.
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
Elim (Z_modulo_2 x); Intros (y,Hy); Rewrite Zmult_sym in Hy; Rewrite <- Zplus_Zmult_2 in Hy.
Exists (y,y); Split. 
Assumption.
Left; Reflexivity.
Exists (y,`y+1`); Split.
Rewrite Zplus_assoc; Assumption.
Right; Reflexivity.
Qed.
