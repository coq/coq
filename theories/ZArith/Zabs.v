(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Arith.
Require fast_integer.
Require Zorder.

V7only [Import nat_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Properties of absolute value *)

Lemma Zabs_eq : (x:Z) (Zle ZERO x) -> (Zabs x)=x.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

Lemma Zabs_non_eq : (x:Z) (Zle x ZERO) -> (Zabs x)=(Zopp x).
Proof.
NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

Definition Zabs_dec : (x:Z){x=(Zabs x)}+{x=(Zopp (Zabs x))}.
Proof.
NewDestruct x;Auto with arith.
Defined.

Lemma Zabs_pos : (x:Z)(Zle ZERO (Zabs x)).
NewDestruct x;Auto with arith; Compute; Intros H;Inversion H.
Qed.

Lemma Zsgn_Zabs: (x:Z)(Zmult x (Zsgn x))=(Zabs x).
Proof.
NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

Lemma Zabs_Zsgn: (x:Z)(Zmult (Zabs x) (Zsgn x))=x.
Proof.
NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

(** absolute value in nat is compatible with order *)

Lemma absolu_lt : (x,y:Z) (Zle ZERO x)/\(Zlt x  y) -> (lt (absolu x) (absolu y)).
Proof.
Intros x y. Case x; Simpl. Case y; Simpl.

Intro. Absurd (Zlt ZERO ZERO). Compute. Intro H0. Discriminate H0. Intuition.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.
Intros. Elim (ZL4 p). Intros. Rewrite H0. Auto with arith.

Case y; Simpl.
Intros. Absurd (Zlt (POS p) ZERO). Compute. Intro H0. Discriminate H0. Intuition.
Intros. Change (gt (convert p) (convert p0)).
Apply compare_convert_SUPERIEUR.
Elim H; Auto with arith. Intro. Exact (ZC2 p0 p).

Intros. Absurd (Zlt (POS p0) (NEG p)).
Compute. Intro H0. Discriminate H0. Intuition.

Intros. Absurd (Zle ZERO (NEG p)). Compute. Auto with arith. Intuition.
Qed.

Lemma Zlt_minus : (n,m:Z)(Zlt ZERO m)->(Zlt (Zminus n m) n).
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=m; Rewrite Zle_plus_minus;
Pattern 1 n ;Rewrite <- (Zero_right n); Rewrite (Zplus_sym m n);
Apply Zlt_reg_l; Assumption.
Qed.

Lemma Zlt_O_minus_lt : (n,m:Z)(Zlt ZERO (Zminus n m))->(Zlt m n).
Proof.
Intros n m H; Apply Zsimpl_lt_plus_l with p:=(Zopp m); Rewrite Zplus_inverse_l;
Rewrite Zplus_sym;Exact H.
Qed.
