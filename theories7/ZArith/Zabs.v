(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

(** Binary Integers (Pierre Crégut (CNET, Lannion, France) *)

Require Arith.
Require BinPos.
Require BinInt.
Require Zorder.
Require Zsyntax.
Require ZArith_dec.

V7only [Import nat_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Properties of absolute value *)

Lemma Zabs_eq : (x:Z) (Zle ZERO x) -> (Zabs x)=x.
Intro x; NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

Lemma Zabs_non_eq : (x:Z) (Zle x ZERO) -> (Zabs x)=(Zopp x).
Proof.
Intro x; NewDestruct x; Auto with arith.
Compute; Intros; Absurd SUPERIEUR=SUPERIEUR; Trivial with arith.
Qed.

V7only [ (* From Zdivides *) ].
Theorem Zabs_Zopp: (z : Z)  (Zabs (Zopp z)) = (Zabs z).
Proof.
Intros z; Case z; Simpl; Auto.
Qed.

(** Proving a property of the absolute value by cases *)

Lemma Zabs_ind : 
  (P:Z->Prop)(x:Z)(`x >= 0` -> (P x)) -> (`x <= 0` -> (P `-x`)) ->
  (P `|x|`).
Proof.
Intros P x H H0; Elim (Z_lt_ge_dec x `0`); Intro.
Assert `x<=0`. Apply Zlt_le_weak; Assumption.
Rewrite Zabs_non_eq. Apply H0. Assumption. Assumption.
Rewrite Zabs_eq. Apply H; Assumption. Apply Zge_le. Assumption.
Save.

V7only [ (* From Zdivides *) ].
Theorem Zabs_intro: (P : ?) (z : Z) (P (Zopp z)) -> (P z) ->  (P (Zabs z)).
Intros P z; Case z; Simpl; Auto.
Qed.

Definition Zabs_dec : (x:Z){x=(Zabs x)}+{x=(Zopp (Zabs x))}.
Proof.
Intro x; NewDestruct x;Auto with arith.
Defined.

Lemma Zabs_pos : (x:Z)(Zle ZERO (Zabs x)).
Intro x; NewDestruct x;Auto with arith; Compute; Intros H;Inversion H.
Qed.

V7only [ (* From Zdivides *) ].
Theorem Zabs_eq_case:
 (z1, z2 : Z) (Zabs z1) = (Zabs z2) ->  z1 = z2 \/ z1 = (Zopp z2).
Proof.
Intros z1 z2; Case z1; Case z2; Simpl; Auto; Try (Intros; Discriminate);
 Intros p1 p2 H1; Injection H1; (Intros H2; Rewrite H2); Auto.
Qed.

(** Triangular inequality *)

Hints Local Resolve Zle_NEG_POS :zarith.

V7only [ (* From Zdivides *) ].
Theorem Zabs_triangle:
 (z1, z2 : Z)  (Zle (Zabs (Zplus z1 z2)) (Zplus (Zabs z1) (Zabs z2))).
Proof.
Intros z1 z2; Case z1; Case z2; Try (Simpl; Auto with zarith; Fail).
Intros p1 p2;
 Apply Zabs_intro
      with P := [x : ?]  (Zle x (Zplus (Zabs (POS p2)) (Zabs (NEG p1))));
 Try Rewrite Zopp_Zplus; Auto with zarith.
Apply Zle_plus_plus; Simpl; Auto with zarith.
Apply Zle_plus_plus; Simpl; Auto with zarith.
Intros p1 p2;
 Apply Zabs_intro
      with P := [x : ?]  (Zle x (Zplus (Zabs (POS p2)) (Zabs (NEG p1))));
 Try Rewrite Zopp_Zplus; Auto with zarith.
Apply Zle_plus_plus; Simpl; Auto with zarith.
Apply Zle_plus_plus; Simpl; Auto with zarith.
Qed.

(** Absolute value and multiplication *)

Lemma Zsgn_Zabs: (x:Z)(Zmult x (Zsgn x))=(Zabs x).
Proof.
Intro x; NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

Lemma Zabs_Zsgn: (x:Z)(Zmult (Zabs x) (Zsgn x))=x.
Proof.
Intro x; NewDestruct x; Rewrite Zmult_sym; Auto with arith.
Qed.

V7only [ (* From Zdivides *) ].
Theorem Zabs_Zmult:
 (z1, z2 : Z)  (Zabs (Zmult z1 z2)) = (Zmult (Zabs z1) (Zabs z2)).
Proof.
Intros z1 z2; Case z1; Case z2; Simpl; Auto.
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
