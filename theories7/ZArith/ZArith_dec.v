(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Sumbool.

Require BinInt.
Require Zorder.
Require Zcompare.
Require Zsyntax.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

Lemma Dcompare_inf : (r:relation) {r=EGAL} + {r=INFERIEUR} + {r=SUPERIEUR}.
Proof.
Induction r; Auto with arith. 
Defined.

Lemma Zcompare_rec :
  (P:Set)(x,y:Z)
    ((Zcompare x y)=EGAL -> P) ->
    ((Zcompare x y)=INFERIEUR -> P) ->
    ((Zcompare x y)=SUPERIEUR -> P) ->
    P.
Proof.
Intros P x y H1 H2 H3.
Elim (Dcompare_inf (Zcompare x y)).
Intro H. Elim H; Auto with arith. Auto with arith.
Defined.

Section decidability.

Variables x,y : Z.

(** Decidability of equality on binary integers *)

Definition Z_eq_dec : {x=y}+{~x=y}.
Proof.
Apply Zcompare_rec with x:=x y:=y.
Intro. Left. Elim (Zcompare_EGAL x y); Auto with arith.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Defined. 

(** Decidability of order on binary integers *)

Definition Z_lt_dec : {(Zlt x y)}+{~(Zlt x y)}.
Proof.
Unfold Zlt.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Right. Rewrite H. Discriminate.
Left; Assumption.
Right. Rewrite H. Discriminate.
Defined.

Definition Z_le_dec : {(Zle x y)}+{~(Zle x y)}.
Proof.
Unfold Zle.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Left. Rewrite H. Discriminate.
Left. Rewrite H. Discriminate.
Right. Tauto.
Defined.

Definition Z_gt_dec : {(Zgt x y)}+{~(Zgt x y)}.
Proof.
Unfold Zgt.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Right. Rewrite H. Discriminate.
Right. Rewrite H. Discriminate.
Left; Assumption.
Defined.

Definition Z_ge_dec : {(Zge x y)}+{~(Zge x y)}.
Proof.
Unfold Zge.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Left. Rewrite H. Discriminate.
Right. Tauto.
Left. Rewrite H. Discriminate.
Defined.

Definition Z_lt_ge_dec : {`x < y`}+{`x >= y`}.
Proof.
Exact Z_lt_dec.
Defined.

V7only [ (* From Zextensions *) ].
Lemma Z_lt_le_dec: {`x < y`}+{`y <= x`}.
Proof.
Intros.
Elim Z_lt_ge_dec.
Intros; Left; Assumption.
Intros; Right; Apply Zge_le; Assumption.
Qed.

Definition Z_le_gt_dec : {`x <= y`}+{`x > y`}.
Proof.
Elim Z_le_dec; Auto with arith.
Intro. Right. Apply not_Zle; Auto with arith.
Defined.

Definition Z_gt_le_dec : {`x > y`}+{`x <= y`}.
Proof.
Exact Z_gt_dec.
Defined.

Definition Z_ge_lt_dec : {`x >= y`}+{`x < y`}.
Proof.
Elim Z_ge_dec; Auto with arith.
Intro. Right. Apply not_Zge; Auto with arith.
Defined.

Definition Z_le_lt_eq_dec : `x <= y` -> {`x < y`}+{x=y}.
Proof.
Intro H.
Apply Zcompare_rec with x:=x y:=y.
Intro. Right. Elim (Zcompare_EGAL x y); Auto with arith.
Intro. Left. Elim (Zcompare_EGAL x y); Auto with arith.
Intro H1. Absurd `x > y`; Auto with arith.
Defined.

End decidability.

(** Cotransitivity of order on binary integers *)

Lemma Zlt_cotrans:(n,m:Z)`n<m`->(p:Z){`n<p`}+{`p<m`}.
Proof.
 Intros x y H z.
 Case (Z_lt_ge_dec x z).
 Intro.
 Left.
 Assumption.
 Intro.
 Right.
 Apply Zle_lt_trans with m:=x.
 Apply Zge_le.
 Assumption.
 Assumption.
Defined.

Lemma Zlt_cotrans_pos:(x,y:Z)`0<x+y`->{`0<x`}+{`0<y`}.
Proof.
 Intros x y H.
 Case (Zlt_cotrans `0` `x+y` H x).
 Intro.
 Left.
 Assumption.
 Intro.
 Right.
 Apply Zsimpl_lt_plus_l with p:=`x`.
 Rewrite Zero_right.
 Assumption.
Defined.

Lemma Zlt_cotrans_neg:(x,y:Z)`x+y<0`->{`x<0`}+{`y<0`}.
Proof.
 Intros x y H;
 Case (Zlt_cotrans `x+y` `0` H x);
 Intro Hxy;
 [ Right;
   Apply Zsimpl_lt_plus_l with p:=`x`;
   Rewrite Zero_right
 | Left
 ];
 Assumption.
Defined.

Lemma not_Zeq_inf:(x,y:Z)`x<>y`->{`x<y`}+{`y<x`}.
Proof.
 Intros x y H.
 Case Z_lt_ge_dec with x y.
 Intro.
 Left.
 Assumption.
 Intro H0.
 Generalize (Zge_le ? ? H0).
 Intro.
 Case (Z_le_lt_eq_dec ? ? H1).
 Intro.
 Right.
 Assumption.
 Intro.
 Apply False_rec.
 Apply H.
 Symmetry.
 Assumption.
Defined.

Lemma Z_dec:(x,y:Z){`x<y`}+{`x>y`}+{`x=y`}.
Proof.
 Intros x y.
 Case (Z_lt_ge_dec x y).
 Intro H.
 Left.
 Left.
 Assumption.
 Intro H.
 Generalize (Zge_le ? ? H).
 Intro H0.
 Case (Z_le_lt_eq_dec y x H0).
 Intro H1.
 Left.
 Right.
 Apply Zlt_gt.
 Assumption.
 Intro.
 Right.
 Symmetry.
 Assumption.
Defined.


Lemma Z_dec':(x,y:Z){`x<y`}+{`y<x`}+{`x=y`}.
Proof.
 Intros x y.
 Case (Z_eq_dec x y);
 Intro H;
 [ Right;
   Assumption
 | Left;
   Apply (not_Zeq_inf ?? H)
 ].
Defined.



Definition Z_zerop : (x:Z){(`x = 0`)}+{(`x <> 0`)}.
Proof.
Exact [x:Z](Z_eq_dec x ZERO).
Defined.

Definition Z_notzerop := [x:Z](sumbool_not ? ? (Z_zerop x)).

Definition Z_noteq_dec := [x,y:Z](sumbool_not ? ? (Z_eq_dec x y)).
