(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Sumbool.

Require fast_integer.
Require Zorder.
Require zarith_aux.
Require auxiliary.
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

Definition Z_eq_dec : {x=y}+{~x=y}.
Proof.
Apply Zcompare_rec with x:=x y:=y.
Intro. Left. Elim (Zcompare_EGAL x y); Auto with arith.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Defined. 

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


Definition Z_zerop : (x:Z){(`x = 0`)}+{(`x <> 0`)}.
Proof.
Exact [x:Z](Z_eq_dec x ZERO).
Defined.

Definition Z_notzerop := [x:Z](sumbool_not ? ? (Z_zerop x)).

Definition Z_noteq_dec := [x,y:Z](sumbool_not ? ? (Z_eq_dec x y)).
