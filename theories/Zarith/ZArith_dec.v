
(* $Id$ *)

Require Sumbool.

Require fast_integer.
Require zarith_aux.
Require auxiliary.
Require Zsyntax.

Lemma Dcompare_inf : (r:relation) {r=EGAL} + {r=INFERIEUR} + {r=SUPERIEUR}.
Proof.
Induction r; Auto with arith. 
Save.

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
Save.


Section decidability.

Local inf_decidable := [P:Prop] {P}+{~P}.

Variables x,y : Z.


Theorem Z_eq_dec : (inf_decidable (x=y)).
Proof.
Unfold inf_decidable.
Apply Zcompare_rec with x:=x y:=y.
Intro. Left. Elim (Zcompare_EGAL x y); Auto with arith.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Intro H3. Right. Elim (Zcompare_EGAL x y). Intros H1 H2. Unfold not. Intro H4.
  Rewrite (H2 H4) in H3. Discriminate H3.
Save. 

Theorem Z_lt_dec : (inf_decidable (Zlt x y)).
Proof.
Unfold inf_decidable Zlt.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Right. Rewrite H. Discriminate.
Left; Assumption.
Right. Rewrite H. Discriminate.
Save.

Theorem Z_le_dec : (inf_decidable (Zle x y)).
Proof.
Unfold inf_decidable Zle.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Left. Rewrite H. Discriminate.
Left. Rewrite H. Discriminate.
Right. Tauto.
Save.

Theorem Z_gt_dec : (inf_decidable (Zgt x y)).
Proof.
Unfold inf_decidable Zgt.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Right. Rewrite H. Discriminate.
Right. Rewrite H. Discriminate.
Left; Assumption.
Save.

Theorem Z_ge_dec : (inf_decidable (Zge x y)).
Proof.
Unfold inf_decidable Zge.
Apply Zcompare_rec with x:=x y:=y; Intro H.
Left. Rewrite H. Discriminate.
Right. Tauto.
Left. Rewrite H. Discriminate.
Save.

Theorem Z_lt_ge_dec : {`x < y`}+{`x >= y`}.
Proof Z_lt_dec.

Theorem Z_le_gt_dec : {`x <= y`}+{`x > y`}.
Proof.
Elim Z_le_dec; Auto with arith.
Intro. Right. Apply not_Zle; Auto with arith.
Save.

Theorem Z_gt_le_dec : {`x > y`}+{`x <= y`}.
Proof Z_gt_dec.

Theorem Z_ge_lt_dec : {`x >= y`}+{`x < y`}.
Proof.
Elim Z_ge_dec; Auto with arith.
Intro. Right. Apply not_Zge; Auto with arith.
Save.


Theorem Z_le_lt_eq_dec : `x <= y` -> {`x < y`}+{x=y}.
Proof.
Intro H.
Apply Zcompare_rec with x:=x y:=y.
Intro. Right. Elim (Zcompare_EGAL x y); Auto with arith.
Intro. Left. Elim (Zcompare_EGAL x y); Auto with arith.
Intro H1. Absurd `x > y`; Auto with arith.
Save.


End decidability.


Theorem Z_zerop : (x:Z){(`x = 0`)}+{(`x <> 0`)}.
Proof [x:Z](Z_eq_dec x ZERO).

Definition Z_notzerop := [x:Z](sumbool_not ? ? (Z_zerop x)).

Definition Z_noteq_dec := [x,y:Z](sumbool_not ? ? (Z_eq_dec x y)).
