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
Import Z_scope.

(** Our purpose is to write an induction shema for {0,1,2,...}
  similar to the [nat] schema (Theorem [Natlike_rec]). For that the
  following implications will be used :
<<
 (n:nat)(Q n)==(n:nat)(P (inject_nat n)) ===> (x:Z)`x > 0) -> (P x)

       	     /\
             ||
             ||

  (Q O) (n:nat)(Q n)->(Q (S n)) <=== (P 0) (x:Z) (P x) -> (P (Zs x))

      	       	       	       	<=== (inject_nat (S n))=(Zs (inject_nat n))

      	       	       	       	<=== inject_nat_complete
>>
  Then the  diagram will be closed and the theorem proved. *)

Lemma inject_nat_complete :
  (x:Z)`0 <= x` -> (EX n:nat | x=(inject_nat n)).
NewDestruct x; Intros;
[ Exists  O; Auto with arith
| Specialize (ZL4 p); Intros Hp; Elim Hp; Intros;
  Exists (S x); Intros; Simpl;
  Specialize (bij1 x); Intro Hx0;
  Rewrite <- H0 in Hx0;
  Apply f_equal with f:=POS;
  Apply convert_intro; Auto with arith
| Absurd `0 <= (NEG p)`;
  [ Unfold Zle; Simpl; Do 2 (Unfold not); Auto with arith
  | Assumption]
].
Qed.

Lemma ZL4_inf: (y:positive) { h:nat | (convert y)=(S h) }.
Induction y; [
  Intros p H;Elim H; Intros x H1; Exists (plus (S x) (S x));
  Unfold convert ;Simpl; Rewrite ZL0; Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| Intros p H1;Elim H1;Intros x H2; Exists (plus x (S x)); Unfold convert;
  Simpl; Rewrite ZL0; Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith].
Qed.

Lemma inject_nat_complete_inf :
  (x:Z)`0 <= x` -> { n:nat | (x=(inject_nat n)) }.
NewDestruct x; Intros;
[ Exists  O; Auto with arith
| Specialize (ZL4_inf p); Intros Hp; Elim Hp; Intros x0 H0;
  Exists (S x0); Intros; Simpl;
  Specialize (bij1 x0); Intro Hx0;
  Rewrite <- H0 in Hx0;
  Apply f_equal with f:=POS;
  Apply convert_intro; Auto with arith
| Absurd `0 <= (NEG p)`;
  [ Unfold Zle; Simpl; Do 2 (Unfold not); Auto with arith
  | Assumption]
].
Qed.

Lemma inject_nat_prop :
  (P:Z->Prop)((n:nat)(P (inject_nat n))) -> 
    (x:Z) `0 <= x` -> (P x).
Intros.
Specialize (inject_nat_complete x H0).
Intros Hn; Elim Hn; Intros.
Rewrite -> H1; Apply H.
Qed.

Lemma inject_nat_set :
  (P:Z->Set)((n:nat)(P (inject_nat n))) -> 
    (x:Z) `0 <= x` -> (P x).
Intros.
Specialize (inject_nat_complete_inf x H0).
Intros Hn; Elim Hn; Intros.
Rewrite -> p; Apply H.
Qed.

Lemma ZERO_le_inj :
  (n:nat) `0 <= (inject_nat n)`.
Induction n; Simpl; Intros;
[ Apply Zle_n
| Unfold Zle; Simpl; Discriminate].
Qed.

Lemma natlike_ind : (P:Z->Prop) (P `0`) ->
  ((x:Z)(`0 <= x` -> (P x) -> (P (Zs x)))) ->
  (x:Z) `0 <= x` -> (P x).
Intros; Apply inject_nat_prop;
[ Induction n;
  [ Simpl; Assumption
  | Intros; Rewrite -> (inj_S n0);
    Exact (H0 (inject_nat n0) (ZERO_le_inj n0) H2) ]
| Assumption].
Qed.

Lemma natlike_rec : (P:Z->Set) (P `0`) ->
  ((x:Z)(`0 <= x` -> (P x) -> (P (Zs x)))) ->
  (x:Z) `0 <= x` -> (P x).
Intros; Apply inject_nat_set;
[ Induction n;
  [ Simpl; Assumption
  | Intros; Rewrite -> (inj_S n0);
    Exact (H0 (inject_nat n0) (ZERO_le_inj n0) H2) ]
| Assumption].
Qed.

Lemma Z_lt_induction : 
  (P:Z->Prop)
     ((x:Z)((y:Z)`0 <= y < x`->(P y))->(P x))
  -> (x:Z)`0 <= x`->(P x).
Proof.
Intros P H x Hx.
Cut (x:Z)`0 <= x`->(y:Z)`0 <= y < x`->(P y).
Intro.
Apply (H0 (Zs x)).
Auto with zarith.

Split; [ Assumption | Exact (Zlt_n_Sn x) ].

Intros x0 Hx0; Generalize Hx0; Pattern x0; Apply natlike_ind.
Intros.
Absurd `0 <= 0`; Try Assumption.
Apply Zgt_not_le.
Apply Zgt_le_trans with m:=y.
Apply Zlt_gt.
Intuition. Intuition.

Intros. Apply H. Intros.
Apply (H1 H0).
Split; [ Intuition | Idtac ].
Apply Zlt_le_trans with y. Intuition.
Apply Zgt_S_le. Apply Zlt_gt. Intuition.

Assumption.
Qed.

Lemma Z_lt_rec : 
  (P:Z->Set)
     ((x:Z)((y:Z)`0 <= y < x`->(P y))->(P x))
  -> (x:Z)`0 <= x`->(P x).
Proof.
Intros P H x Hx.
Cut (x:Z)`0 <= x`->(y:Z)`0 <= y < x`->(P y).
Intro.
Apply (H0 (Zs x)).
Auto with zarith.

Split; [ Assumption | Exact (Zlt_n_Sn x) ].

Intros x0 Hx0; Generalize Hx0; Pattern x0; Apply natlike_rec.
Intros.
Absurd `0 <= 0`; Try Assumption.
Apply Zgt_not_le.
Apply Zgt_le_trans with m:=y.
Apply Zlt_gt.
Intuition. Intuition.

Intros. Apply H. Intros.
Apply (H1 H0).
Split; [ Intuition | Idtac ].
Apply Zlt_le_trans with y. Intuition.
Apply Zgt_S_le. Apply Zlt_gt. Intuition.

Assumption.
Qed.
