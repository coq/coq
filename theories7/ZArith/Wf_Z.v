(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require BinInt.
Require Zcompare.
Require Zorder.
Require Znat.
Require Zmisc.
Require Zsyntax.
Require Wf_nat.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

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
Intro x; NewDestruct x; Intros;
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
Intro y; NewInduction y as [p H|p H1|]; [
  Elim H; Intros x H1; Exists (plus (S x) (S x));
  Unfold convert ;Simpl; Rewrite ZL0; Rewrite ZL2; Unfold convert in H1;
  Rewrite H1; Auto with arith
| Elim H1;Intros x H2; Exists (plus x (S x)); Unfold convert;
  Simpl; Rewrite ZL0; Rewrite ZL2;Unfold convert in H2; Rewrite H2; Auto with arith
| Exists O ;Auto with arith].
Qed.

Lemma inject_nat_complete_inf :
  (x:Z)`0 <= x` -> { n:nat | (x=(inject_nat n)) }.
Intro x; NewDestruct x; Intros;
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
Intros P H x H0.
Specialize (inject_nat_complete x H0).
Intros Hn; Elim Hn; Intros.
Rewrite -> H1; Apply H.
Qed.

Lemma inject_nat_set :
  (P:Z->Set)((n:nat)(P (inject_nat n))) -> 
    (x:Z) `0 <= x` -> (P x).
Intros P H x H0.
Specialize (inject_nat_complete_inf x H0).
Intros Hn; Elim Hn; Intros.
Rewrite -> p; Apply H.
Qed.

Lemma natlike_ind : (P:Z->Prop) (P `0`) ->
  ((x:Z)(`0 <= x` -> (P x) -> (P (Zs x)))) ->
  (x:Z) `0 <= x` -> (P x).
Intros P H H0 x H1; Apply inject_nat_prop;
[ Induction n;
  [ Simpl; Assumption
  | Intros; Rewrite -> (inj_S n0);
    Exact (H0 (inject_nat n0) (ZERO_le_inj n0) H2) ]
| Assumption].
Qed.

Lemma natlike_rec : (P:Z->Set) (P `0`) ->
  ((x:Z)(`0 <= x` -> (P x) -> (P (Zs x)))) ->
  (x:Z) `0 <= x` -> (P x).
Intros P H H0 x H1; Apply inject_nat_set;
[ Induction n;
  [ Simpl; Assumption
  | Intros; Rewrite -> (inj_S n0);
    Exact (H0 (inject_nat n0) (ZERO_le_inj n0) H2) ]
| Assumption].
Qed.

Section Efficient_Rec. 

(** [natlike_rec2] is the same as [natlike_rec], but with a different proof, designed 
     to give a better extracted term. *)

Local R := [a,b:Z]`0<=a`/\`a<b`.

Local R_wf : (well_founded Z R).
Proof.
LetTac f := [z]Cases z of (POS p) => (convert p) | ZERO => O | (NEG _) => O end.
Apply  well_founded_lt_compat with f.
Unfold R f; Clear f R.
Intros x y; Case x; Intros; Elim H; Clear H.
Case y; Intros; Apply compare_convert_O Orelse Inversion H0.
Case y; Intros; Apply compare_convert_INFERIEUR Orelse Inversion H0; Auto.
Intros; Elim H; Auto.
Qed.

Lemma natlike_rec2 : (P:Z->Type)(P `0`) -> 
        ((z:Z)`0<=z` -> (P z) -> (P (Zs z))) -> (z:Z)`0<=z` -> (P z).
Proof.
Intros P Ho Hrec z; Pattern z; Apply (well_founded_induction_type Z R R_wf).
Intro x; Case x.
Trivial.
Intros.
Assert `0<=(Zpred (POS p))`.
Apply Zlt_ZERO_pred_le_ZERO; Unfold Zlt; Simpl; Trivial.
Rewrite Zs_pred.
Apply Hrec.
Auto.
Apply X; Auto; Unfold R; Intuition; Apply Zlt_pred_n_n.
Intros; Elim H; Simpl; Trivial.
Qed.

(** A variant of the previous using [Zpred] instead of [Zs]. *)

Lemma natlike_rec3 : (P:Z->Type)(P `0`) -> 
        ((z:Z)`0<z` -> (P (Zpred z)) -> (P z)) -> (z:Z)`0<=z` -> (P z).
Proof.
Intros P Ho Hrec z; Pattern z; Apply (well_founded_induction_type Z R R_wf).
Intro x; Case x.
Trivial.
Intros; Apply Hrec.
Unfold Zlt; Trivial.
Assert `0<=(Zpred (POS p))`.
Apply Zlt_ZERO_pred_le_ZERO; Unfold Zlt; Simpl; Trivial.
Apply X; Auto; Unfold R; Intuition; Apply Zlt_pred_n_n.
Intros; Elim H; Simpl; Trivial.
Qed.

(** A more general induction principal using [Zlt]. *)

Lemma Z_lt_rec : (P:Z->Type)
 ((x:Z)((y:Z)`0 <= y < x`->(P y))->(P x)) -> (x:Z)`0 <= x`->(P x).
Proof.
Intros P Hrec z; Pattern z; Apply (well_founded_induction_type Z R R_wf).
Intro x; Case x; Intros.
Apply Hrec; Intros.
Assert H2: `0<0`.
  Apply Zle_lt_trans with y; Intuition.
Inversion H2.
Firstorder.
Unfold Zle Zcompare in H; Elim H; Auto.
Defined.

Lemma Z_lt_induction : 
  (P:Z->Prop)
     ((x:Z)((y:Z)`0 <= y < x`->(P y))->(P x))
  -> (x:Z)`0 <= x`->(P x).
Proof.
Exact Z_lt_rec.
Qed.

End Efficient_Rec.
