(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rbasic_fun.
Require Even.
Require Div2.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope Z_scope.
Open Local Scope R_scope.

Lemma minus_neq_O : (n,i:nat) (lt i n) -> ~(minus n i)=O.
Intros; Red; Intro.
Cut (n,m:nat) (le m n) -> (minus n m)=O -> n=m.
Intro; Assert H2 := (H1 ? ? (lt_le_weak ? ? H) H0); Rewrite H2 in H; Elim (lt_n_n ? H).
Pose R := [n,m:nat](le m n)->(minus n m)=(0)->n=m.
Cut ((n,m:nat)(R n m)) -> ((n0,m:nat)(le m n0)->(minus n0 m)=(0)->n0=m).
Intro; Apply H1.
Apply nat_double_ind.
Unfold R; Intros; Inversion H2; Reflexivity.
Unfold R; Intros; Simpl in H3; Assumption.
Unfold R; Intros; Simpl in H4; Assert H5 := (le_S_n ? ? H3); Assert H6 := (H2 H5 H4); Rewrite H6; Reflexivity.
Unfold R; Intros; Apply H1; Assumption.
Qed.

Lemma le_minusni_n : (n,i:nat) (le i n)->(le (minus n i) n).
Pose R := [m,n:nat] (le n m) -> (le (minus m n) m).
Cut ((m,n:nat)(R m n)) -> ((n,i:nat)(le i n)->(le (minus n i) n)).
Intro; Apply H.
Apply nat_double_ind.
Unfold R; Intros; Simpl; Apply le_n.
Unfold R; Intros; Simpl; Apply le_n.
Unfold R; Intros; Simpl; Apply le_trans with n.
Apply H0; Apply le_S_n; Assumption.
Apply le_n_Sn.
Unfold R; Intros; Apply H; Assumption.
Qed.

Lemma lt_minus_O_lt : (m,n:nat) (lt m n) -> (lt O (minus n m)).
Intros n m; Pattern n m; Apply nat_double_ind; [
  Intros; Rewrite <- minus_n_O; Assumption
| Intros; Elim (lt_n_O ? H)
| Intros; Simpl; Apply H; Apply lt_S_n; Assumption].
Qed.

Lemma even_odd_cor : (n:nat) (EX p : nat | n=(mult (2) p)\/n=(S (mult (2) p))).
Intro.
Assert H := (even_or_odd n).
Exists (div2 n).
Assert H0 := (even_odd_double n).
Elim H0; Intros.
Elim H1; Intros H3 _.
Elim H2; Intros H4 _.
Replace (mult (2) (div2 n)) with (Div2.double (div2 n)).
Elim H; Intro.
Left.
Apply H3; Assumption.
Right.
Apply H4; Assumption.
Unfold Div2.double; Ring.
Qed.

(* 2m <= 2n => m<=n *)
Lemma le_double : (m,n:nat) (le (mult (2) m) (mult (2) n)) -> (le m n).
Intros; Apply INR_le.
Assert H1 := (le_INR ? ? H).
Do 2 Rewrite mult_INR in H1.
Apply Rle_monotony_contra with ``(INR (S (S O)))``.
Replace (INR (S (S O))) with ``2``; [Sup0 | Reflexivity].
Assumption.
Qed.

(* Here, we have the euclidian division *)
(* This lemma is used in the proof of sin_eq_0 : (sin x)=0<->x=kPI *)
Lemma euclidian_division : (x,y:R) ``y<>0`` -> (EXT k:Z | (EXT r : R | ``x==(IZR k)*y+r``/\``0<=r<(Rabsolu y)``)).
Intros.
Pose k0 := Cases (case_Rabsolu y) of
     (leftT _) => (Zminus `1` (up ``x/-y``))
   | (rightT _) => (Zminus (up ``x/y``) `1`) end.
Exists k0.
Exists ``x-(IZR k0)*y``.
Split.
Ring.
Unfold k0; Case (case_Rabsolu y); Intro.
Assert H0 := (archimed ``x/-y``); Rewrite <- Z_R_minus; Simpl; Unfold Rminus.
Replace ``-((1+ -(IZR (up (x/( -y)))))*y)`` with ``((IZR (up (x/-y)))-1)*y``; [Idtac | Ring].
Split.
Apply Rle_monotony_contra with ``/-y``.
Apply Rlt_Rinv; Apply Rgt_RO_Ropp; Exact r.
Rewrite Rmult_Or; Rewrite (Rmult_sym ``/-y``); Rewrite Rmult_Rplus_distrl; Rewrite <- Ropp_Rinv; [Idtac | Assumption].
Rewrite Rmult_assoc; Repeat Rewrite Ropp_mul3; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1r | Assumption].
Apply Rle_anti_compatibility with ``(IZR (up (x/( -y))))-x/( -y)``.
Rewrite Rplus_Or; Unfold Rdiv; Pattern 4 ``/-y``; Rewrite <- Ropp_Rinv; [Idtac | Assumption].
Replace ``(IZR (up (x*/ -y)))-x* -/y+( -(x*/y)+ -((IZR (up (x*/ -y)))-1))`` with R1; [Idtac | Ring].
Elim H0; Intros _ H1; Unfold Rdiv in H1; Exact H1.
Rewrite (Rabsolu_left ? r); Apply Rlt_monotony_contra with ``/-y``.
Apply Rlt_Rinv; Apply Rgt_RO_Ropp; Exact r.
Rewrite <- Rinv_l_sym.
Rewrite (Rmult_sym ``/-y``); Rewrite Rmult_Rplus_distrl; Rewrite <- Ropp_Rinv; [Idtac | Assumption].
Rewrite Rmult_assoc; Repeat Rewrite Ropp_mul3; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1r | Assumption]; Apply Rlt_anti_compatibility with ``((IZR (up (x/( -y))))-1)``.
Replace ``(IZR (up (x/( -y))))-1+1`` with ``(IZR (up (x/( -y))))``; [Idtac | Ring].
Replace ``(IZR (up (x/( -y))))-1+( -(x*/y)+ -((IZR (up (x/( -y))))-1))`` with ``-(x*/y)``; [Idtac | Ring].
Rewrite <- Ropp_mul3; Rewrite (Ropp_Rinv ? H); Elim H0; Unfold Rdiv; Intros H1 _; Exact H1.
Apply Ropp_neq; Assumption.
Assert H0 := (archimed ``x/y``); Rewrite <- Z_R_minus; Simpl; Cut ``0<y``.
Intro; Unfold Rminus; Replace ``-(((IZR (up (x/y)))+ -1)*y)`` with ``(1-(IZR (up (x/y))))*y``; [Idtac | Ring].
Split.
Apply Rle_monotony_contra with ``/y``.
Apply Rlt_Rinv; Assumption.
Rewrite Rmult_Or; Rewrite (Rmult_sym ``/y``); Rewrite Rmult_Rplus_distrl; Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1r | Assumption]; Apply Rle_anti_compatibility with ``(IZR (up (x/y)))-x/y``; Rewrite Rplus_Or; Unfold Rdiv; Replace ``(IZR (up (x*/y)))-x*/y+(x*/y+(1-(IZR (up (x*/y)))))`` with R1; [Idtac | Ring]; Elim H0; Intros _ H2; Unfold Rdiv in H2; Exact H2.
Rewrite (Rabsolu_right ? r); Apply Rlt_monotony_contra with ``/y``.
Apply Rlt_Rinv; Assumption.
Rewrite <- (Rinv_l_sym ? H); Rewrite (Rmult_sym ``/y``); Rewrite Rmult_Rplus_distrl; Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1r | Assumption]; Apply Rlt_anti_compatibility with ``((IZR (up (x/y)))-1)``; Replace ``(IZR (up (x/y)))-1+1`` with ``(IZR (up (x/y)))``; [Idtac | Ring]; Replace ``(IZR (up (x/y)))-1+(x*/y+(1-(IZR (up (x/y)))))`` with ``x*/y``; [Idtac | Ring]; Elim H0; Unfold Rdiv; Intros H2 _; Exact H2.
Case (total_order_T R0 y); Intro.
Elim s; Intro.
Assumption.
Elim H; Symmetry; Exact b.
Assert H1 := (Rle_sym2 ? ? r); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H1 r0)).
Qed.

Lemma tech8 : (n,i:nat) (le n (plus (S n) i)).
Intros; Induction i.
Replace (plus (S n) O) with (S n); [Apply le_n_Sn | Ring].
Replace (plus (S n) (S i)) with (S (plus (S n) i)).
Apply le_S; Assumption.
Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Qed.
