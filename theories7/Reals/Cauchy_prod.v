(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Rseries.
Require PartSum.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

(**********)
Lemma sum_N_predN : (An:nat->R;N:nat) (lt O N) -> (sum_f_R0 An N)==``(sum_f_R0 An (pred N)) + (An N)``.
Intros.
Replace N with (S (pred N)).
Rewrite tech5.
Reflexivity.
Symmetry; Apply S_pred with O; Assumption.
Qed.

(**********)
Lemma sum_plus : (An,Bn:nat->R;N:nat) (sum_f_R0 [l:nat]``(An l)+(Bn l)`` N)==``(sum_f_R0 An N)+(sum_f_R0 Bn N)``.
Intros.
Induction N.
Reflexivity.
Do 3 Rewrite tech5.
Rewrite HrecN; Ring.
Qed.

(* The main result *)
Theorem cauchy_finite : (An,Bn:nat->R;N:nat) (lt O N) -> (Rmult (sum_f_R0 An N) (sum_f_R0 Bn N)) == (Rplus (sum_f_R0 [k:nat](sum_f_R0 [p:nat]``(An p)*(Bn (minus k p))`` k) N) (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (plus l k)))*(Bn (minus N l))`` (pred (minus N k))) (pred N))). 
Intros; Induction N.
Elim (lt_n_n ? H).
Cut N=O\/(lt O N).
Intro; Elim H0; Intro.
Rewrite H1; Simpl; Ring.
Replace (pred (S N)) with (S (pred N)).
Do 5 Rewrite tech5.
Rewrite Rmult_Rplus_distrl; Rewrite Rmult_Rplus_distr; Rewrite (HrecN H1).
Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Replace (pred (minus (S N) (S (pred N)))) with (O).
Rewrite Rmult_Rplus_distr; Replace (sum_f_R0 [l:nat]``(An (S (plus l (S (pred N)))))*(Bn (minus (S N) l))`` O) with ``(An (S N))*(Bn (S N))``.
Repeat Rewrite <- Rplus_assoc; Do 2 Rewrite <- (Rplus_sym ``(An (S N))*(Bn (S N))``); Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Rewrite <- minus_n_n; Cut N=(1)\/(le (2) N).
Intro; Elim H2; Intro.
Rewrite H3; Simpl; Ring.
Replace (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (plus l k)))*(Bn (minus N l))`` (pred (minus N k))) (pred N)) with (Rplus (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (pred (minus N k)))) (pred (pred N))) (sum_f_R0 [l:nat]``(An (S l))*(Bn (minus N l))`` (pred N))).
Replace (sum_f_R0 [p:nat]``(An p)*(Bn (minus (S N) p))`` N) with (Rplus (sum_f_R0 [l:nat]``(An (S l))*(Bn (minus N l))`` (pred N)) ``(An O)*(Bn (S N))``).
Repeat Rewrite <- Rplus_assoc; Rewrite <- (Rplus_sym (sum_f_R0 [l:nat]``(An (S l))*(Bn (minus N l))`` (pred N))); Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Replace (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (plus l k)))*(Bn (minus (S N) l))`` (pred (minus (S N) k))) (pred N)) with (Rplus (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) (pred N)) (Rmult (Bn (S N)) (sum_f_R0 [l:nat](An (S l)) (pred N)))).
Rewrite (decomp_sum An N H1); Rewrite Rmult_Rplus_distrl; Repeat Rewrite <- Rplus_assoc; Rewrite <- (Rplus_sym ``(An O)*(Bn (S N))``); Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Repeat Rewrite <- Rplus_assoc; Rewrite <- (Rplus_sym (Rmult (sum_f_R0 [i:nat](An (S i)) (pred N)) (Bn (S N)))); Rewrite <- (Rplus_sym (Rmult (Bn (S N)) (sum_f_R0 [i:nat](An (S i)) (pred N)))); Rewrite (Rmult_sym (Bn (S N))); Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Replace (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) (pred N)) with (Rplus (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (pred (minus N k)))) (pred (pred N))) (Rmult (An (S N)) (sum_f_R0 [l:nat](Bn (S l)) (pred N)))).
Rewrite (decomp_sum Bn N H1); Rewrite Rmult_Rplus_distr.
Pose Z := (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (pred (minus N k)))) (pred (pred N))); Pose Z2 := (sum_f_R0 [i:nat](Bn (S i)) (pred N)); Ring.
Rewrite (sum_N_predN [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) (pred N)).
Replace (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) (pred (pred N))) with (sum_f_R0 [k:nat](Rplus (sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (pred (minus N k)))) ``(An (S N))*(Bn (S k))``) (pred (pred N))).
Rewrite (sum_plus [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (pred (minus N k)))) [k:nat]``(An (S N))*(Bn (S k))`` (pred (pred N))).
Repeat Rewrite Rplus_assoc; Apply Rplus_plus_r.
Replace (pred (minus N (pred N))) with O.
Simpl; Rewrite <- minus_n_O.
Replace (S (pred N)) with N.
Replace (sum_f_R0 [k:nat]``(An (S N))*(Bn (S k))`` (pred (pred N))) with (sum_f_R0 [k:nat]``(Bn (S k))*(An (S N))`` (pred (pred N))).
Rewrite <- (scal_sum [l:nat](Bn (S l)) (pred (pred N)) (An (S N))); Rewrite (sum_N_predN [l:nat](Bn (S l)) (pred N)).
Replace (S (pred N)) with N.
Ring.
Apply S_pred with O; Assumption.
Apply lt_pred; Apply lt_le_trans with (2); [Apply lt_n_Sn | Assumption].
Apply sum_eq; Intros; Apply Rmult_sym.
Apply S_pred with O; Assumption.
Replace (minus N (pred N)) with (1).
Reflexivity.
Pattern 1 N; Replace N with (S (pred N)).
Rewrite <- minus_Sn_m.
Rewrite <- minus_n_n; Reflexivity.
Apply le_n.
Symmetry; Apply S_pred with O; Assumption.
Apply sum_eq; Intros; Rewrite (sum_N_predN [l:nat]``(An (S (S (plus l i))))*(Bn (minus N l))`` (pred (minus N i))).
Replace (S (S (plus (pred (minus N i)) i))) with (S N).
Replace (minus N (pred (minus N i))) with (S i).
Ring.
Rewrite pred_of_minus; Apply INR_eq; Repeat Rewrite minus_INR.
Rewrite S_INR; Ring.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply INR_le; Rewrite minus_INR.
Apply Rle_anti_compatibility with ``(INR i)-1``.
Replace ``(INR i)-1+(INR (S O))`` with (INR i); [Idtac | Ring].
Replace ``(INR i)-1+((INR N)-(INR i))`` with ``(INR N)-(INR (S O))``; [Idtac | Ring].
Rewrite <- minus_INR.
Apply le_INR; Apply le_trans with (pred (pred N)).
Assumption.
Rewrite <- pred_of_minus; Apply le_pred_n.
Apply le_trans with (2).
Apply le_n_Sn.
Assumption.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Rewrite <- pred_of_minus.
Apply le_trans with (pred N).
Apply le_S_n.
Replace (S (pred N)) with N.
Replace (S (pred (minus N i))) with (minus N i).
Apply simpl_le_plus_l with i; Rewrite le_plus_minus_r.
Apply le_plus_r.
Apply le_trans with (pred (pred N)); [Assumption | Apply le_trans with (pred N); Apply le_pred_n].
Apply S_pred with O.
Apply simpl_lt_plus_l with i; Rewrite le_plus_minus_r.
Replace (plus i O) with i; [Idtac | Ring].
Apply le_lt_trans with (pred (pred N)); [Assumption | Apply lt_trans with (pred N); Apply lt_pred_n_n].
Apply lt_S_n.
Replace (S (pred N)) with N.
Apply lt_le_trans with (2).
Apply lt_n_Sn.
Assumption.
Apply S_pred with O; Assumption.
Assumption.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply S_pred with O; Assumption.
Apply le_pred_n.
Apply INR_eq; Rewrite pred_of_minus; Do 3 Rewrite S_INR; Rewrite plus_INR; Repeat Rewrite minus_INR.
Ring.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply INR_le.
Rewrite minus_INR.
Apply Rle_anti_compatibility with ``(INR i)-1``.
Replace ``(INR i)-1+(INR (S O))`` with (INR i); [Idtac | Ring].
Replace ``(INR i)-1+((INR N)-(INR i))`` with ``(INR N)-(INR (S O))``; [Idtac | Ring].
Rewrite <- minus_INR.
Apply le_INR.
Apply le_trans with (pred (pred N)).
Assumption.
Rewrite <- pred_of_minus.
Apply le_pred_n.
Apply le_trans with (2).
Apply le_n_Sn.
Assumption.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply lt_le_trans with (1).
Apply lt_O_Sn.
Apply INR_le.
Rewrite pred_of_minus.
Repeat Rewrite minus_INR.
Apply Rle_anti_compatibility with ``(INR i)-1``.
Replace ``(INR i)-1+(INR (S O))`` with (INR i); [Idtac | Ring].
Replace ``(INR i)-1+((INR N)-(INR i)-(INR (S O)))`` with ``(INR N)-(INR (S O)) -(INR (S O))``.
Repeat Rewrite <- minus_INR.
Apply le_INR.
Apply le_trans with (pred (pred N)).
Assumption.
Do 2 Rewrite <- pred_of_minus.
Apply le_n.
Apply simpl_le_plus_l with (1).
Rewrite le_plus_minus_r.
Simpl; Assumption.
Apply le_trans with (2); [Apply le_n_Sn | Assumption].
Apply le_trans with (2); [Apply le_n_Sn | Assumption].
Ring.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply simpl_le_plus_l with i.
Rewrite le_plus_minus_r.
Replace (plus i (1)) with (S i).
Replace N with (S (pred N)).
Apply le_n_S.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_pred_n.
Symmetry; Apply S_pred with O; Assumption.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Reflexivity.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply lt_le_trans with (1).
Apply lt_O_Sn.
Apply le_S_n.
Replace (S (pred N)) with N.
Assumption.
Apply S_pred with O; Assumption.
Replace (sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(An (S (plus l k)))*(Bn (minus (S N) l))`` (pred (minus (S N) k))) (pred N)) with (sum_f_R0 [k:nat](Rplus (sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) ``(An (S k))*(Bn (S N))``) (pred N)).
Rewrite (sum_plus [k:nat](sum_f_R0 [l:nat]``(An (S (S (plus l k))))*(Bn (minus N l))`` (pred (minus N k))) [k:nat]``(An (S k))*(Bn (S N))``).
Apply Rplus_plus_r.
Rewrite scal_sum; Reflexivity.
Apply sum_eq; Intros; Rewrite Rplus_sym; Rewrite (decomp_sum [l:nat]``(An (S (plus l i)))*(Bn (minus (S N) l))`` (pred (minus (S N) i))).
Replace (plus O i) with i; [Idtac | Ring].
Rewrite <- minus_n_O; Apply Rplus_plus_r.
Replace (pred (pred (minus (S N) i))) with (pred (minus N i)).
Apply sum_eq; Intros.
Replace (minus (S N) (S i0)) with (minus N i0); [Idtac | Reflexivity].
Replace (plus (S i0) i) with (S (plus i0 i)).
Reflexivity.
Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite S_INR; Ring.
Cut (minus N i)=(pred (minus (S N) i)).
Intro; Rewrite H5; Reflexivity.
Rewrite pred_of_minus.
Apply INR_eq; Repeat Rewrite minus_INR.
Rewrite S_INR; Ring.
Apply le_trans with N.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply simpl_le_plus_l with i.
Rewrite le_plus_minus_r.
Replace (plus i (1)) with (S i).
Apply le_n_S.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_trans with N.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Replace (pred (minus (S N) i)) with (minus (S N) (S i)).
Replace (minus (S N) (S i)) with (minus N i); [Idtac | Reflexivity].
Apply simpl_lt_plus_l with i.
Rewrite le_plus_minus_r.
Replace (plus i O) with i; [Idtac | Ring].
Apply le_lt_trans with (pred N).
Assumption.
Apply lt_pred_n_n.
Assumption.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Rewrite pred_of_minus.
Apply INR_eq; Repeat Rewrite minus_INR.
Repeat Rewrite S_INR; Ring.
Apply le_trans with N.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply simpl_le_plus_l with i.
Rewrite le_plus_minus_r.
Replace (plus i (1)) with (S i).
Apply le_n_S.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_trans with N.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Apply le_n_Sn.
Apply le_n_S.
Apply le_trans with (pred N).
Assumption.
Apply le_pred_n.
Rewrite Rplus_sym.
Rewrite (decomp_sum [p:nat]``(An p)*(Bn (minus (S N) p))`` N).
Rewrite <- minus_n_O.
Apply Rplus_plus_r.
Apply sum_eq; Intros.
Reflexivity.
Assumption.
Rewrite Rplus_sym.
Rewrite (decomp_sum [k:nat](sum_f_R0 [l:nat]``(An (S (plus l k)))*(Bn (minus N l))`` (pred (minus N k))) (pred N)).
Rewrite <- minus_n_O.
Replace (sum_f_R0 [l:nat]``(An (S (plus l O)))*(Bn (minus N l))`` (pred N)) with (sum_f_R0 [l:nat]``(An (S l))*(Bn (minus N l))`` (pred N)).
Apply Rplus_plus_r.
Apply sum_eq; Intros.
Replace (pred (minus N (S i))) with (pred (pred (minus N i))).
Apply sum_eq; Intros.
Replace (plus i0 (S i)) with (S (plus i0 i)).
Reflexivity.
Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Rewrite S_INR; Ring.
Cut (pred (minus N i))=(minus N (S i)).
Intro; Rewrite H5; Reflexivity.
Rewrite pred_of_minus.
Apply INR_eq.
Repeat Rewrite minus_INR.
Repeat Rewrite S_INR; Ring.
Apply le_trans with (S (pred (pred N))).
Apply le_n_S; Assumption.
Replace (S (pred (pred N))) with (pred N).
Apply le_pred_n.
Apply S_pred with O.
Apply lt_S_n.
Replace (S (pred N)) with N.
Apply lt_le_trans with (2).
Apply lt_n_Sn.
Assumption.
Apply S_pred with O; Assumption.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply simpl_le_plus_l with i.
Rewrite le_plus_minus_r.
Replace (plus i (1)) with (S i).
Replace N with (S (pred N)).
Apply le_n_S.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_pred_n.
Symmetry; Apply S_pred with O; Assumption.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Ring.
Apply le_trans with (pred (pred N)).
Assumption.
Apply le_trans with (pred N); Apply le_pred_n.
Apply sum_eq; Intros.
Replace (plus i O) with i; [Reflexivity | Trivial].
Apply lt_S_n.
Replace (S (pred N)) with N.
Apply lt_le_trans with (2); [Apply lt_n_Sn | Assumption].
Apply S_pred with O; Assumption.
Inversion H1.
Left; Reflexivity.
Right; Apply le_n_S; Assumption.
Simpl.
Replace (S (pred N)) with N.
Reflexivity.
Apply S_pred with O; Assumption.
Simpl.
Cut (minus N (pred N))=(1).
Intro; Rewrite H2; Reflexivity.
Rewrite pred_of_minus.
Apply INR_eq; Repeat Rewrite minus_INR.
Ring.
Apply lt_le_S; Assumption.
Rewrite <- pred_of_minus; Apply le_pred_n.
Simpl; Symmetry; Apply S_pred with O; Assumption.
Inversion H.
Left; Reflexivity.
Right; Apply lt_le_trans with (1); [Apply lt_n_Sn | Exact H1].
Qed.
