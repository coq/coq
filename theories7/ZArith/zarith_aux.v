(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

Require Export BinInt.
Require Export Zcompare.
Require Export Zorder.
Require Export Zmin.
Require Export Zabs.

V7only [
Notation Zlt := Zlt.
Notation Zgt := Zgt.
Notation Zle := Zle.
Notation Zge := Zge.
Notation Zsgn := Zsgn.
Notation absolu := absolu.
Notation Zabs := Zabs.
Notation Zabs_eq := Zabs_eq.
Notation Zabs_non_eq := Zabs_non_eq.
Notation Zabs_dec := Zabs_dec.
Notation Zabs_pos := Zabs_pos.
Notation Zsgn_Zabs := Zsgn_Zabs.
Notation Zabs_Zsgn := Zabs_Zsgn.
Notation inject_nat := inject_nat.
Notation Zs := Zs.
Notation Zpred := Zpred.
Notation Zgt_Sn_n := Zgt_Sn_n.
Notation Zle_gt_trans := Zle_gt_trans.
Notation Zgt_le_trans := Zgt_le_trans.
Notation Zle_S_gt := Zle_S_gt.
Notation Zcompare_n_S := Zcompare_n_S.
Notation Zgt_n_S := Zgt_n_S.
Notation Zle_not_gt := Zle_not_gt.
Notation Zgt_antirefl := Zgt_antirefl.
Notation Zgt_not_sym := Zgt_not_sym.
Notation Zgt_not_le := Zgt_not_le.
Notation Zgt_trans := Zgt_trans.
Notation Zle_gt_S := Zle_gt_S.
Notation Zgt_pred := Zgt_pred.       
Notation Zsimpl_gt_plus_l := Zsimpl_gt_plus_l. 
Notation Zsimpl_gt_plus_r := Zsimpl_gt_plus_r.
Notation Zgt_reg_l := Zgt_reg_l.      
Notation Zgt_reg_r := Zgt_reg_r.
Notation Zcompare_et_un := Zcompare_et_un.
Notation Zgt_S_n := Zgt_S_n.
Notation Zle_S_n := Zle_S_n.
Notation Zgt_le_S := Zgt_le_S.
Notation Zgt_S_le := Zgt_S_le.
Notation Zgt_S := Zgt_S.
Notation Zgt_trans_S := Zgt_trans_S.
Notation Zeq_S := Zeq_S.
Notation Zpred_Sn := Zpred_Sn.
Notation Zeq_add_S := Zeq_add_S.
Notation Znot_eq_S := Znot_eq_S.
Notation Zsimpl_plus_l := Zsimpl_plus_l.
Notation Zn_Sn := Zn_Sn.
Notation Zplus_n_O := Zplus_n_O.
Notation Zplus_unit_left := Zplus_unit_left.
Notation Zplus_unit_right := Zplus_unit_right.
Notation Zplus_n_Sm := Zplus_n_Sm.
Notation Zmult_n_O := Zmult_n_O.
Notation Zmult_n_Sm := Zmult_n_Sm.
Notation Zle_n := Zle_n.
Notation Zle_refl := Zle_refl.
Notation Zle_trans := Zle_trans.
Notation Zle_n_Sn := Zle_n_Sn.
Notation Zle_n_S := Zle_n_S.
Notation Zs_pred := Zs_pred. (* BinInt *)
Notation Zle_pred_n := Zle_pred_n.
Notation Zle_trans_S := Zle_trans_S.
Notation Zle_Sn_n := Zle_Sn_n.
Notation Zle_antisym := Zle_antisym.
Notation Zgt_lt := Zgt_lt.
Notation Zlt_gt := Zlt_gt.
Notation Zge_le := Zge_le.
Notation Zle_ge := Zle_ge.
Notation Zge_trans := Zge_trans.
Notation Zlt_n_Sn := Zlt_n_Sn.
Notation Zlt_S := Zlt_S.
Notation Zlt_n_S := Zlt_n_S.
Notation Zlt_S_n := Zlt_S_n.
Notation Zlt_n_n := Zlt_n_n.
Notation Zlt_pred := Zlt_pred.
Notation Zlt_pred_n_n := Zlt_pred_n_n.
Notation Zlt_le_S := Zlt_le_S.
Notation Zlt_n_Sm_le := Zlt_n_Sm_le.
Notation Zle_lt_n_Sm := Zle_lt_n_Sm.
Notation Zlt_le_weak := Zlt_le_weak.
Notation Zlt_trans := Zlt_trans.
Notation Zlt_le_trans := Zlt_le_trans.
Notation Zle_lt_trans := Zle_lt_trans.
Notation Zle_lt_or_eq := Zle_lt_or_eq.
Notation Zle_or_lt := Zle_or_lt.
Notation Zle_not_lt := Zle_not_lt.
Notation Zlt_not_le := Zlt_not_le.
Notation Zlt_not_sym := Zlt_not_sym.
Notation Zle_le_S := Zle_le_S.
Notation Zmin := Zmin.
Notation Zmin_SS := Zmin_SS.
Notation Zle_min_l := Zle_min_l.
Notation Zle_min_r := Zle_min_r.
Notation Zmin_case := Zmin_case.
Notation Zmin_or := Zmin_or.
Notation Zmin_n_n := Zmin_n_n.
Notation Zplus_assoc_l := Zplus_assoc_l.
Notation Zplus_assoc_r := Zplus_assoc_r.
Notation Zplus_permute := Zplus_permute.
Notation Zsimpl_le_plus_l := Zsimpl_le_plus_l.
Notation "'Zsimpl_le_plus_l' c" := [a,b:Z](Zsimpl_le_plus_l a b c)
  (at level 10, c at next level).
Notation "'Zsimpl_le_plus_l' c a" := [b:Z](Zsimpl_le_plus_l a b c)
  (at level 10, a, c at next level).
Notation "'Zsimpl_le_plus_l' c a b" := (Zsimpl_le_plus_l a b c)
  (at level 10, a, b, c at next level).
Notation Zsimpl_le_plus_r := Zsimpl_le_plus_r.
Notation "'Zsimpl_le_plus_r' c" := [a,b:Z](Zsimpl_le_plus_r a b c)
  (at level 10, c at next level).
Notation "'Zsimpl_le_plus_r' c a" := [b:Z](Zsimpl_le_plus_r a b c)
  (at level 10, a, c at next level).
Notation "'Zsimpl_le_plus_r' c a b" := (Zsimpl_le_plus_r a b c)
  (at level 10, a, b, c at next level).
Notation Zle_reg_l := Zle_reg_l.
Notation Zle_reg_r := Zle_reg_r.
Notation Zle_plus_plus := Zle_plus_plus.
Notation Zplus_Snm_nSm := Zplus_Snm_nSm.
Notation Zsimpl_lt_plus_l := Zsimpl_lt_plus_l. 
Notation Zsimpl_lt_plus_r := Zsimpl_lt_plus_r.
Notation Zlt_reg_l := Zlt_reg_l.
Notation Zlt_reg_r := Zlt_reg_r.
Notation Zlt_le_reg := Zlt_le_reg.
Notation Zle_lt_reg := Zle_lt_reg.
Notation Zminus := Zminus.
Notation Zminus_plus_simpl := Zminus_plus_simpl.
Notation Zminus_n_O := Zminus_n_O.
Notation Zminus_n_n := Zminus_n_n.
Notation Zplus_minus := Zplus_minus.
Notation Zminus_plus := Zminus_plus.
Notation Zle_plus_minus := Zle_plus_minus.
Notation Zminus_Sn_m := Zminus_Sn_m.
Notation Zlt_minus := Zlt_minus.
Notation Zlt_O_minus_lt := Zlt_O_minus_lt.
Notation Zmult_plus_distr_l := Zmult_plus_distr_l.
Notation Zmult_plus_distr := BinInt.Zmult_plus_distr_l.
Notation Zmult_minus_distr := Zmult_minus_distr.
Notation Zmult_assoc_r := Zmult_assoc_r.
Notation Zmult_assoc_l := Zmult_assoc_l.
Notation Zmult_permute := Zmult_permute.
Notation Zmult_1_n := Zmult_1_n.
Notation Zmult_n_1 := Zmult_n_1.
Notation Zmult_Sm_n := Zmult_Sm_n.
Notation Zmult_Zplus_distr := Zmult_plus_distr_r.
Export BinInt.
Export Zorder.
Export Zmin.
Export Zabs.
Export Zcompare.
].
