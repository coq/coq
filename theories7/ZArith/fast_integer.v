(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(***********************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)
(***********************************************************)

Require BinPos.
Require BinNat.
Require BinInt.
Require Zcompare.
Require Mult.

V7only [
(* Defs and ppties on positive, entier and Z, previously in fast_integer *)
(* For v7 compatibility *)
Notation positive := positive.
Notation xO := xO.
Notation xI := xI.
Notation xH := xH.
Notation add_un := add_un.
Notation add := add.
Notation convert := convert.
Notation convert_add_un := convert_add_un.
Notation cvt_carry := cvt_carry.
Notation convert_add := convert_add.
Notation positive_to_nat := positive_to_nat.
Notation anti_convert := anti_convert.
Notation double_moins_un := double_moins_un.
Notation sub_un := sub_un.
Notation positive_mask := positive_mask.
Notation Un_suivi_de_mask := Un_suivi_de_mask.
Notation Zero_suivi_de_mask := Zero_suivi_de_mask.
Notation double_moins_deux := double_moins_deux.
Notation sub_pos := sub_pos.
Notation true_sub := true_sub.
Notation times := times.
Notation relation := relation.
Notation SUPERIEUR := SUPERIEUR.
Notation INFERIEUR := INFERIEUR.
Notation EGAL := EGAL.
Notation Op := Op.
Notation compare := compare.
Notation compare_convert1 := compare_convert1.
Notation compare_convert_EGAL := compare_convert_EGAL.
Notation ZLSI := ZLSI.
Notation ZLIS := ZLIS.
Notation ZLII := ZLII.
Notation ZLSS := ZLSS.
Notation Dcompare := Dcompare.
Notation convert_compare_EGAL := convert_compare_EGAL.
Notation ZL0 := ZL0.
Notation ZL11 := ZL11.
Notation xI_add_un_xO := xI_add_un_xO.
Notation is_double_moins_un := is_double_moins_un.
Notation double_moins_un_add_un_xI := double_moins_un_add_un_xI.
Notation ZL1 := ZL1.
Notation add_un_not_un := add_un_not_un.
Notation sub_add_one := sub_add_one.
Notation add_sub_one := add_sub_one.
Notation add_un_inj := add_un_inj.
Notation ZL12 := ZL12.
Notation ZL12bis := ZL12bis.
Notation ZL13 := ZL13.
Notation add_sym := add_sym.
Notation ZL14 := ZL14.
Notation ZL14bis := ZL14bis.
Notation ZL15 := ZL15.
Notation add_no_neutral := add_no_neutral.
Notation add_carry_not_add_un := add_carry_not_add_un.
Notation add_carry_add := add_carry_add.
Notation simpl_add_r := simpl_add_r.
Notation simpl_add_carry_r := simpl_add_carry_r.
Notation simpl_add_l := simpl_add_l.
Notation simpl_add_carry_l := simpl_add_carry_l.
Notation add_assoc := add_assoc.
Notation add_xI_double_moins_un := add_xI_double_moins_un.
Notation add_x_x := add_x_x.
Notation ZS := ZS.
Notation US := US.
Notation USH := USH.
Notation ZSH := ZSH.
Notation sub_pos_x_x := sub_pos_x_x.
Notation ZL10 := ZL10.
Notation sub_pos_SUPERIEUR := sub_pos_SUPERIEUR.
Notation sub_add := sub_add.
Notation convert_add_carry := convert_add_carry.
Notation add_verif := add_verif.
Notation ZL2 := ZL2.
Notation ZL6 := ZL6.
Notation positive_to_nat_mult := positive_to_nat_mult.
Notation times_convert := times_convert.
Notation compare_positive_to_nat_O := compare_positive_to_nat_O.
Notation compare_convert_O := compare_convert_O.
Notation convert_xH := convert_xH.
Notation convert_xO := convert_xO.
Notation convert_xI := convert_xI.
Notation bij1 := bij1.
Notation ZL3 := ZL3.
Notation ZL4 := ZL4.
Notation ZL5 := ZL5.
Notation bij2 := bij2.
Notation bij3 := bij3.
Notation ZL7 := ZL7.
Notation ZL8 := ZL8.
Notation compare_convert_INFERIEUR := compare_convert_INFERIEUR.
Notation compare_convert_SUPERIEUR := compare_convert_SUPERIEUR.
Notation convert_compare_INFERIEUR := convert_compare_INFERIEUR.
Notation convert_compare_SUPERIEUR := convert_compare_SUPERIEUR.
Notation ZC1 := ZC1.
Notation ZC2 := ZC2.
Notation ZC3 := ZC3.
Notation ZC4 := ZC4.
Notation true_sub_convert := true_sub_convert.
Notation convert_intro := convert_intro.
Notation ZL16 := ZL16.
Notation ZL17 := ZL17.
Notation compare_true_sub_right := compare_true_sub_right.
Notation compare_true_sub_left := compare_true_sub_left.
Notation times_x_ := times_x_1.
Notation times_x_double := times_x_double.
Notation times_x_double_plus_one := times_x_double_plus_one.
Notation times_sym := times_sym.
Notation times_add_distr := times_add_distr.
Notation times_add_distr_l := times_add_distr_l.
Notation times_assoc := times_assoc.
Notation times_true_sub_distr := times_true_sub_distr.
Notation times_discr_xO_xI := times_discr_xO_xI.
Notation times_discr_xO := times_discr_xO.
Notation simpl_times_r := simpl_times_r.
Notation simpl_times_l := simpl_times_l.
Notation iterate_add := iterate_add.
Notation entier := entier.
Notation Nul := Nul.
Notation Pos := Pos.
Notation Un_suivi_de := Un_suivi_de.
Notation Zero_suivi_de := Zero_suivi_de.
Notation times1 :=
    [x:positive;_:positive->positive;y:positive](times x y).
Notation times1_convert :=
    [x,y:positive;_:positive->positive](times_convert x y).

Notation Z := Z.
Notation POS := POS.
Notation NEG := NEG.
Notation ZERO := ZERO.
Notation Zero_left := Zero_left.
Notation Zopp_Zopp := Zopp_Zopp.
Notation Zero_right := Zero_right.
Notation Zplus_inverse_r := Zplus_inverse_r.
Notation Zopp_Zplus := Zopp_Zplus.
Notation Zplus_sym := Zplus_sym.
Notation Zplus_inverse_l := Zplus_inverse_l.
Notation Zopp_intro := Zopp_intro.
Notation Zopp_NEG := Zopp_NEG.
Notation weak_assoc := weak_assoc.
Notation Zplus_assoc := Zplus_assoc.
Notation Zplus_simpl := Zplus_simpl.
Notation Zmult_sym := Zmult_sym.
Notation Zmult_assoc := Zmult_assoc.
Notation Zmult_one := Zmult_one.
Notation lt_mult_left := lt_mult_left. (* Mult*)
Notation Zero_mult_left := Zero_mult_left.
Notation Zero_mult_right := Zero_mult_right.
Notation Zopp_Zmult := Zopp_Zmult.
Notation Zmult_Zopp_Zopp := Zmult_Zopp_Zopp.
Notation weak_Zmult_plus_distr_r := weak_Zmult_plus_distr_r.
Notation Zmult_plus_distr_r := Zmult_plus_distr_r.
Notation Zcompare_EGAL := Zcompare_EGAL.
Notation Zcompare_ANTISYM := Zcompare_ANTISYM.
Notation le_minus := le_minus.
Notation Zcompare_Zopp := Zcompare_Zopp.
Notation weaken_Zcompare_Zplus_compatible := weaken_Zcompare_Zplus_compatible.
Notation weak_Zcompare_Zplus_compatible := weak_Zcompare_Zplus_compatible.
Notation Zcompare_Zplus_compatible := Zcompare_Zplus_compatible.
Notation Zcompare_trans_SUPERIEUR := Zcompare_trans_SUPERIEUR.
Notation SUPERIEUR_POS := SUPERIEUR_POS.
Export Datatypes.
Export BinPos.
Export BinNat.
Export BinInt.
Export Zcompare.
Export Mult.
].
