(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Univ
open Names
open Nameops
open Term
open Termops
open Inductive
open Sign
open Environ
open Libnames
open Impargs
open Topconstr
open Rawterm
open Pattern
open Nametab
open Symbols
open Reserve
(*i*)

(* Translation from rawconstr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   prefixed by "!" otherwise the function and not the arguments is
   prefixed by "!" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing universe names of Type{.} *)
let print_universes = ref false

(* This suppresses printing of numeral and symbols *)
let print_no_symbol = ref false

(* This governs printing of projections using the dot notation symbols *)
let print_projections = ref false

let print_meta_as_hole = ref false

let with_arguments f = Options.with_option print_arguments f
let with_implicits f = Options.with_option print_implicits f
let with_coercions f = Options.with_option print_coercions f
let with_universes f = Options.with_option print_universes f
let without_symbols f = Options.with_option print_no_symbol f
let with_meta_as_hole f = Options.with_option print_meta_as_hole f

(* For the translator *)
let temporary_implicits_out = ref []
let set_temporary_implicits_out l = temporary_implicits_out := l
let get_temporary_implicits_out id =
  try List.assoc id !temporary_implicits_out
  with Not_found -> []

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (dummy_loc,sc,e)

let insert_pat_delimiters e = function
  | None -> e
  | Some sc -> CPatDelimiters (dummy_loc,sc,e)

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
       error
       "Termast: arbitrary substitution of references not yet implemented")
     ctxt)

let idopt_of_name = function 
  | Name id -> Some id
  | Anonymous -> None

let extern_evar loc n =
(*
  msgerrnl (str 
    "Warning: existential variable turned into meta-variable during externalization");
  CPatVar (loc,(false,make_ident "META" (Some n)))
*)
  CEvar (loc,n)

let raw_string_of_ref = function
  | ConstRef kn -> 
      "CONST("^(string_of_kn kn)^")"
  | IndRef (kn,i) ->
      "IND("^(string_of_kn kn)^","^(string_of_int i)^")"
  | ConstructRef ((kn,i),j) -> 
      "CONSTRUCT("^
      (string_of_kn kn)^","^(string_of_int i)^","^(string_of_int j)^")"
  | VarRef id -> 
      "SECVAR("^(string_of_id id)^")"

(* v7->v8 translation *)

let name_app f = function
  | Name id -> Name (f id)
  | Anonymous -> Anonymous

let avoid_wildcard_string s =
  if s = "_" then "x_" else s

let avoid_wildcard id =
  if id = id_of_string "_" then id_of_string "x_" else id

let translate_keyword = function
  | ("forall" | "fun" | "match" | "fix" | "cofix" | "for" | "let"
    | "if"  | "then" | "else" | "return" | "mod" | "where" | "exists" as s) ->
      let s' = s^"_" in
      msgerrnl
      (str ("Warning: '"^
          s^"' is now a keyword; it has been translated to '"^s'^"'"));
      s'
  | s -> s

let is_coq_root d =
  let d = repr_dirpath d in d <> [] & string_of_id (list_last d) = "Coq"

let is_dir dir s =
  let d = repr_dirpath dir in
  d <> [] & string_of_id (List.hd d) = s

let is_module m = is_dir (Lib.library_dp()) m

let translate_v7_string dir = function
  (* ZArith *)
  | "double_moins_un" -> "Pdouble_minus_one"
  | "double_moins_deux" -> "Pdouble_minus_two"
  | "double_moins_un_add_un" -> "xI_eq_double_minus_one_succ"
  | "add_un_double_moins_un_xO" -> "Psucc_double_minus_one_eq_xO"
  | "add_un_Zs" -> "Zpos_succ_morphism"
  | "entier" -> "N"
  | "entier_of_Z" -> "Zabs_N"
  | "Z_of_entier" -> "Z_of_N"
  | "SUPERIEUR" -> "Gt"
  | "EGAL" -> "Eq"
  | "INFERIEUR" -> "Lt"
  | "add" -> "Pplus"
  | "add_carry" -> "Pplus_carry"
  | "add_assoc" -> "Pplus_assoc"
  | "add_sym" -> "Pplus_comm"
  | "add_x_x" -> "Pplus_diag"
  | "add_carry_add" -> "Pplus_carry_plus"
  | "simpl_add_r" -> "Pplus_reg_r"
  | "simpl_add_l" -> "Pplus_reg_l"
  | "simpl_add_carry_r" -> "Pplus_carry_reg_r"
  | "simpl_add_carry_l" -> "Pplus_carry_reg_l"
  | "simpl_times_r" -> "Pmult_reg_r"
  | "simpl_times_l" -> "Pmult_reg_l"
(*
  | "xO_xI_add_double_moins_un" -> "xO_xI_plus_double_minus_one"
*)
  | "double_moins_un_plus_xO_double_moins_un" ->
      "Pdouble_minus_one_plus_xO_double_minus_one"
  | "add_xI_double_moins_un" -> "Pplus_xI_double_minus_one"
  | "add_xO_double_moins_un" -> "Pplus_xO_double_minus_one"
  | "iter_pos_add" -> "iter_pos_plus"
  | "add_no_neutral" -> "Pplus_no_neutral"
  | "add_carry_not_add_un" -> "Pplus_carry_no_neutral"
  | "times" when not (is_module "Mapfold") -> "Pmult"
  | "times_add_distr" -> "Pmult_plus_distr_l"
  | "times_add_distr_l" -> "Pmult_plus_distr_r"
  | "times_true_sub_distr" -> "Pmult_minus_distr_l"
  | "times_sym" -> "Pmult_comm"
  | "times_assoc" -> "Pmult_assoc"
  | "times_convert" -> "nat_of_P_mult_morphism"
  | "true_sub" -> "Pminus"
  | "times_x_1" -> "Pmult_1_r"
  | "times_x_double" -> "Pmult_xO_permute_r"
  | "times_x_double_plus_one" -> "Pmult_xI_permute_r"
  | "times_discr_xO_xI" -> "Pmult_xI_mult_xO_discr"
  | "times_discr_xO" -> "Pmult_xO_discr"
  | "true_sub_convert" -> "nat_of_P_minus_morphism"
  | "compare_true_sub_right" -> "Pcompare_minus_r"
  | "compare_true_sub_left" -> "Pcompare_minus_l"
  | "sub_add" -> "Pplus_minus" (* similar to le_plus_minus in Arith *)
  | "sub_add_one" -> "Ppred_succ"
  | "add_sub_one" -> "Psucc_pred"
  | "add_un" -> "Psucc"
  | "add_un_discr" -> "Psucc_discr"
  | "add_un_not_un" -> "Psucc_not_one"
  | "add_un_inj" -> "Psucc_inj"
  | "xI_add_un_xO" -> "xI_succ_xO"
  | "ZL12" -> "Pplus_one_succ_r"
  | "ZL12bis" -> "Pplus_one_succ_l"
  | "ZL13" -> "Pplus_carry_spec"
  | "ZL14" -> "Pplus_succ_permute_r"
  | "ZL14bis" -> "Pplus_succ_permute_l"
  | "sub_un" -> "Ppred"
  | "sub_pos" -> "Pminus_mask"
  | "sub_pos_x_x" -> "Pminus_mask_diag"
(*  | "sub_pos_x_x" -> "Pminus_mask_diag"*)
  | "sub_pos_SUPERIEUR" -> "Pminus_mask_Gt"
  | "sub_neg" -> "Pminus_mask_carry"
  | "Zdiv2_pos" -> "Pdiv2"
  | "ZERO" -> "Z0"
  | "POS" -> "Zpos"
  | "NEG" -> "Zneg"
  | "Nul" -> "N0"
  | "Pos" -> "Npos"
  | "Un_suivi_de" -> "Ndouble_plus_one"
  | "Zero_suivi_de" -> "Ndouble"
  | "Un_suivi_de_mask" -> "Pdouble_plus_one_mask"
  | "Zero_suivi_de_mask" -> "Pdouble_mask"
  | "ZS" -> "double_eq_zero_inversion"
  | "US" -> "double_plus_one_zero_discr"
  | "USH" -> "double_plus_one_eq_one_inversion"
  | "ZSH" -> "double_eq_one_discr"
  | "is_double_moins_un" -> "Psucc_double_minus_one_xO"
  | "double_moins_un_add_un_xI" -> "Pdouble_minus_one_succ_xI"
  | "ZPminus_add_un_permute" -> "ZPminus_succ_permute"
  | "ZPminus_add_un_permute_Zopp" -> "ZPminus_succ_permute_opp"
  | "ZPminus_double_moins_un_xO_add_un" -> "ZPminus_double_minus_one_xO_succ"
  | "ZL1" -> "xO_succ_permute"
  | "Zplus_assoc_r" -> "Zplus_assoc_reverse"
  | "Zplus_sym" -> "Zplus_comm"
  | "Zero_left" -> "Zplus_0_l"
  | "Zero_right" -> "Zplus_0_r"
  | "Zplus_n_O" -> "Zplus_0_r_reverse"
  | "Zplus_unit_left" -> "Zplus_0_simpl_l"
  | "Zplus_unit_right" -> "Zplus_0_simpl_l_reverse"
  | "Zplus_Zopp_expand" -> "Zplus_opp_expand"
  | "Zn_Sn" -> "Zsucc_discr"
  | "Zs" -> "Zsucc"
  | "Psucc_Zs" -> "Zpos_succ_permute"
  | "Zs_pred" -> "Zsucc_pred"
  | "Zpred_Sn" -> "Zpred_succ"
  | "Zminus_n_O" -> "Zminus_0_l_reverse"
  | "Zminus_n_n" -> "Zminus_diag_reverse"
  | "Zminus_Sn_m" -> "Zminus_succ_l"
  | "Zeq_Zminus" -> "Zeq_minus"
  | "Zminus_Zeq" -> "Zminus_eq"
  | "Zplus_minus" -> "Zplus_minus_eq"
  | "Zminus_plus" -> "Zminus_plus"
  | "Zminus_plus_simpl" -> "Zminus_plus_simpl_l_reverse"
  | "Zminus_Zplus_compatible" -> "Zminus_plus_simpl_r"
  | "Zle_plus_minus" -> "Zplus_minus"
  | "Zopp_Zplus" -> "Zopp_plus_distr"
  | "Zopp_Zopp" -> "Zopp_involutive"
  | "Zopp_NEG" -> "Zopp_neg"
  | "Zopp_Zdouble" -> "Zopp_double"
  | "Zopp_Zdouble_plus_one" -> "Zopp_double_plus_one"
  | "Zopp_Zdouble_minus_one" -> "Zopp_double_minus_one"
  | "Zplus_inverse_r" -> "Zplus_opp_r"
  | "Zplus_inverse_l" -> "Zplus_opp_l"
  | "Zplus_S_n" -> "Zplus_succ_l"
  | "Zplus_n_Sm" -> "Zplus_succ_r"
  | "Zplus_Snm_nSm" -> "Zplus_succ_comm"
  | "Zmult_assoc_r" -> "Zmult_assoc_reverse"
  | "Zmult_sym" -> "Zmult_comm"
  | "Zmult_eq" -> "Zmult_integral_l"
  | "Zmult_zero" -> "Zmult_integral"
  | "Zero_mult_left" -> "Zmult_0_l"
  | "Zero_mult_right" -> "Zmult_0_r"
  | "Zmult_1_n" -> "Zmult_1_l"
  | "Zmult_n_1" -> "Zmult_1_r"
  | "Zmult_n_O" -> "Zmult_0_r_reverse"
  | "Zopp_one" -> "Zopp_eq_mult_neg_1"
  | "Zopp_Zmult" -> "Zopp_mult_distr_l_reverse"
  | "Zopp_Zmult_r" -> "Zopp_mult_distr_r"
  | "Zopp_Zmult_l" -> "Zopp_mult_distr_l"
  | "Zmult_Zopp_Zopp" -> "Zmult_opp_opp"
  | "Zmult_Zopp_left" -> "Zmult_opp_comm"
  | "Zmult_Zplus_distr" -> "Zmult_plus_distr_r"
  | "Zmult_plus_distr" -> "Zmult_plus_distr_r"
  | "Zmult_Zminus_distr_r" -> "Zmult_minus_distr_l"
  | "Zmult_Zminus_distr_l" -> "Zmult_minus_distr_r"
  | "Zcompare_Zplus_compatible" -> "Zcompare_plus_compat"
  | "Zcompare_Zplus_compatible2" -> "Zplus_compare_compat"
  | "Zcompare_Zmult_compatible" -> "Zcompare_mult_compat"
  | "inject_nat" -> "Z_of_nat"
  | "inject_nat_complete" -> "Z_of_nat_complete"
  | "inject_nat_complete_inf" -> "Z_of_nat_complete_inf"
  | "inject_nat_prop" -> "Z_of_nat_prop"
  | "inject_nat_set" -> "Z_of_nat_set"
  | "convert" -> "nat_of_P"
  | "anti_convert" -> "P_of_succ_nat"
  | "positive_to_nat" -> "Pmult_nat"
  | "convert_intro" -> "nat_of_P_inj"
  | "convert_add" -> "nat_of_P_plus_morphism"
  | "convert_add_un" -> "Pmult_nat_succ_morphism"
  | "cvt_add_un" -> "nat_of_P_succ_morphism"
  | "convert_add_carry" -> "Pmult_nat_plus_carry_morphism"
  | "compare_convert_O" -> "lt_O_nat_of_P"
  | "Zopp_intro" -> "Zopp_inj"
  | "plus_iter_add" -> "plus_iter_eq_plus"
  | "add_verif" -> "Pmult_nat_l_plus_morphism"
  | "ZL2" -> "Pmult_nat_r_plus_morphism"
(* Trop spécifique ?
  | "ZL6" -> "Pmult_nat_plus_shift_morphism"
*)
  | "ZL15" -> "Pplus_carry_pred_eq_plus"
  | "cvt_carry" -> "nat_of_P_plus_carry_morphism"
  | "iter_convert" -> "iter_nat_of_P"
  | "compare" -> "Pcompare"
  | "compare_convert1" -> "Pcompare_not_Eq"
  | "compare_convert_INFERIEUR" -> "nat_of_P_lt_Lt_compare_morphism"
  | "compare_convert_SUPERIEUR" -> "nat_of_P_gt_Gt_compare_morphism"
  | "compare_convert_EGAL"      -> "Pcompare_Eq_eq"
  | "convert_compare_INFERIEUR" -> "nat_of_P_lt_Lt_compare_complement_morphism"
  | "convert_compare_SUPERIEUR" -> "nat_of_P_gt_Gt_compare_complement_morphism"
  | "convert_compare_EGAL"      -> "Pcompare_refl"
  | "Zcompare_EGAL"             -> "Zcompare_Eq_iff_eq"
  | "Zcompare_EGAL_eq"          -> "Zcompare_Eq_eq"
  | "Zcompare_x_x"              -> "Zcompare_refl"
  | "Zcompare_et_un"            -> "Zcompare_Gt_not_Lt"
  | "Zcompare_trans_SUPERIEUR"  -> "Zcompare_Gt_trans"
  | "Zcompare_n_S"              -> "Zcompare_succ_compat"
  | "SUPERIEUR_POS"             -> "Zcompare_Gt_spec"
  | "Zcompare_ANTISYM"          -> "Zcompare_antisym"
  | "compare_positive_to_nat_O" -> "le_Pmult_nat"
  | "Zcompare_Zs_SUPERIEUR"     -> "Zcompare_succ_Gt"
  | "Zcompare_Zopp"             -> "Zcompare_opp"
  | "ZLSI" -> "Pcompare_Gt_Lt"
  | "ZLIS" -> "Pcompare_Lt_Gt"
  | "ZLII" -> "Pcompare_Lt_Lt"
  | "ZLSS" -> "Pcompare_Gt_Gt"
  | "bij1" -> "nat_of_P_o_P_of_succ_nat_eq_succ"
  | "bij2" -> "P_of_succ_nat_o_nat_of_P_eq_succ"
  | "bij3" -> "pred_o_P_of_succ_nat_o_nat_of_P_eq_id"
  | "POS_inject" -> "Zpos_eq_Z_of_nat_o_nat_of_P"
  | "absolu" -> "Zabs_nat"
  | "absolu_lt" -> "Zabs_nat_lt" (* "Zabs_nat_lt_morphism_pos" ? *)
  | "Zeq_add_S" -> "Zsucc_inj"
  | "Znot_eq_S" -> "Zsucc_inj_contrapositive"
  | "Zeq_S" -> "Zsucc_eq_compat"
  | "Zsimpl_plus_l" -> "Zplus_reg_l"
  | "Zplus_simpl" -> "Zplus_eq_compat"
  | "POS_gt_ZERO" -> "Zgt_pos_0"
  | "ZERO_le_POS" -> "Zle_0_pos"
  | "ZERO_le_inj" -> "Zle_0_nat"
  | "NEG_lt_ZERO" -> "Zlt_neg_0"
  | "Zlt_ZERO_pred_le_ZERO" -> "Zlt_0_le_0_pred"
  | "POS_xI" -> "Zpos_xI"
  | "POS_xO" -> "Zpos_xO"
  | "NEG_xI" -> "Zneg_xI"
  | "NEG_xO" -> "Zneg_xO"
  | "POS_add" -> "Zpos_plus_distr"
  | "NEG_add" -> "Zneg_plus_distr"
  (* Z Orders *)
  | "not_Zge" -> "Znot_ge_lt"
  | "not_Zlt" -> "Znot_lt_ge"
  | "not_Zle" -> "Znot_le_gt"
  | "not_Zgt" -> "Znot_gt_le"
  | "Zgt_not_sym" -> "Zgt_asym"
  | "Zlt_not_sym" -> "Zlt_asym"
  | "Zlt_n_n" -> "Zlt_irrefl"
  | "Zgt_antirefl" -> "Zgt_irrefl"
  | "Zgt_reg_l" -> "Zplus_gt_compat_l"
  | "Zgt_reg_r" -> "Zplus_gt_compat_r"
  | "Zlt_reg_l" -> "Zplus_lt_compat_l"
  | "Zlt_reg_r" -> "Zplus_lt_compat_r"
  | "Zle_reg_l" -> "Zplus_le_compat_l"
  | "Zle_reg_r" -> "Zplus_le_compat_r"
  | "Zlt_le_reg" -> "Zplus_lt_le_compat"
  | "Zle_lt_reg" -> "Zplus_le_lt_compat"
  | "Zle_plus_plus" -> "Zplus_le_compat"
  | "Zlt_Zplus" -> "Zplus_lt_compat"
  | "Zle_O_plus" -> "Zplus_le_0_compat"
  | "Zle_mult_simpl" -> "Zmult_le_reg_r"
  | "Zge_mult_simpl" -> "Zmult_ge_reg_r"
  | "Zgt_mult_simpl" -> "Zmult_gt_reg_r"
  | "Zsimpl_gt_plus_l" -> "Zplus_gt_reg_l"
  | "Zsimpl_gt_plus_r" -> "Zplus_gt_reg_r"
  | "Zsimpl_le_plus_l" -> "Zplus_le_reg_l"
  | "Zsimpl_le_plus_r" -> "Zplus_le_reg_r"
  | "Zsimpl_lt_plus_l" -> "Zplus_lt_reg_l"
  | "Zsimpl_lt_plus_r" -> "Zplus_lt_reg_r"
  | "Zlt_Zmult_right2" -> "Zmult_gt_0_lt_reg_r"
  | "Zlt_Zmult_right" -> "Zmult_gt_0_lt_compat_r"
  | "Zle_Zmult_right2" -> "Zmult_gt_0_le_reg_r"
  | "Zle_Zmult_right" -> "Zmult_gt_0_le_compat_r"
  | "Zgt_Zmult_right" -> "Zmult_gt_compat_r"
  | "Zgt_Zmult_left" -> "Zmult_gt_compat_l"
  | "Zlt_Zmult_left" -> "Zmult_gt_0_lt_compat_l"
  | "Zcompare_Zmult_right" -> "Zmult_compare_compat_r"
  | "Zcompare_Zmult_left" -> "Zmult_compare_compat_l"
  | "Zplus_Zmult_2" -> "Zplus_diag_eq_mult_2"
  | "Zmult_Sm_n" -> "Zmult_succ_l_reverse"
  | "Zmult_n_Sm" -> "Zmult_succ_r_reverse"
  | "Zmult_le" -> "Zmult_le_0_reg_r"
  | "Zmult_reg_left" -> "Zmult_reg_l"
  | "Zmult_reg_right" -> "Zmult_reg_r"
  | "Zle_ZERO_mult" -> "Zmult_le_0_compat"
  | "Zgt_ZERO_mult" -> "Zmult_gt_0_compat"
  | "Zle_mult" -> "Zmult_gt_0_le_0_compat"
  | "Zmult_lt" -> "Zmult_gt_0_lt_0_reg_r"
  | "Zmult_gt" -> "Zmult_gt_0_reg_l"
  | "Zle_Zmult_pos_right" -> "Zmult_le_compat_r"
  | "Zle_Zmult_pos_left" -> "Zmult_le_compat_l"
  | "Zge_Zmult_pos_right" -> "Zmult_ge_compat_r"
  | "Zge_Zmult_pos_left" -> "Zmult_ge_compat_l"
  | "Zge_Zmult_pos_compat" -> "Zmult_ge_compat"
  | "Zlt_Zcompare" -> "Zlt_compare"
  | "Zle_Zcompare" -> "Zle_compare"
  | "Zgt_Zcompare" -> "Zgt_compare"
  | "Zge_Zcompare" -> "Zge_compare"
  (* IntMap *)
  | "convert_xH" -> "nat_of_P_xH"
  | "convert_xO" -> "nat_of_P_xO"
  | "convert_xI" -> "nat_of_P_xI"
  | "positive_to_nat_mult" -> "Pmult_nat_mult_permute"
  | "positive_to_nat_2" -> "Pmult_nat_2_mult_2_permute"
  | "positive_to_nat_4" -> "Pmult_nat_4_mult_2_permute"
  (* ZArith and Arith orders *)
  | "Zle_refl" -> "Zeq_le"
  | "Zle_n" -> "Zle_refl"
  | "Zle_trans_S" -> "Zle_succ_le"
  | "Zgt_trans_S" -> "Zge_trans_succ"
  | "Zgt_S" -> "Zgt_succ_gt_or_eq"
  | "Zle_Sn_n" -> "Znot_le_succ"
  | "Zlt_n_Sn" -> "Zlt_succ"
  | "Zlt_S" -> "Zlt_lt_succ"
  | "Zlt_n_S" -> "Zsucc_lt_compat"
  | "Zle_n_S" -> "Zsucc_le_compat"
  | "Zgt_n_S" -> "Zsucc_gt_compat"
  | "Zlt_S_n" -> "Zsucc_lt_reg"
  | "Zgt_S_n" -> "Zsucc_gt_reg"
  | "Zle_S_n" -> "Zsucc_le_reg"
  | "Zle_0_plus" -> "Zplus_le_0_compat"
  | "Zgt_Sn_n" -> "Zgt_succ"
  | "Zgt_le_S" -> "Zgt_le_succ"
  | "Zgt_S_le" -> "Zgt_succ_le"
  | "Zle_S_gt" -> "Zlt_succ_gt"
  | "Zle_gt_S" -> "Zlt_gt_succ"
  | "Zgt_pred" -> "Zgt_succ_pred"
  | "Zlt_pred" -> "Zlt_succ_pred"
  | "Zgt0_le_pred" -> "Zgt_0_le_0_pred"
  | "Z_O_1" -> "Zlt_0_1"
  | "Zle_NEG_POS" -> "Zle_neg_pos"
  | "Zle_n_Sn" -> "Zle_succ"
  | "Zle_pred_n" -> "Zle_pred"
  | "Zlt_pred_n_n" -> "Zlt_pred"
  | "Zlt_le_S" -> "Zlt_le_succ"
  | "Zlt_n_Sm_le" -> "Zlt_succ_le"
  | "Zle_lt_n_Sm" -> "Zle_lt_succ"
  | "Zle_le_S" -> "Zle_le_succ"
  | "Zlt_minus" -> "Zlt_minus_simpl_swap"
  | "le_trans_S" -> "le_Sn_le"
  (* Arith *)
(* Peano.v
  | "plus_n_O" -> "plus_0_r_reverse"
  | "plus_O_n" -> "plus_0_l"
*)
  | "plus_assoc_l" -> "plus_assoc"
  | "plus_assoc_r" -> "plus_assoc_reverse"
  | "plus_sym" -> "plus_comm"
  | "mult_sym" -> "mult_comm"
  | "max_sym" -> "max_comm"
  | "min_sym" -> "min_comm"
  | "gt_not_sym" -> "gt_asym"
  | "lt_not_sym" -> "lt_asym"
  | "gt_antirefl" -> "gt_irrefl"
  | "lt_n_n" -> "lt_irrefl"
(* Trop utilisé dans CoqBook | "le_n" -> "le_refl"*)
  | "simpl_plus_l" -> "plus_reg_l"
  | "simpl_plus_r" -> "plus_reg_r"
  | "fact_growing" -> "fact_le"
  | "mult_assoc_l" -> "mult_assoc"
  | "mult_assoc_r" -> "mult_assoc_reverse"
  | "mult_plus_distr" -> "mult_plus_distr_r"
  | "mult_plus_distr_r" -> "mult_plus_distr_l"
  | "mult_minus_distr" -> "mult_minus_distr_r"
  | "mult_1_n" -> "mult_1_l"
  | "mult_n_1" -> "mult_1_r"
(* Peano.v
  | "mult_n_O" -> "mult_O_r_reverse"
  | "mult_n_Sm" -> "mult_S_r_reverse"
*)
  | "lt_mult_left" -> "mult_S_lt_compat_l"
  | "mult_le" -> "mult_le_compat_l"
  | "le_mult_right" -> "mult_le_compat_r"
  | "le_mult_mult" -> "mult_le_compat"
  | "mult_lt" -> "mult_S_lt_compat_l"
  | "lt_mult_right" -> "mult_lt_compat_r"
  | "mult_le_conv_1" -> "mult_S_le_reg_l"
  | "exists" -> "exists_between"
  | "IHexists" -> "IHexists_between"
(* Peano.v
  | "pred_Sn" -> "pred_S"
*)
  | "inj_minus_aux" -> "not_le_minus_0"
  | "minus_x_x" -> "minus_diag"
  | "minus_plus_simpl" -> "minus_plus_simpl_l_reverse"
  | "gt_reg_l" -> "plus_gt_compat_l"
  | "le_reg_l" -> "plus_le_compat_l"
  | "le_reg_r" -> "plus_le_compat_r"
  | "lt_reg_l" -> "plus_lt_compat_l"
  | "lt_reg_r" -> "plus_lt_compat_r"
  | "le_plus_plus" -> "plus_le_compat"
  | "le_lt_plus_plus" -> "plus_le_lt_compat"
  | "lt_le_plus_plus" -> "plus_lt_le_compat"
  | "lt_plus_plus" -> "plus_lt_compat"
  | "plus_simpl_l" -> "plus_reg_l"
  | "simpl_gt_plus_l" -> "plus_gt_reg_l"
  | "simpl_le_plus_l" -> "plus_le_reg_l"
  | "simpl_lt_plus_l" -> "plus_lt_reg_l"
(* Noms sur le principe de ceux de Z
  | "le_n_S" -> "S_le_compat"
  | "le_n_Sn" -> "le_S"
(*  | "le_O_n" -> "??" *)
  | "le_pred_n" -> "le_pred"
  | "le_trans_S" -> "le_S_le"
  | "le_S_n" -> "S_le_reg"
  | "le_Sn_O" -> "not_le_S_O"
  | "le_Sn_n" -> "not_le_S"
*)
  (* Init *)
  | "IF" -> "IF_then_else"
  | "relation" when is_module "Datatypes" or is_dir dir "Datatypes"
      -> "comparison"
  | "Op" when is_module "Datatypes" or is_dir dir "Datatypes"
      -> "CompOpp"
  (* Lists *)
  | "idempot_rev" -> "rev_involutive"
  | "forall" -> "HereAndFurther"
  (* Bool *)
  | "orb_sym" -> "orb_comm"
  | "andb_sym" -> "andb_comm"
  (* Reals *)
  | s when String.length s >= 7 & (String.sub s 0 7 = "Rabsolu") ->
      "Rabs"^(String.sub s 7 (String.length s - 7))
  | s when String.length s >= 7 &
      (String.sub s (String.length s - 7) 7 = "Rabsolu") ->
      (String.sub s 0 (String.length s - 7))^"Rabs"
(*
  | "Rabsolu" -> "Rabs"
  | "Rabsolu_pos_lt" -> "Rabs_pos_lt"
  | "Rabsolu_no_R0" -> "Rabs_no_R0"
  | "Rabsolu_Rabsolu" -> "Rabs_Rabs"
  | "Rabsolu_mult" -> "Rabs_mult"
  | "Rabsolu_triang" -> "Rabs_triang"
  | "Rabsolu_Ropp" -> "Rabs_Ropp"
  | "Rabsolu_right" -> "Rabs_right"
...
  | "case_Rabsolu" -> "case_Rabs"
  | "Pow_Rabsolu" -> "Pow_Rabs"
...
*)
  | "complet" -> "completeness"
  | "complet_weak" -> "completeness_weak"
  | "Rle_sym1" -> "Rle_ge"
  | "Rmin_sym" -> "Rmin_comm"
  | "Rplus_sym" -> "Rplus_comm"
  | "Rmult_sym" -> "Rmult_comm"
  | "Rsqr_times" -> "Rsqr_mult"
  | "sqrt_times" -> "sqrt_mult"
  | "Rmult_1l" -> "Rmult_1_l"
  | "Rplus_Ol" -> "Rplus_0_l"
  | "Rplus_Ropp_r" -> "Rplus_opp_r"
  | "Rmult_Rplus_distr_l" -> "Rmult_plus_distr_l"
  | "Rlt_antisym" -> "Rlt_asym"
  | "Rlt_antirefl" -> "Rlt_irrefl"
  | "Rlt_compatibility" -> "Rplus_lt_compat_l"
  | "Rgt_plus_plus_r" -> "Rplus_gt_compat_l"
  | "Rgt_r_plus_plus" -> "Rplus_gt_reg_l"
  | "Rge_plus_plus_r" -> "Rplus_ge_compat_l"
  | "Rge_r_plus_plus" -> "Rplus_ge_reg_l"
(* Si on en change un, il faut changer tous les autres R*_monotony *)
  | "Rlt_monotony" -> "Rmult_lt_compat_l"
  | "Rlt_monotony_r" -> "Rmult_lt_compat_r"
  | "Rlt_monotony_contra" -> "Rmult_lt_reg_l"
  | "Rlt_anti_monotony" -> "Rmult_lt_gt_compat_neg_l"
  | "Rle_monotony" -> "Rmult_le_compat_l"
  | "Rle_monotony_r" -> "Rmult_le_compat_r"
  | "Rle_monotony_contra" -> "Rmult_le_reg_l"
  | "Rle_anti_monotony1" -> "Rmult_le_compat_neg_l"
  | "Rle_anti_monotony" -> "Rmult_le_ge_compat_neg_l"
  | "Rle_Rmult_comp" -> "Rmult_le_compat"
    (* Expliciter que la contrainte est r2>0 dans r1<r2 et non 0<r1 ce
       qui est plus général mais différent de Rmult_le_compat *)
  | "Rmult_lt" -> "Rmult_lt_compat"
  | "Rlt_monotony_rev" -> "Rmult_lt_reg_l"
  | "Rge_monotony" -> "Rmult_ge_compat_r"
  | "Rmult_lt_0" -> "Rmult_lt_compat_ge" (* Un truc hybride *)

  | "Rge_ge_eq" -> "Rge_antisym"
  | s when String.length s >= 7 & 
      let s' = String.sub s 0 7 in
      (s' = "unicite" or s' = "unicity") ->
      "uniqueness"^(String.sub s 7 (String.length s - 7))
  (* Default *)
  | s when String.length s > 1 && s.[0]='_' ->
      String.sub s 1 (String.length s - 1)
  | "_" -> 
      msgerrnl (str 
	"Warning: '_' is no longer an ident; it has been translated to 'x_'");
      "x_"
  | x -> x

let id_of_v7_string s =
  id_of_string (if !Options.v7 then s else translate_v7_string empty_dirpath s)

let v7_to_v8_dir_id dir id =
  if Options.do_translate() then
    let s = string_of_id id in
    let s = 
      if (is_coq_root (Lib.library_dp()) or is_coq_root dir)
      then translate_v7_string dir s else avoid_wildcard_string s in
    id_of_string (translate_keyword s)
  else id

let v7_to_v8_id id = v7_to_v8_dir_id empty_dirpath id

let shortest_qualid_of_v7_global ctx ref =
  let fulldir,_ = repr_path (sp_of_global ref) in
  let dir,id = repr_qualid (shortest_qualid_of_global ctx ref) in
  make_qualid dir (v7_to_v8_dir_id fulldir id)

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_v7_global vars r)
  with Not_found ->
    (* happens in debugger *)
    Ident (loc,id_of_string (raw_string_of_ref r))

(***********************************************************************)
(* Equality up to location (useful for translator v8) *)

let rec check_same_pattern p1 p2 =
  match p1, p2 with
    | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) when i1=i2 ->
        check_same_pattern a1 a2
    | CPatCstr(_,c1,a1), CPatCstr(_,c2,a2) when c1=c2 ->
        List.iter2 check_same_pattern a1 a2
    | CPatAtom(_,r1), CPatAtom(_,r2) when r1=r2 -> ()
    | CPatNumeral(_,i1), CPatNumeral(_,i2) when i1=i2 -> ()
    | CPatDelimiters(_,s1,e1), CPatDelimiters(_,s2,e2) when s1=s2 ->
        check_same_pattern e1 e2
    | _ -> failwith "not same pattern"

let check_same_ref r1 r2 =
  match r1,r2 with
  | Qualid(_,q1), Qualid(_,q2) when q1=q2 -> ()
  | Ident(_,i1), Ident(_,i2) when i1=i2 -> ()
  | _ -> failwith "not same ref"

let rec check_same_type ty1 ty2 =
  match ty1, ty2 with
  | CRef r1, CRef r2 -> check_same_ref r1 r2
  | CFix(_,(_,id1),fl1), CFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,i1,a1,b1) (id2,i2,a2,b2) ->
        if id1<>id2 || i1<>i2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CCoFix(_,(_,id1),fl1), CCoFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,a1,b1) (id2,a2,b2) ->
        if id1<>id2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CArrow(_,a1,b1), CArrow(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) when na1=na2 ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CAppExpl(_,r1,al1), CAppExpl(_,r2,al2) when r1=r2 ->
      List.iter2 check_same_type al1 al2
  | CApp(_,(_,e1),al1), CApp(_,(_,e2),al2) ->
      check_same_type e1 e2;
      List.iter2 (fun (a1,e1) (a2,e2) ->
                    if e1<>e2 then failwith "not same expl";
                    check_same_type a1 a2) al1 al2
  | CCases(_,_,a1,brl1), CCases(_,_,a2,brl2) ->
      List.iter2 (fun (tm1,_) (tm2,_) -> check_same_type tm1 tm2) a1 a2;
      List.iter2 (fun (_,pl1,r1) (_,pl2,r2) ->
        List.iter2 check_same_pattern pl1 pl2;
        check_same_type r1 r2) brl1 brl2
  | COrderedCase(_,_,_,a1,bl1), COrderedCase(_,_,_,a2,bl2) ->
      check_same_type a1 a2;
      List.iter2 check_same_type bl1 bl2
  | CHole _, CHole _ -> ()
  | CPatVar(_,i1), CPatVar(_,i2) when i1=i2 -> ()
  | CSort(_,s1), CSort(_,s2) when s1=s2 -> ()
  | CCast(_,a1,b1), CCast(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CNotation(_,n1,e1), CNotation(_,n2,e2) when n1=n2 ->
      List.iter2 check_same_type e1 e2
  | CNumeral(_,i1), CNumeral(_,i2) when i1=i2 -> ()
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) when s1=s2 ->
      check_same_type e1 e2
  | _ when ty1=ty2 -> ()
  | _ -> failwith "not same type"

and check_same_binder (nal1,e1) (nal2,e2) =
  List.iter2 (fun (_,na1) (_,na2) ->
    if na1<>na2 then failwith "not same name") nal1 nal2;
  check_same_type e1 e2

let same c d = try check_same_type c d; true with _ -> false

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let make_current_scopes (scopt,scopes) = 
  option_fold_right push_scope scopt scopes

let make_notation loc ntn l =
  match ntn,l with
    (* Special case to avoid writing "- 3" for e.g. (Zopp 3) *)
    | "- _", [CNumeral(_,Bignat.POS p)] -> CNotation (loc,"- ( _ )",l)
    | _ -> CNotation (loc,ntn,l)

let make_pat_notation loc ntn l =
  match ntn,l with
    (* Special case to avoid writing "- 3" for e.g. (Zopp 3) *)
    | "- _", [CPatNumeral(_,Bignat.POS p)] ->
        CPatNotation (loc,"- ( _ )",l)
    | _ -> CPatNotation (loc,ntn,l)


(*
let rec cases_pattern_expr_of_constr_expr = function
  | CRef r -> CPatAtom (dummy_loc,Some r)
  | CHole loc -> CPatAtom (loc,None)
  | CApp (loc,(proj,CRef c),l) when proj = None ->
      let l,e = List.split l in
      if not (List.for_all ((=) None) e) then
	anomaly "Unexpected explicitation in pattern";
      CPatCstr (loc,c,List.map cases_pattern_expr_of_constr_expr l)
  | CNotation (loc,ntn,l) ->
      CPatNotation (loc,ntn,List.map cases_pattern_expr_of_constr_expr l)
  | CNumeral (loc,n) -> CPatNumeral (loc,n)
  | CDelimiters (loc,s,e) -> 
      CPatDelimiters (loc,s,cases_pattern_expr_of_constr_expr e)	
  | _ -> anomaly "Constrextern: not a pattern"

let rec rawconstr_of_cases_pattern = function
  | PatVar (loc,Name id) -> RVar (loc,id)
  | PatVar (loc,Anonymous) -> RHole (loc,InternalHole)
  | PatCstr (loc,(ind,_ as c),args,_) -> 
      let nparams = (snd (Global.lookup_inductive ind)).Declarations.mind_nparams in
      let params = list_tabulate (fun _ -> RHole (loc,InternalHole)) nparams in
      let args = params @ List.map rawconstr_of_cases_pattern args in
      let f = RRef (loc,ConstructRef c) in
      if args = [] then f else RApp (loc,f,args)
*)

let bind_env sigma var v =
  try
    let vvar = List.assoc var sigma in
    if v=vvar then sigma else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma

let rec match_cases_pattern metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env sigma id2 r1
  | PatVar (_,Anonymous), AHole _ -> sigma
  | a, AHole _ when not(Options.do_translate()) -> sigma
  | PatCstr (loc,(ind,_ as r1),args1,Anonymous), _ ->
      let nparams =
	(snd (Global.lookup_inductive ind)).Declarations.mind_nparams in
      let params1 = list_tabulate (fun _ -> PatVar (loc,Anonymous)) nparams in
      (match params1@args1, a2 with
	| [], ARef (ConstructRef r2) when r1 = r2 -> sigma
	| l1, AApp (ARef (ConstructRef r2),l2) 
	    when r1 = r2 & List.length l1 = List.length l2 ->
	    List.fold_left2 (match_cases_pattern metas) sigma l1 l2
	| _ -> raise No_match)
  | _ -> raise No_match

let match_aconstr_cases_pattern c (metas_scl,pat) =
  let subst = match_cases_pattern (List.map fst metas_scl) [] c pat in
  (* Reorder canonically the substitution *)
  let find x subst =
    try List.assoc x subst
    with Not_found -> anomaly "match_aconstr_cases_pattern" in
  List.map (fun (x,scl) -> (find x subst,scl)) metas_scl

 (* Better to use extern_rawconstr composed with injection/retraction ?? *)
let rec extern_cases_pattern_in_scope scopes vars pat =
  try 
    if !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc (make_current_scopes scopes) with
    | None -> raise No_match
    | Some key ->
        let loc = pattern_loc pat in
        insert_pat_delimiters (CPatNumeral (loc,n)) key
  with No_match ->
  try 
    if !print_no_symbol then raise No_match;
    extern_symbol_pattern scopes vars pat
      (Symbols.uninterp_cases_pattern_notations pat)
  with No_match ->
  match pat with
  | PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,v7_to_v8_id id)))
  | PatVar (loc,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(loc,cstrsp,args,na) ->
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      let p = CPatCstr
        (loc,extern_reference loc vars (ConstructRef cstrsp),args) in
      (match na with
	| Name id -> CPatAlias (loc,p,v7_to_v8_id id)
	| Anonymous -> p)
	
and extern_symbol_pattern (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as rule)::rules ->
      try
	(* Check the number of arguments expected by the notation *)
	let loc = match t,n with
	  | PatCstr (_,f,l,_), Some n when List.length l > n ->
	      raise No_match
	  | PatCstr (loc,_,_,_),_ -> loc
	  | PatVar (loc,_),_ -> loc in
	(* Try matching ... *)
	let subst = match_aconstr_cases_pattern t pat in
	(* Try availability of interpretation ... *)
        match keyrule with
          | NotationRule (sc,ntn) ->
	      let scopes' = make_current_scopes (tmp_scope, scopes) in
	      (match Symbols.availability_of_notation (sc,ntn) scopes' with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes = make_current_scopes (scopt, scopes) in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern_cases_pattern_in_scope 
		        (scopt,List.fold_right push_scope scl scopes) vars c)
                      subst in
		  insert_pat_delimiters (make_pat_notation loc ntn l) key)
          | SynDefRule kn ->
 	      CPatAtom (loc,Some (Qualid (loc, shortest_qualid_of_syndef kn)))
	with
	    No_match -> extern_symbol_pattern allscopes vars t rules

(**********************************************************************)
(* Externalising applications *)

let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_projection nargs = function
  | Some r when !print_projections ->
      (try 
	let n = Recordops.find_projection_nparams r + 1 in
	if n <= nargs then Some n else None
      with Not_found -> None)
  | _ -> None

let is_nil = function
  | [CRef ref] -> snd (repr_qualid (snd (qualid_of_reference ref))) = id_of_string "nil"
  | _ -> false

let stdlib_but_length args = function
  | Some r -> 
      let dir,id = repr_path (sp_of_global r) in
      (is_coq_root (Lib.library_dp()) or is_coq_root dir)
      && not (List.mem (string_of_id id) ["Zlength";"length"] && is_nil args)
      && not (List.mem (string_of_id id) ["In"] && List.length args >= 2
              && is_nil (List.tl args))
  | None -> false

let explicit_code imp q =
  dummy_loc,
  if !Options.v7 & not (Options.do_translate()) then ExplByPos q
  else ExplByName (name_of_implicit imp)

let is_hole = function CHole _ -> true | _ -> false

let is_significant_implicit a impl tail =
  not (is_hole a) or (tail = [] & not (List.for_all is_status_implicit impl))

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let explicitize loc inctx impl (cf,f) args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          (!print_implicits & !print_implicits_explicit_args) or 
	  (is_significant_implicit a impl tail &
	  (not (is_inferable_implicit inctx n imp) or
	    (Options.do_translate() & not (stdlib_but_length args cf))))
	in
        if visible then (a,Some (explicit_code imp q)) :: tail else tail
    | a::args, _::impl -> (a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (a,None)) args (*In case of polymorphism*)
    | [], _ -> [] in
  match is_projection (List.length args) cf with
    | Some i as ip ->
	if impl <> [] & is_status_implicit (List.nth impl (i-1)) then
	  let f' = match f with CRef f -> f | _ -> assert false in
	  CAppExpl (loc,(ip,f'),args)
	else
	  let (args1,args2) = list_chop i args in
	  let (impl1,impl2) = if impl=[] then [],[] else list_chop i impl in
	  let args1 = exprec 1 (args1,impl1) in
	  let args2 = exprec (i+1) (args2,impl2) in
	  CApp (loc,(Some (List.length args1),f),args1@args2)
    | None -> 
	let args = exprec 1 (args,impl) in
	if args = [] then f else CApp (loc, (None, f), args)

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions or Options.do_translate () then app
  else
    try
      match dest_ref f with
	| Some r ->
	    (match Classops.hide_coercion r with
	       | Some n ->
		   if n >= List.length args then app
		   else (* We skip a coercion *) 
		     let fargs = list_skipn n args in
	       	     skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	       | None -> app)
	| None -> app
    with Not_found -> app

let extern_global loc impl f =
  if impl <> [] & List.for_all is_status_implicit impl then
    CAppExpl (loc, (None, f), [])
  else
    CRef f

let extern_app loc inctx impl (cf,f) args =
  if args = [] (* maybe caused by a hidden coercion *) then
    extern_global loc impl f
  else
  if !print_implicits &
    not !print_implicits_explicit_args &
    List.exists is_status_implicit impl
  then 
    CAppExpl (loc, (is_projection (List.length args) cf, f), args)
  else
    explicitize loc inctx impl (cf,CRef f) args

let rec extern_args extern scopes env args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> (None,scopes), []
	  | scopt::subscopes -> (scopt,scopes), subscopes in
	extern argscopes env a :: extern_args extern scopes env args subscopes

(**********************************************************************)
(* mapping rawterms to constr_expr                                    *)

let rec extern inctx scopes vars r =
  try 
    if !print_no_symbol then raise No_match;
    extern_numeral (Rawterm.loc_of_rawconstr r)
      scopes (Symbols.uninterp_numeral r)
  with No_match ->

  try 
    if !print_no_symbol then raise No_match;
    extern_symbol scopes vars r (Symbols.uninterp_notations r)
  with No_match -> match r with
  | RRef (loc,ref) ->
      extern_global loc (implicits_of_global_out ref)
        (extern_reference loc vars ref)

  | RVar (loc,id) -> CRef (Ident (loc,v7_to_v8_id id))

  | REvar (loc,n) -> extern_evar loc n

  | RPatVar (loc,n) -> if !print_meta_as_hole then CHole loc else CPatVar (loc,n)

  | RApp (loc,f,args) ->
      let (f,args) =
	if inctx then
	  skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args)
	else 
	  (f,args) in
      (match f with
	 | REvar (loc,ev) -> extern_evar loc ev (* we drop args *)
	 | RRef (rloc,ref) ->
	     let subscopes = Symbols.find_arguments_scope ref in
	     let args =
	       extern_args (extern true) (snd scopes) vars args subscopes in
	     extern_app loc inctx (implicits_of_global_out ref)
               (Some ref,extern_reference rloc vars ref)
	       args
	 | RVar (rloc,id) -> (* useful for translation of inductive *)
	     let args = List.map (sub_extern true scopes vars) args in
	     extern_app loc inctx (get_temporary_implicits_out id)
	       (None,Ident (rloc,v7_to_v8_id id))
	       args
	 | _       -> 
	     explicitize loc inctx [] (None,sub_extern false scopes vars f)
               (List.map (sub_extern true scopes vars) args))

  | RProd (loc,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_type scopes vars t, extern_type scopes vars c)

  | RLetIn (loc,na,t,c) ->
      let na = name_app avoid_wildcard na in
      CLetIn (loc,(loc,na),sub_extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | RProd (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) t c in
      CProdN (loc,[(dummy_loc,na)::idl,t],c)

  | RLambda (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) t c in
      CLambdaN (loc,[(dummy_loc,na)::idl,t],c)

  | RCases (loc,(typopt,rtntypopt),tml,eqns) ->
      let pred = option_app (extern_type scopes vars) typopt in
      let rtntypopt = option_app (extern_type scopes vars) !rtntypopt in
      let vars' = 
	List.fold_right (name_fold Idset.add)
	  (cases_predicate_names tml) vars in
      let tml = List.map (fun (tm,{contents=(na,x)}) ->
	(sub_extern false scopes vars tm,
	(na,option_app (fun (loc,ind,nal) ->
	  let args = List.map (function
	    | Anonymous -> RHole (dummy_loc,InternalHole) 
	    | Name id -> RVar (dummy_loc,id)) nal in
	  let t = RApp (dummy_loc,RRef (dummy_loc,IndRef ind),args) in
	  (extern_type scopes vars t)) x))) tml in
      let eqns = List.map (extern_eqn (typopt<>None) scopes vars) eqns in 
      CCases (loc,(pred,rtntypopt),tml,eqns)

  | ROrderedCase (loc,cs,typopt,tm,bv,{contents = Some x}) ->
      extern false scopes vars x

  | ROrderedCase (loc,cs,typopt,tm,bv,_) ->
      let bv = Array.map (sub_extern (typopt<>None) scopes vars) bv in
      COrderedCase
	(loc,cs,option_app (extern_type scopes vars) typopt,
         sub_extern false scopes vars tm,Array.to_list bv)

  | RLetTuple (loc,nal,(na,typopt),tm,b) ->
      CLetTuple (loc,nal,
        (na,option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern false scopes (List.fold_left add_vname vars nal) b)

  | RIf (loc,c,(na,typopt),b1,b2) ->
      CIf (loc,sub_extern false scopes vars c,
        (na,option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars b1, sub_extern false scopes vars b2)

  | RRec (loc,fk,idv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
		 (fi,nv.(i),extern_type scopes vars tyv.(i),
                  extern false scopes vars' bv.(i))) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
		 (fi,extern_type scopes vars tyv.(i),
                  sub_extern false scopes vars' bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (loc,s) ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

  | RHole (loc,e) -> CHole loc

  | RCast (loc,c,t) ->
      CCast (loc,sub_extern true scopes vars c,extern_type scopes vars t)

  | RDynamic (loc,d) -> CDynamic (loc,d)

and extern_type (_,scopes) = extern true (Some Symbols.type_scope,scopes)

and sub_extern inctx (_,scopes) = extern inctx (None,scopes)

and factorize_prod scopes vars aty = function
  | RProd (loc,(Name id as na),ty,c)
      when same aty (extern_type scopes vars (anonymize_if_reserved na ty))
	& not (occur_var_constr_expr id aty) (* avoid na in ty escapes scope *)
	-> let id = avoid_wildcard id in
           let (nal,c) = factorize_prod scopes (Idset.add id vars) aty c in
           ((loc,Name id)::nal,c)
  | c -> ([],extern_type scopes vars c)

and factorize_lambda inctx scopes vars aty = function
  | RLambda (loc,na,ty,c)
      when same aty (extern_type scopes vars (anonymize_if_reserved na ty))
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let na = name_app avoid_wildcard na in
           let (nal,c) =
	     factorize_lambda inctx scopes (add_vname vars na) aty c in
           ((loc,na)::nal,c)
  | c -> ([],sub_extern inctx scopes vars c)

and extern_eqn inctx scopes vars (loc,ids,pl,c) =
  (loc,List.map (extern_cases_pattern_in_scope scopes vars) pl,
   extern inctx scopes vars c)

and extern_numeral loc scopes (sc,n) =
  match Symbols.availability_of_numeral sc (make_current_scopes scopes) with
    | None -> raise No_match
    | Some key -> insert_delimiters (CNumeral (loc,n)) key

and extern_symbol (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as rule)::rules ->
      let loc = Rawterm.loc_of_rawconstr t in
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args) = match t,n with
	  | RApp (_,f,args), Some n when List.length args > n ->
	      let args1, args2 = list_chop n args in
	      RApp (dummy_loc,f,args1), args2
	  | _ -> t,[] in
	(* Try matching ... *)
	let subst = match_aconstr t pat in
	(* Try availability of interpretation ... *)
        let e =
          match keyrule with
          | NotationRule (sc,ntn) ->
	      let scopes' = make_current_scopes (tmp_scope, scopes) in
	      (match Symbols.availability_of_notation (sc,ntn) scopes' with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes = make_current_scopes (scopt, scopes) in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern (* assuming no overloading: *) true
		        (scopt,List.fold_right push_scope scl scopes) vars c)
                      subst in
	          insert_delimiters (make_notation loc ntn l) key)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef kn)) in
 	if args = [] then e 
	else
	  (* TODO: compute scopt for the extra args, in case, head is a ref *)
	  explicitize loc false [] (None,e)
	  (List.map (extern true allscopes vars) args)
      with
	  No_match -> extern_symbol allscopes vars t rules

let extern_rawconstr vars c = 
  extern false (None,Symbols.current_scopes()) vars c

let extern_rawtype vars c =
  extern_type (None,Symbols.current_scopes()) vars c

let extern_cases_pattern vars p = 
  extern_cases_pattern_in_scope (None,Symbols.current_scopes()) vars p

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = dummy_loc (* for constr and pattern, locations are lost *)

let extern_constr_gen at_top scopt env t =
  let vars = vars_of_env env in
  let avoid = if at_top then ids_of_context env else [] in
  extern (not at_top) (scopt,Symbols.current_scopes()) vars
    (Detyping.detype (at_top,env) avoid (names_of_rel_context env) t)

let extern_constr_in_scope at_top scope env t =
  extern_constr_gen at_top (Some scope) env t

let extern_constr at_top env t =
  extern_constr_gen at_top None env t

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let rec raw_of_pat tenv env = function
  | PRef ref -> RRef (loc,ref)
  | PVar id -> RVar (loc,id)
  | PEvar n -> REvar (loc,n)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
	| Name id   -> id
	| Anonymous ->
	    anomaly "rawconstr_of_pattern: index to an anonymous variable"
      with Not_found -> id_of_string ("[REL "^(string_of_int n)^"]") in
      RVar (loc,id)
  | PMeta None -> RHole (loc,InternalHole)
  | PMeta (Some n) -> RPatVar (loc,(false,n))
  | PApp (f,args) ->
      RApp (loc,raw_of_pat tenv env f,array_map_to_list (raw_of_pat tenv env) args)
  | PSoApp (n,args) ->
      RApp (loc,RPatVar (loc,(true,n)),
        List.map (raw_of_pat tenv env) args)
  | PProd (na,t,c) ->
      RProd (loc,na,raw_of_pat tenv env t,raw_of_pat tenv (na::env) c)
  | PLetIn (na,t,c) ->
      RLetIn (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PLambda (na,t,c) ->
      RLambda (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PCase ((_,(IfStyle|LetStyle as cs)),typopt,tm,bv) ->
      ROrderedCase (loc,cs,option_app (raw_of_pat tenv env) typopt,
         raw_of_pat tenv env tm,Array.map (raw_of_pat tenv env) bv, ref None)
  | PCase ((_,cs),typopt,tm,[||]) ->
      RCases (loc,(option_app (raw_of_pat tenv env) typopt,ref None (* TODO *)),
         [raw_of_pat tenv env tm,ref (Anonymous,None)],[])
  | PCase ((Some ind,cs),typopt,tm,bv) ->
      let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
      let k = (snd (lookup_mind_specif (Global.env()) ind)).Declarations.mind_nrealargs in
      Detyping.detype_case false (raw_of_pat tenv env)(raw_of_eqn tenv env)
	tenv avoid ind cs typopt k tm bv
  | PCase _ -> error "Unsupported case-analysis while printing pattern"
  | PFix f -> Detyping.detype (false,tenv) [] env (mkFix f)
  | PCoFix c -> Detyping.detype (false,tenv) [] env (mkCoFix c)
  | PSort s -> RSort (loc,s)

and raw_of_eqn tenv env constr construct_nargs branch =
  let make_pat x env b ids =
    let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
    let id = next_name_away_with_default "x" x avoid in
    PatVar (dummy_loc,Name id),(Name id)::env,id::ids
  in
  let rec buildrec ids patlist env n b =
    if n=0 then
      (dummy_loc, ids, 
       [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
       raw_of_pat tenv env b)
    else
      match b with
	| PLambda (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| PLetIn (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| _ ->
	    error "Unsupported branch in case-analysis while printing pattern"
  in 
  buildrec [] [] env construct_nargs branch

let extern_pattern tenv env pat =
  extern true (None,Symbols.current_scopes()) Idset.empty
    (raw_of_pat tenv env pat)
