(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let rec translate_ident_string = function
    (* translate keyword *)
  | ("at" | "IF" | "forall" | "fun" | "match" | "fix" | "cofix" | "for" | "let"
    | "if"  | "then" | "else" | "return" | "mod" | "where" 
    | "exists" | "exists2" | "using" as s) ->
      let s' = s^"_" in
      msgerrnl
      (str ("Warning: '"^
          s^"' is now a keyword; it has been translated to '"^s'^"'"));
      s'
(* Le conflit est en fait surtout avec Eval dans Definition et c'est gere dans
   Ppconstrnew
  | "eval" as s ->
      let s' = s^"_" in
      msgerrnl
      (str ("Warning: '"^
          s^"' is a conflicting ident; it has been translated to '"^s'^"'"));
      s'
*)

  (* avoid _ *)
  | "_" -> 
      msgerrnl (str 
        "Warning: '_' is no longer an ident; it has been translated to 'x_'");
      "x_"
  (* avoid @ *)
  | s when String.contains s '@' ->
      let n = String.index s '@' in 
      translate_ident_string
      (String.sub s 0 n ^ "'at'" ^ String.sub s (n+1) (String.length s -n-1))
  | s -> s

let translate_ident id =
  id_of_string (translate_ident_string (string_of_id id))

let is_coq_root d =
  let d = repr_dirpath d in d <> [] & string_of_id (list_last d) = "Coq"

let is_dir dir s =
  let d = repr_dirpath dir in
  d <> [] & string_of_id (List.hd d) = s

let is_module m = is_dir (Lib.library_dp()) m

let bp = ["BinPos"]
let bz = ["BinInt"]
let bn = ["BinNat"]
let pn = ["nat"]
let zc = ["Zcompare"]
let lo = ["Logic"]
let da = ["Datatypes"]
let zabs = ["Zabs"]
let zo = ["Zorder"]
let zn = ["Znat"]
let wz = ["Wf_Z"]
let mu = ["Mult"]
let pl = ["Plus"]
let mi = ["Minus"]
let le = ["Le"]
let gt = ["Gt"]
let lt = ["Lt"]
let be = ["Between"]
let bo = ["Bool"]
let c dir = 
  let d = repr_dirpath dir in
  if d = [] then [] else [string_of_id (List.hd d)]

let translation_table = [
  (* ZArith *)
"double_moins_un", (bp,"Pdouble_minus_one");
"double_moins_deux", (bp,"Pdouble_minus_two");
"is_double_moins_un", (bp,"Psucc_o_double_minus_one_eq_xO");
"double_moins_un_add_un_xI", (bp,"Pdouble_minus_one_o_succ_eq_xI");
"add_un_Zs", (bz,"Zpos_succ_morphism");
"entier", (bn,"N");
"entier_of_Z", (bz,"Zabs_N");
"Z_of_entier", (bz,"Z_of_N");
"SUPERIEUR", (da,"Gt");
"EGAL", (da,"Eq");
"INFERIEUR", (da,"Lt");
"add", (bp,"Pplus");
"add_carry", (bp,"Pplus_carry");
"add_assoc", (bp,"Pplus_assoc");
"add_sym", (bp,"Pplus_comm");
"add_x_x", (bp,"Pplus_diag");
"add_carry_add", (bp,"Pplus_carry_plus");
"simpl_add_r", (bp,"Pplus_reg_r");
"simpl_add_l", (bp,"Pplus_reg_l");
"simpl_add_carry_r", (bp,"Pplus_carry_reg_r");
"simpl_add_carry_l", (bp,"Pplus_carry_reg_l");
"simpl_times_r", (bp,"Pmult_reg_r");
"simpl_times_l", (bp,"Pmult_reg_l");
(*
"xO_xI_add_double_moins_un", (bp,"xO_xI_plus_double_minus_one");
*)
"double_moins_un_plus_xO_double_moins_un",
  (bp,"Pdouble_minus_one_plus_xO_double_minus_one");
"add_xI_double_moins_un", (bp,"Pplus_xI_double_minus_one");
"add_xO_double_moins_un", (bp,"Pplus_xO_double_minus_one");
"iter_pos_add", (bp,"iter_pos_plus");
"add_no_neutral", (bp,"Pplus_no_neutral");
"add_carry_not_add_un", (bp,"Pplus_carry_no_neutral");
"times_add_distr", (bp,"Pmult_plus_distr_l");
"times_add_distr_l", (bp,"Pmult_plus_distr_r");
"times_true_sub_distr", (bp,"Pmult_minus_distr_l");
"times_sym", (bp,"Pmult_comm");
"times_assoc", (bp,"Pmult_assoc");
"times_convert", (bp,"nat_of_P_mult_morphism");
"true_sub", (bp,"Pminus");
"times_x_1", (bp,"Pmult_1_r");
"times_x_double", (bp,"Pmult_xO_permute_r"); 
   (* Changer en Pmult_xO_distrib_r_reverse *)
"times_x_double_plus_one", (bp,"Pmult_xI_permute_r"); (* Changer ? *)
"times_discr_xO_xI", (bp,"Pmult_xI_mult_xO_discr");
"times_discr_xO", (bp,"Pmult_xO_discr");
"times_one_inversion_l", (bp,"Pmult_1_inversion_l");
"true_sub_convert", (bp,"nat_of_P_minus_morphism");
"compare_true_sub_right", (bp,"Pcompare_minus_r");
"compare_true_sub_left", (bp,"Pcompare_minus_l");
"sub_add", (bp,"Pplus_minus" (* similar to le_plus_minus in Arith *));
"sub_add_one", (bp,"Ppred_succ");
"add_sub_one", (bp,"Psucc_pred");
"add_un", (bp,"Psucc");
"add_un_discr", (bp,"Psucc_discr");
"add_un_not_un", (bp,"Psucc_not_one");
"add_un_inj", (bp,"Psucc_inj");
"xI_add_un_xO", (bp,"xI_succ_xO");
"ZL12", (bp,"Pplus_one_succ_r");
"ZL12bis", (bp,"Pplus_one_succ_l");
"ZL13", (bp,"Pplus_carry_spec");
      (* Changer en Pplus_succ_distrib_r_reverse ? *)
"ZL14", (bp,"Pplus_succ_permute_r");
      (* Changer en Plus_succ_distrib_l_reverse *)
"ZL14bis", (bp,"Pplus_succ_permute_l");
"sub_un", (bp,"Ppred");
"sub_pos", (bp,"Pminus_mask");
"sub_pos_x_x", (bp,"Pminus_mask_diag");
(*"sub_pos_x_x", (bp,"Pminus_mask_diag");*)
"sub_pos_SUPERIEUR", (bp,"Pminus_mask_Gt");
"sub_neg", (bp,"Pminus_mask_carry");
"Zdiv2_pos", (bp,"Pdiv2");
"Pdiv2", (["Zbinary"],"Zdiv2_ge_compat");
"ZERO", (bz,"Z0");
"POS", (bz,"Zpos");
"NEG", (bz,"Zneg");
"Nul", (bn,"N0");
"Pos", (bn,"Npos");
"Un_suivi_de", (bn,"Ndouble_plus_one");
"Zero_suivi_de", (bn,"Ndouble");
"Un_suivi_de_mask", (bp,"Pdouble_plus_one_mask");
"Zero_suivi_de_mask", (bp,"Pdouble_mask");
"ZS", (bp,"double_eq_zero_inversion");
"US", (bp,"double_plus_one_zero_discr");
"USH", (bp,"double_plus_one_eq_one_inversion");
"ZSH", (bp,"double_eq_one_discr");
"ZPminus_add_un_permute", (bz,"ZPminus_succ_permute");
"ZPminus_add_un_permute_Zopp", (bz,"ZPminus_succ_permute_opp");
"ZPminus_double_moins_un_xO_add_un", (bz,"ZPminus_double_minus_one_xO_succ");
"ZL1", (bp,"xO_succ_permute");  (* ?? *)
"Zplus_assoc_r", (bz,"Zplus_assoc_reverse");
"Zplus_sym", (bz,"Zplus_comm");
"Zero_left", (bz,"Zplus_0_l");
"Zero_right", (bz,"Zplus_0_r");
"Zplus_n_O", (bz,"Zplus_0_r_reverse");
"Zplus_unit_left", (bz,"Zplus_0_simpl_l");
"Zplus_unit_right", (bz,"Zplus_0_simpl_l_reverse");
"Zplus_Zopp_expand", (bz,"Zplus_opp_expand");
"Zn_Sn", (bz,"Zsucc_discr");
"Zs", (bz,"Zsucc");
"Psucc_Zs", (bz,"Zpos_succ_permute");
"Zs_pred", (bz,"Zsucc_pred");
"Zpred_Sn", (bz,"Zpred_succ");
"Zminus_n_O", (bz,"Zminus_0_l_reverse");
"Zminus_n_n", (bz,"Zminus_diag_reverse");
"Zminus_Sn_m", (bz,"Zminus_succ_l");
"Zeq_Zminus", (bz,"Zeq_minus");
"Zminus_Zeq", (bz,"Zminus_eq");
"Zplus_minus", (bz,"Zplus_minus_eq");
"Zminus_plus", (bz,"Zminus_plus");
"Zminus_plus_simpl", (bz,"Zminus_plus_simpl_l_reverse");
"Zminus_Zplus_compatible", (bz,"Zminus_plus_simpl_r");
"Zle_plus_minus", (bz,"Zplus_minus");
"Zopp_Zplus", (bz,"Zopp_plus_distr");
"Zopp_Zopp", (bz,"Zopp_involutive");
"Zopp_NEG", (bz,"Zopp_neg");
"Zopp_Zdouble", (bz,"Zopp_double");
"Zopp_Zdouble_plus_one", (bz,"Zopp_double_plus_one");
"Zopp_Zdouble_minus_one", (bz,"Zopp_double_minus_one");
"Zplus_inverse_r", (bz,"Zplus_opp_r");
"Zplus_inverse_l", (bz,"Zplus_opp_l");
"Zplus_S_n", (bz,"Zplus_succ_l");
"Zplus_n_Sm", (bz,"Zplus_succ_r");
"Zplus_Snm_nSm", (bz,"Zplus_succ_comm");
"Zmult_assoc_r", (bz,"Zmult_assoc_reverse");
"Zmult_sym", (bz,"Zmult_comm");
"Zmult_eq", (bz,"Zmult_integral_l");
"Zmult_zero", (bz,"Zmult_integral");
"Zero_mult_left", (bz,"Zmult_0_l");
"Zero_mult_right", (bz,"Zmult_0_r");
"Zmult_1_n", (bz,"Zmult_1_l");
"Zmult_n_1", (bz,"Zmult_1_r");
"Zmult_n_O", (bz,"Zmult_0_r_reverse");
"Zopp_one", (bz,"Zopp_eq_mult_neg_1");
"Zopp_Zmult", (bz,"Zopp_mult_distr_l_reverse");
"Zopp_Zmult_r", (bz,"Zopp_mult_distr_r");
"Zopp_Zmult_l", (bz,"Zopp_mult_distr_l");
"Zmult_Zopp_Zopp", (bz,"Zmult_opp_opp");
"Zmult_Zopp_left", (bz,"Zmult_opp_comm");
"Zmult_Zplus_distr", (bz,"Zmult_plus_distr_r");
"Zmult_plus_distr", (bz,"Zmult_plus_distr_r");
"Zmult_Zminus_distr_r", (bz,"Zmult_minus_distr_l");
"Zmult_Zminus_distr_l", (bz,"Zmult_minus_distr_r");
"Zcompare_Zplus_compatible", (zc,"Zcompare_plus_compat");
"Zcompare_Zplus_compatible2", (zc,"Zplus_compare_compat");
"Zcompare_Zmult_compatible", (zc,"Zcompare_mult_compat");
"inject_nat", (bz,"Z_of_nat");
"inject_nat_complete", (wz,"Z_of_nat_complete");
"inject_nat_complete_inf", (wz,"Z_of_nat_complete_inf");
"inject_nat_prop", (wz,"Z_of_nat_prop");
"inject_nat_set", (wz,"Z_of_nat_set");
"convert", (bp,"nat_of_P");
"anti_convert", (bp,"P_of_succ_nat");
"positive_to_nat", (bp,"Pmult_nat");
"Zopp_intro", (bz,"Zopp_inj");
"plus_iter_add", (bp,"plus_iter_eq_plus");
"compare", (bp,"Pcompare");
"iter_convert", (["Zmisc"],"iter_nat_of_P");
"ZLSI", (bp,"Pcompare_Gt_Lt");
"ZLIS", (bp,"Pcompare_Lt_Gt");
"ZLII", (bp,"Pcompare_Lt_Lt");
"ZLSS", (bp,"Pcompare_Gt_Gt");
  (* Pnat *)
"convert_intro", (pn,"nat_of_P_inj");
"convert_add", (pn,"nat_of_P_plus_morphism");
"convert_add_un", (pn,"Pmult_nat_succ_morphism");
"cvt_add_un", (pn,"nat_of_P_succ_morphism");
"convert_add_carry", (pn,"Pmult_nat_plus_carry_morphism");
"compare_convert_O", (pn,"lt_O_nat_of_P");
"add_verif", (pn,"Pmult_nat_l_plus_morphism");
"ZL2", (pn,"Pmult_nat_r_plus_morphism");
"compare_positive_to_nat_O", (pn,"le_Pmult_nat");
(* Trop spécifique ?
"ZL6", (pn,"Pmult_nat_plus_shift_morphism");
*)
"ZL15", (pn,"Pplus_carry_pred_eq_plus");
"cvt_carry", (pn,"nat_of_P_plus_carry_morphism");
"compare_convert1", (pn,"Pcompare_not_Eq");
"compare_convert_INFERIEUR", (pn,"nat_of_P_lt_Lt_compare_morphism");
"compare_convert_SUPERIEUR", (pn,"nat_of_P_gt_Gt_compare_morphism");
"compare_convert_EGAL", (pn,"Pcompare_Eq_eq");
"convert_compare_INFERIEUR", (pn,"nat_of_P_lt_Lt_compare_complement_morphism");
"convert_compare_SUPERIEUR", (pn,"nat_of_P_gt_Gt_compare_complement_morphism");
"convert_compare_EGAL", (pn,"Pcompare_refl");
"bij1", (pn,"nat_of_P_o_P_of_succ_nat_eq_succ");
"bij2", (pn,"P_of_succ_nat_o_nat_of_P_eq_succ");
"bij3", (pn,"pred_o_P_of_succ_nat_o_nat_of_P_eq_id");
  (* Zcompare *)
"Zcompare_EGAL", (zc,"Zcompare_Eq_iff_eq");
"Zcompare_EGAL_eq", (zc,"Zcompare_Eq_eq");
"Zcompare_x_x", (zc,"Zcompare_refl");
"Zcompare_et_un", (zc,"Zcompare_Gt_not_Lt");
"Zcompare_trans_SUPERIEUR", (zc,"Zcompare_Gt_trans");
"Zcompare_n_S", (zc,"Zcompare_succ_compat");
"SUPERIEUR_POS", (zc,"Zcompare_Gt_spec");
"Zcompare_ANTISYM", (zc,"Zcompare_Gt_Lt_antisym");
"Zcompare_Zs_SUPERIEUR", (zc,"Zcompare_succ_Gt");
"Zcompare_Zopp", (zc,"Zcompare_opp");
"POS_inject", (zn,"Zpos_eq_Z_of_nat_o_nat_of_P");
"absolu", (bz,"Zabs_nat");
"absolu_lt", (zabs,"Zabs_nat_lt" (* "Zabs_nat_lt_morphism_pos" ? *));
"Zeq_add_S", (bz,"Zsucc_inj");
"Znot_eq_S", (bz,"Zsucc_inj_contrapositive");
"Zeq_S", (bz,"Zsucc_eq_compat");
"Zsimpl_plus_l", (bz,"Zplus_reg_l");
"Zplus_simpl", (bz,"Zplus_eq_compat");
"POS_gt_ZERO", (zo,"Zgt_pos_0");
"ZERO_le_POS", (zo,"Zle_0_pos");
"ZERO_le_inj", (zo,"Zle_0_nat");
"NEG_lt_ZERO", (zo,"Zlt_neg_0");
"Zlt_ZERO_pred_le_ZERO", (zo,"Zlt_0_le_0_pred");
"POS_xI", (bz,"Zpos_xI");
"POS_xO", (bz,"Zpos_xO");
"NEG_xI", (bz,"Zneg_xI");
"NEG_xO", (bz,"Zneg_xO");
"POS_add", (bz,"Zpos_plus_distr");
"NEG_add", (bz,"Zneg_plus_distr");
  (* Z Orders *)
"not_Zge", (zo,"Znot_ge_lt");
"not_Zlt", (zo,"Znot_lt_ge");
"not_Zle", (zo,"Znot_le_gt");
"not_Zgt", (zo,"Znot_gt_le");
"Zgt_not_sym", (zo,"Zgt_asym");
"Zlt_not_sym", (zo,"Zlt_asym");
"Zlt_n_n", (zo,"Zlt_irrefl");
"Zgt_antirefl", (zo,"Zgt_irrefl");
"Zgt_reg_l", (zo,"Zplus_gt_compat_l");
"Zgt_reg_r", (zo,"Zplus_gt_compat_r");
"Zlt_reg_l", (zo,"Zplus_lt_compat_l");
"Zlt_reg_r", (zo,"Zplus_lt_compat_r");
"Zle_reg_l", (zo,"Zplus_le_compat_l");
"Zle_reg_r", (zo,"Zplus_le_compat_r");
"Zlt_le_reg", (zo,"Zplus_lt_le_compat");
"Zle_lt_reg", (zo,"Zplus_le_lt_compat");
"Zle_plus_plus", (zo,"Zplus_le_compat");
"Zlt_Zplus", (zo,"Zplus_lt_compat");
"Zle_O_plus", (zo,"Zplus_le_0_compat");
"Zle_mult_simpl", (zo,"Zmult_le_reg_r");
"Zge_mult_simpl", (zo,"Zmult_ge_reg_r");
"Zgt_mult_simpl", (zo,"Zmult_gt_reg_r");
"Zsimpl_gt_plus_l", (zo,"Zplus_gt_reg_l");
"Zsimpl_gt_plus_r", (zo,"Zplus_gt_reg_r");
"Zsimpl_le_plus_l", (zo,"Zplus_le_reg_l");
"Zsimpl_le_plus_r", (zo,"Zplus_le_reg_r");
"Zsimpl_lt_plus_l", (zo,"Zplus_lt_reg_l");
"Zsimpl_lt_plus_r", (zo,"Zplus_lt_reg_r");
"Zlt_Zmult_right2", (zo,"Zmult_gt_0_lt_reg_r");
"Zlt_Zmult_right", (zo,"Zmult_gt_0_lt_compat_r");
"Zle_Zmult_right2", (zo,"Zmult_gt_0_le_reg_r");
"Zle_Zmult_right", (zo,"Zmult_gt_0_le_compat_r");
"Zgt_Zmult_right", (zo,"Zmult_gt_compat_r");
"Zgt_Zmult_left", (zo,"Zmult_gt_compat_l");
"Zlt_Zmult_left", (zo,"Zmult_gt_0_lt_compat_l");
"Zcompare_Zmult_right", (zc,"Zmult_compare_compat_r");
"Zcompare_Zmult_left", (zc,"Zmult_compare_compat_l");
"Zplus_Zmult_2", (bz,"Zplus_diag_eq_mult_2");
"Zmult_Sm_n", (bz,"Zmult_succ_l_reverse");
"Zmult_n_Sm", (bz,"Zmult_succ_r_reverse");
"Zmult_le", (zo,"Zmult_le_0_reg_r");
"Zmult_reg_left", (bz,"Zmult_reg_l");
"Zmult_reg_right", (bz,"Zmult_reg_r");
"Zle_ZERO_mult", (zo,"Zmult_le_0_compat");
"Zgt_ZERO_mult", (zo,"Zmult_gt_0_compat");
"Zle_mult", (zo,"Zmult_gt_0_le_0_compat");
"Zmult_lt", (zo,"Zmult_gt_0_lt_0_reg_r");
"Zmult_gt", (zo,"Zmult_gt_0_reg_l");
"Zle_Zmult_pos_right", (zo,"Zmult_le_compat_r");
"Zle_Zmult_pos_left", (zo,"Zmult_le_compat_l");
"Zge_Zmult_pos_right", (zo,"Zmult_ge_compat_r");
"Zge_Zmult_pos_left", (zo,"Zmult_ge_compat_l");
"Zge_Zmult_pos_compat", (zo,"Zmult_ge_compat");
"Zlt_Zcompare", (zo,"Zlt_compare");
"Zle_Zcompare", (zo,"Zle_compare");
"Zgt_Zcompare", (zo,"Zgt_compare");
"Zge_Zcompare", (zo,"Zge_compare");
  (* ex-IntMap *)
"convert_xH", (pn,"nat_of_P_xH");
"convert_xO", (pn,"nat_of_P_xO");
"convert_xI", (pn,"nat_of_P_xI");
"positive_to_nat_mult", (pn,"Pmult_nat_mult_permute");
"positive_to_nat_2", (pn,"Pmult_nat_2_mult_2_permute");
"positive_to_nat_4", (pn,"Pmult_nat_4_mult_2_permute");
  (* ZArith and Arith orders *)
"Zle_refl", (zo,"Zeq_le");
"Zle_n", (zo,"Zle_refl");
"Zle_trans_S", (zo,"Zle_succ_le");
"Zgt_trans_S", (zo,"Zge_trans_succ");
"Zgt_S", (zo,"Zgt_succ_gt_or_eq");
"Zle_Sn_n", (zo,"Znot_le_succ");
"Zlt_n_Sn", (zo,"Zlt_succ");
"Zlt_S", (zo,"Zlt_lt_succ");
"Zlt_n_S", (zo,"Zsucc_lt_compat");
"Zle_n_S", (zo,"Zsucc_le_compat");
"Zgt_n_S", (zo,"Zsucc_gt_compat");
"Zlt_S_n", (zo,"Zsucc_lt_reg");
"Zgt_S_n", (zo,"Zsucc_gt_reg");
"Zle_S_n", (zo,"Zsucc_le_reg");
"Zle_0_plus", (zo,"Zplus_le_0_compat");
"Zgt_Sn_n", (zo,"Zgt_succ");
"Zgt_le_S", (zo,"Zgt_le_succ");
"Zgt_S_le", (zo,"Zgt_succ_le");
"Zle_S_gt", (zo,"Zlt_succ_gt");
"Zle_gt_S", (zo,"Zlt_gt_succ");
"Zgt_pred", (zo,"Zgt_succ_pred");
"Zlt_pred", (zo,"Zlt_succ_pred");
"Zgt0_le_pred", (zo,"Zgt_0_le_0_pred");
"Z_O_1", (zo,"Zlt_0_1");
"Zle_NEG_POS", (zo,"Zle_neg_pos");
"Zle_n_Sn", (zo,"Zle_succ");
"Zle_pred_n", (zo,"Zle_pred");
"Zlt_pred_n_n", (zo,"Zlt_pred");
"Zlt_le_S", (zo,"Zlt_le_succ");
"Zlt_n_Sm_le", (zo,"Zlt_succ_le");
"Zle_lt_n_Sm", (zo,"Zle_lt_succ");
"Zle_le_S", (zo,"Zle_le_succ");
"Zlt_minus", (zo,"Zlt_minus_simpl_swap");
"le_trans_S", (le,"le_Sn_le");
(* Znumtheory *)
"Zdivide_Zmod", ([],"Zdivide_mod");
"Zmod_Zdivide", ([],"Zmod_divide");
"Zdivide_mult_left", ([],"Zmult_divide_compat_l");
"Zdivide_mult_right", ([],"Zmult_divide_compat_r");
"Zdivide_opp", ([],"Zdivide_opp_r");
"Zdivide_opp_rev", ([],"Zdivide_opp_r_rev");
"Zdivide_opp_left", ([],"Zdivide_opp_l");
"Zdivide_opp_left_rev", ([],"Zdivide_opp_l_rev");
"Zdivide_right", ([],"Zdivide_mult_r");
"Zdivide_left", ([],"Zdivide_mult_l");
"Zdivide_plus", ([],"Zdivide_plus_r");
"Zdivide_minus", ([],"Zdivide_minus_l");
"Zdivide_a_ab", ([],"Zdivide_factor_r");
"Zdivide_a_ba", ([],"Zdivide_factor_l");
(* Arith *)
(* Peano.v
"plus_n_O", ("plus_0_r_reverse");
"plus_O_n", ("plus_0_l");
*)
"plus_assoc_l", (pl,"plus_assoc");
"plus_assoc_r", (pl,"plus_assoc_reverse");
"plus_sym", (pl,"plus_comm");
"mult_sym", (mu,"mult_comm");
"max_sym", (["Max"],"max_comm");
"min_sym", (["Min"],"min_comm");
"gt_not_sym", (gt,"gt_asym");
"lt_not_sym", (lt,"lt_asym");
"gt_antirefl", (gt,"gt_irrefl");
"lt_n_n", (lt,"lt_irrefl");
(* Trop utilisé dans CoqBook | "le_n" -> "le_refl"*)
"simpl_plus_l", (pl,"plus_reg_l");
"simpl_plus_r", (pl,"plus_reg_r");
"fact_growing", (["Factorial"],"fact_le");
"mult_assoc_l", (mu,"mult_assoc");
"mult_assoc_r", (mu,"mult_assoc_reverse");
"mult_plus_distr", (mu,"mult_plus_distr_r");
"mult_plus_distr_r", (mu,"mult_plus_distr_l");
"mult_minus_distr", (mu,"mult_minus_distr_r");
"mult_1_n", (mu,"mult_1_l");
"mult_n_1", (mu,"mult_1_r");
(* Peano.v
"mult_n_O", ("mult_O_r_reverse");
"mult_n_Sm", ("mult_S_r_reverse");
*)
"mult_le", (mu,"mult_le_compat_l");
"le_mult_right", (mu,"mult_le_compat_r");
"le_mult_mult", (mu,"mult_le_compat");
"mult_lt", (mu,"mult_S_lt_compat_l");
"lt_mult_right", (mu,"mult_lt_compat_r");
"mult_le_conv_1", (mu,"mult_S_le_reg_l");
"exists", (be,"exists_between");
"IHexists", ([],"IHexists_between");
(* Peano.v
"pred_Sn", ("pred_S");
*)
"inj_minus_aux", (mi,"not_le_minus_0");
"minus_x_x", (mi,"minus_diag");
"minus_plus_simpl", (mi,"minus_plus_simpl_l_reverse");
"gt_reg_l", (gt,"plus_gt_compat_l");
"le_reg_l", (pl,"plus_le_compat_l");
"le_reg_r", (pl,"plus_le_compat_r");
"lt_reg_l", (pl,"plus_lt_compat_l");
"lt_reg_r", (pl,"plus_lt_compat_r");
"le_plus_plus", (pl,"plus_le_compat");
"le_lt_plus_plus", (pl,"plus_le_lt_compat");
"lt_le_plus_plus", (pl,"plus_lt_le_compat");
"lt_plus_plus", (pl,"plus_lt_compat");
"plus_simpl_l", (pl,"plus_reg_l");
"simpl_gt_plus_l", (pl,"plus_gt_reg_l");
"simpl_le_plus_l", (pl,"plus_le_reg_l");
"simpl_lt_plus_l", (pl,"plus_lt_reg_l");
(* Noms sur le principe de ceux de Z
"le_n_S", ("S_le_compat");
"le_n_Sn", ("le_S");
(*"le_O_n", ("??" *));
"le_pred_n", ("le_pred");
"le_trans_S", ("le_S_le");
"le_S_n", ("S_le_reg");
"le_Sn_O", ("not_le_S_O");
"le_Sn_n", ("not_le_S");
*)
  (* Init *)
"IF", (lo,"IF_then_else");
  (* Lists *)
"idempot_rev", (["List"],"rev_involutive");
"forall", (["Streams"],"HereAndFurther");
  (* Bool *)
"orb_sym", (bo,"orb_comm");
"andb_sym", (bo,"andb_comm");
  (* Ring *)
"SR_plus_sym", (["Ring_theory"],"SR_plus_comm");
"SR_mult_sym", (["Ring_theory"],"SR_mult_comm");
"Th_plus_sym", (["Ring_theory"],"Th_plus_comm");
"Th_mul_sym", (["Ring_theory"],"Th_mult_comm");
"SSR_plus_sym", (["Setoid_ring_theory"],"SSR_plus_comm");
"SSR_mult_sym", (["Setoid_ring_theory"],"SSR_mult_comm");
"STh_plus_sym", (["Setoid_ring_theory"],"STh_plus_comm");
"STh_mul_sym", (["Setoid_ring_theory"],"STh_mult_comm");
  (* Reals *)
(*
"Rabsolu", ("Rabs");
"Rabsolu_pos_lt", ("Rabs_pos_lt");
"Rabsolu_no_R0", ("Rabs_no_R0");
"Rabsolu_Rabsolu", ("Rabs_Rabs");
"Rabsolu_mult", ("Rabs_mult");
"Rabsolu_triang", ("Rabs_triang");
"Rabsolu_Ropp", ("Rabs_Ropp");
"Rabsolu_right", ("Rabs_right");
...
"case_Rabsolu", ("case_Rabs");
"Pow_Rabsolu", ("Pow_Rabs");
...
*)
(* Raxioms *)
"complet", ([],"completeness");
"complet_weak", ([],"completeness_weak");
"Rle_sym1", ([],"Rle_ge");
"Rmin_sym", ([],"Rmin_comm");
"Rplus_sym", ([],"Rplus_comm");
"Rmult_sym", ([],"Rmult_comm");
"Rsqr_times", ([],"Rsqr_mult");
"sqrt_times", ([],"sqrt_mult");
"Rmult_1l", ([],"Rmult_1_l");
"Rplus_Ol", ([],"Rplus_0_l");
"Rplus_Ropp_r", ([],"Rplus_opp_r");
"Rmult_Rplus_distr", ([],"Rmult_plus_distr_l");
"Rlt_antisym", ([],"Rlt_asym");
(* RIneq *)
"Rlt_antirefl", ([],"Rlt_irrefl");
"Rlt_compatibility", ([],"Rplus_lt_compat_l");
"Rgt_plus_plus_r", ([],"Rplus_gt_compat_l");
"Rgt_r_plus_plus", ([],"Rplus_gt_reg_l");
"Rge_plus_plus_r", ([],"Rplus_ge_compat_l");
"Rge_r_plus_plus", ([],"Rplus_ge_reg_l");
(* Si on en change un, il faut changer tous les autres R*_monotony *)
"Rlt_monotony", ([],"Rmult_lt_compat_l");
"Rlt_monotony_r", ([],"Rmult_lt_compat_r");
"Rlt_monotony_contra", ([],"Rmult_lt_reg_l");
(*"Rlt_monotony_rev", ([],"Rmult_lt_reg_l");*)
"Rlt_anti_monotony", ([],"Rmult_lt_gt_compat_neg_l");
"Rle_monotony", ([],"Rmult_le_compat_l");
"Rle_monotony_r", ([],"Rmult_le_compat_r");
"Rle_monotony_contra", ([],"Rmult_le_reg_l");
"Rle_anti_monotony1", ([],"Rmult_le_compat_neg_l");
"Rle_anti_monotony", ([],"Rmult_le_ge_compat_neg_l");
"Rge_monotony", ([],"Rmult_ge_compat_r");
"Rge_ge_eq", ([],"Rge_antisym");
(* Le reste de RIneq *)
"imp_not_Req", ([],"Rlt_dichotomy_converse");
"Req_EM", ([],"Req_dec");
"total_order", ([],"Rtotal_order");
"not_Req", ([],"Rdichotomy");
(* "Rlt_le" -> c dir,"Rlt_le_weak" ? *)
"not_Rle", ([],"Rnot_le_lt");
"not_Rge", ([],"Rnot_ge_lt");
"Rlt_le_not", ([],"Rlt_not_le");
"Rle_not", ([],"Rgt_not_le");
"Rle_not_lt", ([],"Rle_not_lt");
"Rlt_ge_not", ([],"Rlt_not_ge");
"eq_Rle", ([],"Req_le");
"eq_Rge", ([],"Req_ge");
"eq_Rle_sym", ([],"Req_le_sym");
"eq_Rge_sym", ([],"Req_ge_sym");
(* "Rle_le_eq" -> ?   x<=y/\y<=x <-> x=y *)
"Rlt_rew", ([],"Rlt_eq_compat");
"total_order_Rlt", ([],"Rlt_dec");
"total_order_Rle", ([],"Rle_dec");
"total_order_Rgt", ([],"Rgt_dec");
"total_order_Rge", ([],"Rge_dec");
"total_order_Rlt_Rle", ([],"Rlt_le_dec");
(* "Rle_or_lt" -> c dir,"Rle_or_lt"*)
"total_order_Rle_Rlt_eq", ([],"Rle_lt_or_eq_dec");
(* "inser_trans_R" -> c dir,"Rle_lt_inser_trans" ?*)
(* "Rplus_ne" -> c dir,"Rplus_0_r_l" ? *)
"Rplus_Or", ([],"Rplus_0_r");
"Rplus_Ropp_l", ([],"Rplus_opp_l");
"Rplus_Ropp", ([],"Rplus_opp_r_uniq");
"Rplus_plus_r", ([],"Rplus_eq_compat_l");
"r_Rplus_plus", ([],"Rplus_eq_reg_l");
"Rplus_ne_i", ([],"Rplus_0_r_uniq");
"Rmult_Or", ([],"Rmult_0_r");
"Rmult_Ol", ([],"Rmult_0_l");
(* "Rmult_ne" -> c dir,"Rmult_1_l_r" ? *)
"Rmult_1r", ([],"Rmult_1_r");
"Rmult_mult_r", ([],"Rmult_eq_compat_l");
"r_Rmult_mult", ([],"Rmult_eq_reg_l");
"without_div_Od", ([],"Rmult_integral");
"without_div_Oi", ([],"Rmult_eq_0_compat");
"without_div_Oi1", ([],"Rmult_eq_0_compat_r");
"without_div_Oi2", ([],"Rmult_eq_0_compat_l");
"without_div_O_contr", ([],"Rmult_neq_0_reg");
"mult_non_zero", ([],"Rmult_integral_contrapositive");
"Rmult_Rplus_distrl", ([],"Rmult_plus_distr_r");
"Rsqr_O", ([],"Rsqr_0");
"Rsqr_r_R0", ([],"Rsqr_0_uniq");
"eq_Ropp", ([],"Ropp_eq_compat");
"Ropp_O", ([],"Ropp_0");
"eq_RoppO", ([],"Ropp_eq_0_compat");
"Ropp_Ropp", ([],"Ropp_involutive");
"Ropp_neq", ([],"Ropp_neq_0_compat");
"Ropp_distr1", ([],"Ropp_plus_distr");
"Ropp_mul1", ([],"Ropp_mult_distr_l_reverse");
"Ropp_mul2", ([],"Rmult_opp_opp");
"Ropp_mul3", ([],"Ropp_mult_distr_r_reverse");
"minus_R0", ([],"Rminus_0_r");
"Rminus_Ropp", ([],"Rminus_0_l");
"Ropp_distr2", ([],"Ropp_minus_distr");
"Ropp_distr3", ([],"Ropp_minus_distr'");
"eq_Rminus", ([],"Rminus_diag_eq");
"Rminus_eq", ([],"Rminus_diag_uniq");
"Rminus_eq_right", ([],"Rminus_diag_uniq_sym");
"Rplus_Rminus", ([],"Rplus_minus");
(*
"Rminus_eq_contra", ([],"Rminus_diag_neq");
"Rminus_not_eq", ([],"Rminus_neq_diag_sym");
 "Rminus_not_eq_right" -> ?
*)
"Rminus_distr", ([],"Rmult_minus_distr_l");
"Rinv_R1", ([],"Rinv_1");
"Rinv_neq_R0", ([],"Rinv_neq_0_compat");
"Rinv_Rinv", ([],"Rinv_involutive");
"Rinv_Rmult", ([],"Rinv_mult_distr");
"Ropp_Rinv", ([],"Ropp_inv_permute");
(* "Rinv_r_simpl_r" -> OK ? *)
(* "Rinv_r_simpl_l" -> OK ? *)
(* "Rinv_r_simpl_m" -> OK ? *)
"Rinv_Rmult_simpl", ([],"Rinv_mult_simpl"); (* ? *)
"Rlt_compatibility_r", ([],"Rplus_lt_compat_r");
"Rlt_anti_compatibility", ([],"Rplus_lt_reg_r");
"Rle_compatibility", ([],"Rplus_le_compat_l");
"Rle_compatibility_r", ([],"Rplus_le_compat_r");
"Rle_anti_compatibility", ([],"Rplus_le_reg_l");
(* "sum_inequa_Rle_lt" -> ? *)
"Rplus_lt", ([],"Rplus_lt_compat");
"Rplus_le", ([],"Rplus_le_compat");
"Rplus_lt_le_lt", ([],"Rplus_lt_le_compat");
"Rplus_le_lt_lt", ([],"Rplus_le_lt_compat");
"Rgt_Ropp", ([],"Ropp_gt_lt_contravar");
"Rlt_Ropp", ([],"Ropp_lt_gt_contravar");
"Ropp_Rlt", ([],"Ropp_lt_cancel");  (* ?? *)
"Rlt_Ropp1", ([],"Ropp_lt_contravar");
"Rle_Ropp", ([],"Ropp_le_ge_contravar");
"Ropp_Rle", ([],"Ropp_le_cancel");
"Rle_Ropp1", ([],"Ropp_le_contravar");
"Rge_Ropp", ([],"Ropp_ge_le_contravar");
"Rlt_RO_Ropp", ([],"Ropp_0_lt_gt_contravar");
"Rgt_RO_Ropp", ([],"Ropp_0_gt_lt_contravar");
"Rle_RO_Ropp", ([],"Ropp_0_le_ge_contravar");
"Rge_RO_Ropp", ([],"Ropp_0_ge_le_contravar");
(* ... cf plus haut pour les lemmes intermediaires *)
"Rle_Rmult_comp", ([],"Rmult_le_compat");
   (* Expliciter que la contrainte est r2>0 dans r1<r2 et non 0<r1 ce
      qui est plus général mais différent de Rmult_le_compat ? *)
"Rmult_lt", ([],"Rmult_gt_0_lt_compat"); (* Hybride aussi *)
"Rmult_lt_0", ([],"Rmult_ge_0_gt_0_lt_compat"); (* Un truc hybride *)
(*
 "Rlt_minus" -> 
 "Rle_minus" -> 
 "Rminus_lt" -> 
 "Rminus_le" -> 
 "tech_Rplus" -> 
*)
"pos_Rsqr", ([],"Rle_0_sqr");
"pos_Rsqr1", ([],"Rlt_0_sqr");
"Rlt_R0_R1", ([],"Rlt_0_1");
"Rle_R0_R1", ([],"Rle_0_1");
"Rlt_Rinv", ([],"Rinv_0_lt_compat");
"Rlt_Rinv2", ([],"Rinv_lt_0_compat");
"Rinv_lt", ([],"Rinv_lt_contravar");
"Rlt_Rinv_R1", ([],"Rinv_1_lt_contravar");
"Rlt_not_ge", ([],"Rnot_lt_ge");
"Rgt_not_le", ([],"Rnot_gt_le");
(*
 "Rgt_ge" -> "Rgt_ge_weak" ?
*)
"Rlt_sym", ([],"Rlt_gt_iff");
(* | "Rle_sym1" -> c dir,"Rle_ge" OK *)
"Rle_sym2", ([],"Rge_le");
"Rle_sym", ([],"Rle_ge_iff");
(*
 "Rge_gt_trans" -> OK
 "Rgt_ge_trans" -> OK
 "Rgt_trans" -> OK
 "Rge_trans" -> OK
*)
"Rgt_RoppO", ([],"Ropp_lt_gt_0_contravar");
"Rlt_RoppO", ([],"Ropp_gt_lt_0_contravar");
"Rlt_r_plus_R1", ([],"Rle_lt_0_plus_1");
"Rlt_r_r_plus_R1", ([],"Rlt_plus_1");
(* "tech_Rgt_minus" -> ? *)
(* OK, cf plus haut
"Rgt_r_plus_plus", ([],"Rplus_gt_reg_l");
"Rgt_plus_plus_r", ([],"Rplus_gt_compat_l");
"Rge_plus_plus_r", ([],"Rplus_ge_compat_l");
"Rge_r_plus_plus", ([],"Rplus_ge_reg_l");
"Rge_monotony" ->  *)
(*
 "Rgt_minus" -> 
 "minus_Rgt" -> 
 "Rge_minus" -> 
 "minus_Rge" -> 
*)
"Rmult_gt", ([],"Rmult_gt_0_compat");
"Rmult_lt_pos", ([],"Rmult_lt_0_compat");  (* lt_0 ou 0_lt ?? *)
"Rplus_eq_R0_l", ([],"Rplus_eq_0_l"); (* ? *)
"Rplus_eq_R0", ([],"Rplus_eq_R0");
"Rplus_Rsr_eq_R0_l", ([],"Rplus_sqr_eq_0_l");
"Rplus_Rsr_eq_R0", ([],"Rplus_sqr_eq_0");
(*
 "S_INR" -> 
 "S_O_plus_INR" -> 
 "plus_INR" -> 
 "minus_INR" -> 
 "mult_INR" -> 
 "lt_INR_0" -> 
 "lt_INR" -> 
 "INR_lt_1" -> 
 "INR_pos" -> 
 "pos_INR" -> 
 "INR_lt" -> 
 "le_INR" -> 
 "not_INR_O" -> 
 "not_O_INR" -> 
 "not_nm_INR" -> 
 "INR_eq" -> 
 "INR_le" -> 
 "not_1_INR" -> 
 "IZN" -> 
 "INR_IZR_INZ" -> 
 "plus_IZR_NEG_POS" -> 
 "plus_IZR" -> 
 "mult_IZR" -> 
 "Ropp_Ropp_IZR" -> 
 "Z_R_minus" -> 
 "lt_O_IZR" -> 
 "lt_IZR" -> 
 "eq_IZR_R0" -> 
 "eq_IZR" -> 
 "not_O_IZR" -> 
 "le_O_IZR" -> 
 "le_IZR" -> 
 "le_IZR_R1" -> 
 "IZR_ge" -> 
 "IZR_le" -> 
 "IZR_lt" -> 
 "one_IZR_lt1" -> 
 "one_IZR_r_R1" -> 
 "single_z_r_R1" -> 
 "tech_single_z_r_R1" -> 
 "prod_neq_R0" -> 
 "Rmult_le_pos" -> 
 "double" -> 
 "double_var" -> 
*)
"gt0_plus_gt0_is_gt0", ([],"Rplus_lt_0_compat");
"ge0_plus_gt0_is_gt0", ([],"Rplus_le_lt_0_compat");
"gt0_plus_ge0_is_gt0", ([],"Rplus_lt_le_0_compat");
"ge0_plus_ge0_is_ge0", ([],"Rplus_le_le_0_compat");
(*
 "plus_le_is_le" -> ?
 "plus_lt_is_lt" -> ?
*)
"Rmult_lt2", ([],"Rmult_le_0_lt_compat");
(* "Rge_ge_eq" -> c dir,"Rge_antisym" OK *)
]

let translate_v7_string dir s =
  try
    let d,s' = List.assoc s translation_table in
    (if d=[] then c dir else d),s'
  with Not_found ->
  (* Special cases *)
  match s with
  (* Init *)
  | "relation" when is_module "Datatypes" or is_dir dir "Datatypes"
      -> da,"comparison"
  | "Op" when is_module "Datatypes" or is_dir dir "Datatypes"
      -> da,"CompOpp"
  (* BinPos *)
  | "times" when not (is_module "Mapfold") -> bp,"Pmult"
  (* Reals *)
  | s when String.length s >= 7 & (String.sub s 0 7 = "Rabsolu") ->
      c dir,
      "Rabs"^(String.sub s 7 (String.length s - 7))
  | s when String.length s >= 7 &
      (String.sub s (String.length s - 7) 7 = "Rabsolu") -> c dir,
      "R"^(String.sub s 0 (String.length s - 7))^"abs"
  | s when String.length s >= 7 & 
      let s' = String.sub s 0 7 in
      (s' = "unicite" or s' = "unicity") -> c dir,
      "uniqueness"^(String.sub s 7 (String.length s - 7))
  | s when String.length s >= 3 &
      let s' = String.sub s 0 3 in
      s' = "gcd" -> c dir, "Zis_gcd"^(String.sub s 3 (String.length s - 3))
  (* Default *)
  | x -> [],x


let id_of_v7_string s =
  id_of_string (if !Options.v7 then s else snd (translate_v7_string empty_dirpath s))

let v7_to_v8_dir_id dir id =
  if Options.do_translate() then
    let s = string_of_id id in
    let dir',s =
      if (is_coq_root (Lib.library_dp()) or is_coq_root dir)
      then translate_v7_string dir s else [], s in
    dir',id_of_string (translate_ident_string s)
  else [],id

let v7_to_v8_id id = snd (v7_to_v8_dir_id empty_dirpath id)

let short_names =
  List.map (fun x -> snd (snd x)) translation_table

let is_new_name s =
  Options.do_translate () &
  (List.mem s short_names or
  s = "comparison" or s = "CompOpp" or s = "Pmult" or
  (String.length s >= 4 & String.sub s 0 4 = "Rabs") or
  (String.length s >= 4 & String.sub s (String.length s - 3) 3 = "abs"
                        & s.[0] = 'R') or
  (String.length s >= 10 & String.sub s 0 10 = "uniqueness"))

let v7_to_v8_dir fulldir dir =
  if Options.do_translate () & dir <> empty_dirpath then
    let update s =
      let l = List.map string_of_id (repr_dirpath dir) in
      make_dirpath (List.map id_of_string (s :: List.tl l))
    in
    let l = List.map string_of_id (repr_dirpath fulldir) in
    if l = [ "List"; "Lists"; "Coq" ] then update "MonoList"
    else if l = [ "PolyList"; "Lists"; "Coq" ] then update "List"
    else dir
  else dir

let shortest_qualid_of_v7_global ctx ref =
  let fulldir,_ = repr_path (sp_of_global ref) in
  let dir,id = repr_qualid (shortest_qualid_of_global ctx ref) in
  let dir',id = v7_to_v8_dir_id fulldir id in
  let dir'' =
    if dir' = [] then
      (* A name that is not renamed *)
      if dir = empty_dirpath & is_new_name (string_of_id id)
      then 
        (* An unqualified name that is not renamed but which coincides *)
        (* with a new name: force qualification unless it is a variable *)
        if fulldir <> empty_dirpath & not (is_coq_root fulldir)
        then make_dirpath [List.hd (repr_dirpath fulldir)] 
        else empty_dirpath
      else v7_to_v8_dir fulldir dir
    else
      (* A stdlib name that has been renamed *)
      try
        let d,_ = repr_path (Nametab.full_name_cci (make_short_qualid id)) in
        if not (is_coq_root d) then 
          (* The user has defined id, then we qualify the new name *)
          v7_to_v8_dir fulldir (make_dirpath (List.map id_of_string dir'))
        else empty_dirpath
      with Not_found -> v7_to_v8_dir fulldir dir in
  make_qualid dir'' id

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_v7_global vars r)
  with Not_found ->
    (* happens in debugger *)
    Ident (loc,id_of_string (raw_string_of_ref r))

(************************************************************************)
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
      List.iter2 (fun (id1,i1,bl1,a1,b1) (id2,i2,bl2,a2,b2) ->
        if id1<>id2 || i1<>i2 then failwith "not same fix";
        check_same_fix_binder bl1 bl2;
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CCoFix(_,(_,id1),fl1), CCoFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,bl1,a1,b1) (id2,bl2,a2,b2) ->
        if id1<>id2 then failwith "not same fix";
        check_same_fix_binder bl1 bl2;
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

and check_same_fix_binder bl1 bl2 =
  List.iter2 (fun b1 b2 ->
    match b1,b2 with
        LocalRawAssum(nal1,ty1), LocalRawAssum(nal2,ty2) ->
          check_same_binder (nal1,ty1) (nal2,ty2)
      | LocalRawDef(na1,def1), LocalRawDef(na2,def2) ->
          check_same_binder ([na1],def1) ([na2],def2)          
      | _ -> failwith "not same binder") bl1 bl2

let same c d = try check_same_type c d; true with _ -> false

(* Idem for rawconstr *)
let option_iter2 f o1 o2 = 
  match o1, o2 with
      Some o1, Some o2 -> f o1 o2
    | None, None -> ()
    | _ -> failwith "option"

let array_iter2 f v1 v2 =
  List.iter2 f (Array.to_list v1) (Array.to_list v2)

let rec same_patt p1 p2 =
  match p1, p2 with
      PatVar(_,na1), PatVar(_,na2) -> if na1<>na2 then failwith "PatVar"
    | PatCstr(_,c1,pl1,al1), PatCstr(_,c2,pl2,al2) ->
        if c1<>c2 || al1 <> al2 then failwith "PatCstr";
        List.iter2 same_patt pl1 pl2
    | _ -> failwith "same_patt"

let rec same_raw c d =
  match c,d with
   | RRef(_,gr1), RRef(_,gr2) -> if gr1<>gr2 then failwith "RRef"
   | RVar(_,id1), RVar(_,id2) -> if id1<>id2 then failwith "RVar"
   | REvar(_,e1,a1), REvar(_,e2,a2) ->
       if e1 <> e2 then failwith "REvar";
       option_iter2(List.iter2 same_raw) a1 a2
  | RPatVar(_,pv1), RPatVar(_,pv2) -> if pv1<>pv2 then failwith "RPatVar"
  | RApp(_,f1,a1), RApp(_,f2,a2) ->
      List.iter2 same_raw (f1::a1) (f2::a2)
  | RLambda(_,na1,t1,m1), RLambda(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RLambda";
      same_raw t1 t2; same_raw m1 m2
  | RProd(_,na1,t1,m1), RProd(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RProd";
      same_raw t1 t2; same_raw m1 m2
  | RLetIn(_,na1,t1,m1), RLetIn(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RLetIn";
      same_raw t1 t2; same_raw m1 m2
  | RCases(_,_,c1,b1), RCases(_,_,c2,b2) ->
      List.iter2
        (fun (t1,{contents=(al1,oind1)}) (t2,{contents=(al2,oind2)}) ->
          same_raw t1 t2;
          if al1 <> al2 then failwith "RCases";
          option_iter2(fun (_,i1,nl1) (_,i2,nl2) ->
            if i1<>i2 || nl1 <> nl2 then failwith "RCases") oind1 oind2) c1 c2;
      List.iter2 (fun (_,_,pl1,b1) (_,_,pl2,b2) ->
        List.iter2 same_patt pl1 pl2;
        same_raw b1 b2) b1 b2
  | ROrderedCase(_,_,_,c1,v1,_), ROrderedCase(_,_,_,c2,v2,_) ->
      same_raw c1 c2;
      array_iter2 same_raw v1 v2
  | RLetTuple(_,nl1,_,b1,c1), RLetTuple(_,nl2,_,b2,c2) ->
      if nl1<>nl2 then failwith "RLetTuple";
      same_raw b1 b2;
      same_raw c1 c2
  | RIf(_,b1,_,t1,e1),RIf(_,b2,_,t2,e2) ->
      same_raw b1 b2; same_raw t1 t2; same_raw e1 e2
  | RRec(_,fk1,na1,bl1,ty1,def1), RRec(_,fk2,na2,bl2,ty2,def2) ->
      if fk1 <> fk2 || na1 <> na2 then failwith "RRec";
      array_iter2
        (List.iter2 (fun (na1,bd1,ty1) (na2,bd2,ty2) ->
          if na1<>na2 then failwith "RRec";
          option_iter2 same_raw bd1 bd2;
          same_raw ty1 ty2)) bl1 bl2;
      array_iter2 same_raw ty1 ty2;
      array_iter2 same_raw def1 def2
  | RSort(_,s1), RSort(_,s2) -> if s1<>s2 then failwith "RSort"
  | RHole _, _ -> ()
  | _, RHole _ -> ()
  | RCast(_,c1,_),r2 -> same_raw c1 r2
  | r1, RCast(_,c2,_) -> same_raw r1 c2
  | RDynamic(_,d1), RDynamic(_,d2) -> if d1<>d2 then failwith"RDynamic"
  | _ -> failwith "same_raw"
     
let same_rawconstr c d = 
  try same_raw c d; true
  with Failure _ | Invalid_argument _ -> false

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let make_current_scopes (scopt,scopes) = 
  option_fold_right push_scope scopt scopes

let has_curly_brackets ntn =
  String.length ntn >= 6 & (String.sub ntn 0 6 = "{ _ } " or
    String.sub ntn (String.length ntn - 6) 6 = " { _ }" or
    string_string_contains ntn " { _ } ")

let rec wildcards ntn n =
  if n = String.length ntn then []
  else let l = spaces ntn (n+1) in if ntn.[n] = '_' then n::l else l
and spaces ntn n =
  if n = String.length ntn then []
  else if ntn.[n] = ' ' then wildcards ntn (n+1) else spaces ntn (n+1)

let expand_curly_brackets make_ntn ntn l =
  let ntn' = ref ntn in
  let rec expand_ntn i =
    function
    | [] -> []
    | a::l ->
        let a' = 
          let p = List.nth (wildcards !ntn' 0) i - 2 in
          if p>=0 & p+5 <= String.length !ntn' & String.sub !ntn' p 5 = "{ _ }"
          then begin
            ntn' := 
              String.sub !ntn' 0 p ^ "_" ^ 
              String.sub !ntn' (p+5) (String.length !ntn' -p-5);
            make_ntn "{ _ }" [a] end
          else a in
        a' :: expand_ntn (i+1) l in
  let l = expand_ntn 0 l in
  (* side effect *)
  make_ntn !ntn' l

let make_notation loc ntn l =
  if has_curly_brackets ntn
  then expand_curly_brackets (fun n l -> CNotation (loc,n,l)) ntn l
  else match ntn,l with
    (* Special case to avoid writing "- 3" for e.g. (Zopp 3) *)
    | "- _", [CNumeral(_,Bignat.POS p)] ->
        CNotation (loc,ntn,[CNotation(loc,"( _ )",l)])
    | _ -> CNotation (loc,ntn,l)

let make_pat_notation loc ntn l =
  if has_curly_brackets ntn
  then expand_curly_brackets (fun n l -> CPatNotation (loc,n,l)) ntn l
  else match ntn,l with
    (* Special case to avoid writing "- 3" for e.g. (Zopp 3) *)
    | "- _", [CPatNumeral(_,Bignat.POS p)] ->
        CPatNotation (loc,ntn,[CPatNotation(loc,"( _ )",l)])
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
      let l2 =
        match a2 with
	  | ARef (ConstructRef r2) when r1 = r2 -> []
	  | AApp (ARef (ConstructRef r2),l2)  when r1 = r2 -> l2
          | _ -> raise No_match in
      if List.length l2 <> nparams + List.length args1
      then raise No_match
      else
        let (p2,args2) = list_chop nparams l2 in
        (* All parameters must be _ *)
        List.iter (function AHole _ -> () | _ -> raise No_match) p2;
	List.fold_left2 (match_cases_pattern metas) sigma args1 args2
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
    if !Options.raw_print or !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc (make_current_scopes scopes) with
    | None -> raise No_match
    | Some key ->
        let loc = pattern_loc pat in
        insert_pat_delimiters (CPatNumeral (loc,n)) key
  with No_match ->
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
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
  | Some r when not !Options.raw_print & !print_projections ->
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
          !Options.raw_print or
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

let extern_global loc impl f =
  if impl <> [] & List.for_all is_status_implicit impl then
    CAppExpl (loc, (None, f), [])
  else
    CRef f

let extern_app loc inctx impl (cf,f) args =
  if args = [] (* maybe caused by a hidden coercion *) then
    extern_global loc impl f
  else
  if 
    ((!Options.raw_print or
      (!print_implicits & not !print_implicits_explicit_args)) &
     List.exists is_status_implicit impl)
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

let rec remove_coercions inctx = function
  | RApp (loc,RRef (_,r),args) as c
      when
        inctx &
        not (!Options.raw_print or !print_coercions or Options.do_translate ())
      ->
      (try match Classops.hide_coercion r with
	  | Some n when n < List.length args ->
	      (* We skip a coercion *) 
	      let l = list_skipn n args in
              let (a,l) = match l with a::l -> (a,l) | [] -> assert false in
              let (a,l) =
                (* Recursively remove the head coercions *)
                match remove_coercions inctx a with
                  | RApp (_,a,l') -> a,l'@l
                  | a -> a,l in
              if l = [] then a
              else
                (* Recursively remove coercions in arguments *)
                RApp (loc,a,List.map (remove_coercions true) l)
	  | _ -> c
      with Not_found -> c)
  | c -> c

let rec rename_rawconstr_var id0 id1 = function
    RRef(loc,VarRef id) when id=id0 -> RRef(loc,VarRef id1)
  | RVar(loc,id) when id=id0 -> RVar(loc,id1)
  | c -> map_rawconstr (rename_rawconstr_var id0 id1) c

let rec share_fix_binders n rbl ty def =
  match ty,def with
      RProd(_,na0,t0,b), RLambda(_,na1,t1,m) ->
        if not(same_rawconstr t0 t1) then List.rev rbl, ty, def
        else
          let (na,b,m) =
            match na0, na1 with
                Name id0, Name id1 ->
                  if id0=id1 then (na0,b,m)
                  else if not (occur_rawconstr id1 b) then
                    (na1,rename_rawconstr_var id0 id1 b,m)
                  else if not (occur_rawconstr id0 m) then
                    (na1,b,rename_rawconstr_var id1 id0 m)
                  else (* vraiment pas de chance! *)
                    failwith "share_fix_binders: capture"
              | Name id, Anonymous ->
                  if not (occur_rawconstr id m) then (na0,b,m)
                  else
                    failwith "share_fix_binders: capture"
              | Anonymous, Name id -> 
                  if not (occur_rawconstr id b) then (na1,b,m)
                  else
                    failwith "share_fix_binders: capture"
              | _ -> (na1,b,m) in
          share_fix_binders (n-1) ((na,None,t0)::rbl) b m
    | _ -> List.rev rbl, ty, def

(**********************************************************************)
(* mapping rawterms to constr_expr                                    *)

let rec extern inctx scopes vars r =
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    extern_numeral (Rawterm.loc_of_rawconstr r)
      scopes (Symbols.uninterp_numeral r)
  with No_match ->

  let r = remove_coercions inctx r in

  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    extern_symbol scopes vars r (Symbols.uninterp_notations r)
  with No_match -> match r with
  | RRef (loc,ref) ->
      extern_global loc (implicits_of_global_out ref)
        (extern_reference loc vars ref)

  | RVar (loc,id) -> CRef (Ident (loc,v7_to_v8_id id))

  | REvar (loc,n,_) -> (* we drop args *) extern_evar loc n

  | RPatVar (loc,n) -> if !print_meta_as_hole then CHole loc else CPatVar (loc,n)

  | RApp (loc,f,args) ->
      (match f with
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
      let na = name_app translate_ident na in
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
      let vars' = 
	List.fold_right (name_fold Idset.add)
	  (cases_predicate_names tml) vars in
      let rtntypopt' = option_app (extern_type scopes vars') !rtntypopt in
      let tml = List.map (fun (tm,{contents=(na,x)}) ->
        let na' = match na,tm with
            Anonymous, RVar (_,id) when 
              !rtntypopt<>None & occur_rawconstr id (out_some !rtntypopt)
              -> Some Anonymous
          | Anonymous, _ -> None
          | Name id, RVar (_,id') when id=id' -> None
          | Name _, _ -> Some na in
	(sub_extern false scopes vars tm,
	(na',option_app (fun (loc,ind,nal) ->
	  let args = List.map (function
	    | Anonymous -> RHole (dummy_loc,InternalHole) 
	    | Name id -> RVar (dummy_loc,id)) nal in
	  let t = RApp (dummy_loc,RRef (dummy_loc,IndRef ind),args) in
	  (extern_type scopes vars t)) x))) tml in
      let eqns = List.map (extern_eqn (typopt<>None) scopes vars) eqns in 
      CCases (loc,(pred,rtntypopt'),tml,eqns)

  | ROrderedCase (loc,cs,typopt,tm,bv,{contents = Some x}) ->
      extern false scopes vars x

  | ROrderedCase (loc,IfStyle,typopt,tm,bv,_) when Options.do_translate () ->
      let rec strip_branches = function
        | (RLambda (_,_,_,c1), RLambda (_,_,_,c2)) -> strip_branches (c1,c2)
        | x -> x in
      let c1,c2 = strip_branches (bv.(0),bv.(1)) in
      msgerrnl (str "Warning: unable to ensure the correctness of the translation of an if-then-else");
      let bv = Array.map (sub_extern (typopt<>None) scopes vars) [|c1;c2|] in
      COrderedCase
	(loc,IfStyle,option_app (extern_type scopes vars) typopt,
         sub_extern false scopes vars tm,Array.to_list bv)
      (* We failed type-checking If and to translate it to CIf *)
      (* try to remove the dependances in branches anyway *)


  | ROrderedCase (loc,cs,typopt,tm,bv,_) ->
      let bv = Array.map (sub_extern (typopt<>None) scopes vars) bv in
      COrderedCase
	(loc,cs,option_app (extern_type scopes vars) typopt,
         sub_extern false scopes vars tm,Array.to_list bv)

  | RLetTuple (loc,nal,(na,typopt),tm,b) ->
      CLetTuple (loc,nal,
        (option_app (fun _ -> na) typopt,
`        option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern false scopes (List.fold_left add_vname vars nal) b)

  | RIf (loc,c,(na,typopt),b1,b2) ->
      CIf (loc,sub_extern false scopes vars c,
        (option_app (fun _ -> na) typopt,
         option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars b1, sub_extern false scopes vars b2)

  | RRec (loc,fk,idv,blv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
                 let (bl,ty,def) =
                   if Options.do_translate() then
                     let n = List.fold_left
                       (fun n (_,obd,_) -> if obd=None then n-1 else n)
                       nv.(i) blv.(i) in
                     share_fix_binders n (List.rev blv.(i)) tyv.(i) bv.(i)
                   else blv.(i), tyv.(i), bv.(i) in
                 let (ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 (fi,nv.(i), bl, extern_type scopes vars0 ty,
                  extern false scopes vars1 def)) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
                 let (ids,bl) = extern_local_binder scopes vars blv.(i) in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 (fi,bl,extern_type scopes vars0 tyv.(i),
                  sub_extern false scopes vars1 bv.(i))) idv
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
	-> let id = translate_ident id in
           let (nal,c) = factorize_prod scopes (Idset.add id vars) aty c in
           ((loc,Name id)::nal,c)
  | c -> ([],extern_type scopes vars c)

and factorize_lambda inctx scopes vars aty = function
  | RLambda (loc,na,ty,c)
      when same aty (extern_type scopes vars (anonymize_if_reserved na ty))
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let na = name_app translate_ident na in
           let (nal,c) =
	     factorize_lambda inctx scopes (add_vname vars na) aty c in
           ((loc,na)::nal,c)
  | c -> ([],sub_extern inctx scopes vars c)

and extern_local_binder scopes vars = function
    [] -> ([],[])
  | (na,Some bd,ty)::l ->
      let na = name_app translate_ident na in
      let (ids,l) =
        extern_local_binder scopes (name_fold Idset.add na vars) l in
      (na::ids,
       LocalRawDef((dummy_loc,na), extern false scopes vars bd) :: l)
      
  | (na,None,ty)::l ->
      let na = name_app translate_ident na in
      let ty = extern_type scopes vars (anonymize_if_reserved na ty) in
      (match extern_local_binder scopes (name_fold Idset.add na vars) l with
          (ids,LocalRawAssum(nal,ty')::l)
            when same ty ty' &
              match na with Name id -> not (occur_var_constr_expr id ty')
                | _ -> true ->
              (na::ids,
               LocalRawAssum((dummy_loc,na)::nal,ty')::l)
        | (ids,l) ->
            (na::ids,
             LocalRawAssum([(dummy_loc,na)],ty) :: l))

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
  | PEvar (n,l) -> REvar (loc,n,Some (array_map_to_list (raw_of_pat tenv env) l))
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
	(fun _ _ -> false (* lazy: don't try to display pattern with "if" *))
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
