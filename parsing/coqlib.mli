(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Names
open Term
open Pattern
(*i*)

(*s This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(*s Global references *)

(* Modules *)
val logic_module : dir_path
val logic_type_module : dir_path

(* Natural numbers *)
val glob_nat : global_reference
val glob_O : global_reference
val glob_S : global_reference

(* Special variable for pretty-printing of constant naturals *)
val glob_My_special_variable_nat : global_reference

(* Equality *)
val glob_eq : global_reference
val glob_eqT : global_reference

(*s Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   applied to [()] to get the actual constr or pattern at runtime *)

type 'a delayed = unit -> 'a

(*s For Equality tactics *)
type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

val build_sigma_set : unit -> coq_sigma_data
val build_sigma_type : unit -> coq_sigma_data

type coq_leibniz_eq_data = {
  eq   : constr delayed;
  ind  : constr delayed;
  rrec : constr delayed option;
  rect : constr delayed option;
  congr: constr delayed;
  sym  : constr delayed }

val build_coq_eq_data : coq_leibniz_eq_data
val build_coq_eqT_data : coq_leibniz_eq_data
val build_coq_idT_data : coq_leibniz_eq_data

val build_coq_f_equal2 : constr delayed
val build_coq_eqT : constr delayed
val build_coq_sym_eqT : constr delayed

(* Empty Type *)
val build_coq_EmptyT : constr delayed

(* Unit Type and its unique inhabitant *)
val build_coq_UnitT : constr delayed
val build_coq_IT : constr delayed

(* Specif *)
val build_coq_sumbool : constr delayed

(*s Connectives *)
(* The False proposition *)
val build_coq_False : constr delayed

(* The True proposition and its unique proof *)
val build_coq_True : constr delayed
val build_coq_I : constr delayed

(* Negation *)
val build_coq_not : constr delayed

(* Conjunction *)
val build_coq_and : constr delayed

(* Disjunction *)
val build_coq_or : constr delayed

(* Existential quantifier *)
val build_coq_ex : constr delayed

(**************************** Patterns ************************************)
(* ["(eq ?1 ?2 ?3)"] *)
val build_coq_eq_pattern : constr_pattern delayed

(* ["(eqT ?1 ?2 ?3)"] *)
val build_coq_eqT_pattern : constr_pattern delayed

(* ["(identityT ?1 ?2 ?3)"] *)
val build_coq_idT_pattern : constr_pattern delayed

(* ["(existS ?1 ?2 ?3 ?4)"] *)
val build_coq_existS_pattern : constr_pattern delayed

(* ["(existT ?1 ?2 ?3 ?4)"] *)
val build_coq_existT_pattern : constr_pattern delayed

(* ["(not ?)"] *)
val build_coq_not_pattern : constr_pattern delayed

(* ["? -> False"] *)
val build_coq_imp_False_pattern : constr_pattern delayed

(* ["(sumbool (eq ?1 ?2 ?3) ?4)"] *)
val build_coq_eqdec_partial_pattern : constr_pattern delayed

(* ["! (x,y:?1). (sumbool (eq ?1 x y) ~(eq ?1 x y))"] *)
val build_coq_eqdec_pattern : constr_pattern delayed

(* ["(A : ?)(x:A)(? A x x)"] and ["(x : ?)(? x x)"] *)
val build_coq_refl_rel1_pattern : constr_pattern delayed
val build_coq_refl_rel2_pattern : constr_pattern delayed

(* ["(?1 -> ?2)"] *)
val build_coq_arrow_pattern : constr_pattern delayed

(* ["(sig ?1 ?2)"] *)
val build_coq_sig_pattern : constr_pattern delayed
