(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Declarations
open Sign
open Environ
open Evd

val mis_nf_constructor_type :
  (section_path * 'a) * mutual_inductive_body *
  one_inductive_body -> int -> constr

type inductive_family = inductive * constr list
and inductive_type = IndType of inductive_family * constr list
val liftn_inductive_family :
  int -> int -> 'a * constr list -> 'a * constr list
val lift_inductive_family :
  int -> 'a * constr list -> 'a * constr list
val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type : int -> inductive_type -> inductive_type
val substnl_ind_family :
  constr list -> int -> 'a * constr list -> 'a * constr list
val substnl_ind_type :
  constr list -> int -> inductive_type -> inductive_type
val make_ind_family : 'a * 'b -> 'a * 'b
val dest_ind_family : 'a * 'b -> 'a * 'b
val make_ind_type : inductive_family * constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * constr list
val mkAppliedInd : inductive_type -> constr
val mis_is_recursive_subset :
  int list -> one_inductive_body -> bool
val mis_is_recursive :
  mutual_inductive_body * one_inductive_body ->
  bool
val make_case_info :
  env -> inductive ->
  case_style option -> pattern_source array -> case_info
val make_default_case_info : env -> inductive -> case_info

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : rel_context;
  cs_concl_realargs : constr array;
} 
val lift_constructor : int -> constructor_summary -> constructor_summary
val get_constructor :
  inductive * mutual_inductive_body * one_inductive_body * constr list ->
  int -> constructor_summary
val get_constructors :
  env -> inductive * constr list -> constructor_summary array
val get_arity :
  env -> inductive * constr list -> arity
val local_rels : rel_context -> constr list
val build_dependent_constructor : constructor_summary -> constr
val build_dependent_inductive   : env -> inductive * constr list -> constr
val make_arity :
  env -> bool -> inductive * constr list -> sorts -> types
val build_branch_type :
  env -> bool -> constr -> constructor_summary -> types

exception Induc
val extract_mrectype : constr -> inductive * constr list
val find_mrectype :
  env -> 'a evar_map -> constr -> inductive * constr list
val find_rectype :
  env -> 'a evar_map -> constr -> inductive_type
val find_inductive :
  env -> 'a evar_map -> constr -> inductive * constr list
val find_coinductive :
  env ->
  'a evar_map -> constr -> inductive * constr list
val type_case_branches_with_names :
  env -> inductive * constr list -> unsafe_judgment -> constr ->
    types array * types
val control_only_guard : env -> types -> unit
