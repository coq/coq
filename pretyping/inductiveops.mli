(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Names
open Term
open Declarations
open Environ
open Evd

(* An inductive type with its parameters *)
type inductive_family
val make_ind_family : inductive * constr list -> inductive_family
val dest_ind_family : inductive_family -> inductive * constr list
val map_ind_family : (constr -> constr) -> inductive_family -> inductive_family
val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family  : int -> inductive_family -> inductive_family
val substnl_ind_family :
  constr list -> int -> inductive_family -> inductive_family

(* An inductive type with its parameters and real arguments *)
type inductive_type = IndType of inductive_family * constr list
val make_ind_type : inductive_family * constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * constr list
val map_inductive_type : (constr -> constr) -> inductive_type -> inductive_type
val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type  : int -> inductive_type -> inductive_type
val substnl_ind_type :
  constr list -> int -> inductive_type -> inductive_type

val mkAppliedInd : inductive_type -> constr
val mis_is_recursive_subset : int list -> wf_paths -> bool
val mis_is_recursive :
  inductive * mutual_inductive_body * one_inductive_body -> bool
val mis_nf_constructor_type :
  inductive * mutual_inductive_body * one_inductive_body -> int -> constr
val mis_constr_nargs : inductive -> int array

val mis_constr_nargs_env : env -> inductive -> int array

val mis_constructor_nargs_env : env -> constructor -> int

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : Sign.rel_context;
  cs_concl_realargs : constr array;
} 
val lift_constructor : int -> constructor_summary -> constructor_summary
val get_constructor :
  inductive * mutual_inductive_body * one_inductive_body * constr list ->
  int -> constructor_summary
val get_arity        : env -> inductive_family -> Sign.arity
val get_constructors : env -> inductive_family -> constructor_summary array
val build_dependent_constructor : constructor_summary -> constr
val build_dependent_inductive   : env -> inductive_family -> constr
val make_arity_signature :
  env -> bool -> inductive_family -> Sign.rel_context
val make_arity : env -> bool -> inductive_family -> sorts -> types
val build_branch_type : env -> bool -> constr -> constructor_summary -> types

(* Raise [Not_found] if not given an valid inductive type *)
val extract_mrectype : constr -> inductive * constr list
val find_mrectype    : env -> evar_map -> constr -> inductive * constr list
val find_rectype     : env -> evar_map -> constr -> inductive_type
val find_inductive   : env -> evar_map -> constr -> inductive * constr list
val find_coinductive : env -> evar_map -> constr -> inductive * constr list

(********************)
(* Determines if a case predicate type corresponds to dependent elimination *)
val is_dependent_elimination :
  env -> types -> inductive_family -> bool

(* Builds the case predicate arity (dependent or not) *)
val arity_of_case_predicate :
  env -> inductive_family -> bool -> sorts -> types

val type_case_branches_with_names :
  env -> inductive * constr list -> unsafe_judgment -> constr ->
    types array * types
val make_case_info :
  env -> inductive -> case_style -> pattern_source array -> case_info
val make_default_case_info : env -> case_style -> inductive -> case_info

(********************)
val control_only_guard : env -> types -> unit
