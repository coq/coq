(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Declarations
open Environ
open Evd
open Sign

(** The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

val type_of_inductive    : env -> inductive -> types

(** Return type as quoted by the user *)
val type_of_constructor  : env -> constructor -> types
val type_of_constructors : env -> inductive -> types array

(** Return constructor types in normal form *)
val arities_of_constructors : env -> inductive -> types array

(** An inductive type with its parameters *)
type inductive_family
val make_ind_family : inductive * constr list -> inductive_family
val dest_ind_family : inductive_family -> inductive * constr list
val map_ind_family : (constr -> constr) -> inductive_family -> inductive_family
val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family  : int -> inductive_family -> inductive_family
val substnl_ind_family :
  constr list -> int -> inductive_family -> inductive_family

(** An inductive type with its parameters and real arguments *)
type inductive_type = IndType of inductive_family * constr list
val make_ind_type : inductive_family * constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * constr list
val map_inductive_type : (constr -> constr) -> inductive_type -> inductive_type
val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type  : int -> inductive_type -> inductive_type
val substnl_ind_type : constr list -> int -> inductive_type -> inductive_type

val mkAppliedInd : inductive_type -> constr
val mis_is_recursive_subset : int list -> wf_paths -> bool
val mis_is_recursive :
  inductive * mutual_inductive_body * one_inductive_body -> bool
val mis_nf_constructor_type :
  inductive * mutual_inductive_body * one_inductive_body -> int -> constr

(** Extract information from an inductive name *)

(** Arity of constructors excluding parameters and local defs *)
val mis_constr_nargs : inductive -> int array
val mis_constr_nargs_env : env -> inductive -> int array

val nconstructors : inductive -> int

(** Return the lengths of parameters signature and real arguments signature *)
val inductive_nargs : env -> inductive -> int * int

val mis_constructor_nargs_env : env -> constructor -> int
val constructor_nrealargs : env -> constructor -> int
val constructor_nrealhyps : env -> constructor -> int

val get_full_arity_sign : env -> inductive -> rel_context

val allowed_sorts : env -> inductive -> sorts_family list

(** Extract information from an inductive family *)

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
val get_arity        : env -> inductive_family -> rel_context * sorts_family
val get_constructors : env -> inductive_family -> constructor_summary array
val build_dependent_constructor : constructor_summary -> constr
val build_dependent_inductive   : env -> inductive_family -> constr
val make_arity_signature : env -> bool -> inductive_family -> rel_context
val make_arity : env -> bool -> inductive_family -> sorts -> types
val build_branch_type : env -> bool -> constr -> constructor_summary -> types

(** Raise [Not_found] if not given an valid inductive type *)
val extract_mrectype : constr -> inductive * constr list
val find_mrectype    : env -> evar_map -> constr -> inductive * constr list
val find_rectype     : env -> evar_map -> constr -> inductive_type
val find_inductive   : env -> evar_map -> constr -> inductive * constr list
val find_coinductive : env -> evar_map -> constr -> inductive * constr list

(********************)

(** Builds the case predicate arity (dependent or not) *)
val arity_of_case_predicate :
  env -> inductive_family -> bool -> sorts -> types

val type_case_branches_with_names :
  env -> inductive * constr list -> constr -> constr ->
    types array * types

(** Annotation for cases *)
val make_case_info : env -> inductive -> case_style -> case_info

(*i Compatibility
val make_default_case_info : env -> case_style -> inductive -> case_info
i*)

(********************)

val type_of_inductive_knowing_conclusion :
  env -> one_inductive_body -> types -> types

(********************)
val control_only_guard : env -> types -> unit

val subst_inductive : Mod_subst.substitution -> inductive -> inductive
