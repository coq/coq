(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Declarations
open Environ
open Evd

(** The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

val type_of_inductive    : env -> pinductive -> types

(** Return type as quoted by the user *)
val type_of_constructor  : env -> pconstructor -> types
val type_of_constructors : env -> pinductive -> types array

(** Return constructor types in normal form *)
val arities_of_constructors : env -> pinductive -> types array

(** An inductive type with its parameters *)
type inductive_family
val make_ind_family : inductive puniverses * constr list -> inductive_family
val dest_ind_family : inductive_family -> inductive puniverses * constr list
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
  pinductive * mutual_inductive_body * one_inductive_body -> int -> constr

(** {6 Extract information from an inductive name} *)

(** @return number of constructors *)
val nconstructors : inductive -> int
val nconstructors_env : env -> inductive -> int

(** @return arity of constructors excluding parameters, excluding local defs *)
val constructors_nrealargs : inductive -> int array
val constructors_nrealargs_env : env -> inductive -> int array

(** @return arity of constructors excluding parameters, including local defs *)
val constructors_nrealdecls : inductive -> int array
val constructors_nrealdecls_env : env -> inductive -> int array

(** @return the arity, excluding params, excluding local defs *)
val inductive_nrealargs : inductive -> int
val inductive_nrealargs_env : env -> inductive -> int

(** @return the arity, excluding params, including local defs *)
val inductive_nrealdecls : inductive -> int
val inductive_nrealdecls_env : env -> inductive -> int

(** @return the arity, including params, excluding local defs *)
val inductive_nallargs : inductive -> int
val inductive_nallargs_env : env -> inductive -> int

(** @return the arity, including params, including local defs *)
val inductive_nalldecls : inductive -> int
val inductive_nalldecls_env : env -> inductive -> int

(** @return nb of params without local defs *)
val inductive_nparams : inductive -> int
val inductive_nparams_env : env -> inductive -> int

(** @return nb of params with local defs *)
val inductive_nparamdecls : inductive -> int
val inductive_nparamdecls_env : env -> inductive -> int

(** @return params context *)
val inductive_paramdecls : pinductive -> rel_context
val inductive_paramdecls_env : env -> pinductive -> rel_context

(** @return full arity context, hence with letin *)
val inductive_alldecls : pinductive -> rel_context
val inductive_alldecls_env : env -> pinductive -> rel_context

(** {7 Extract information from a constructor name} *)

(** @return param + args without letin *)
val constructor_nallargs : constructor -> int
val constructor_nallargs_env : env -> constructor -> int

(** @return param + args with letin *)
val constructor_nalldecls : constructor -> int
val constructor_nalldecls_env : env -> constructor -> int

(** @return args without letin *)
val constructor_nrealargs : constructor -> int
val constructor_nrealargs_env : env -> constructor -> int

(** @return args with letin *)
val constructor_nrealdecls : constructor -> int
val constructor_nrealdecls_env : env -> constructor -> int

(** Is there local defs in params or args ? *)
val constructor_has_local_defs : constructor -> bool
val inductive_has_local_defs : inductive -> bool

val allowed_sorts : env -> inductive -> sorts_family list

(** Primitive projections *)
val projection_nparams : projection -> int
val projection_nparams_env : env -> projection -> int

(** Extract information from an inductive family *)

type constructor_summary = {
  cs_cstr : pconstructor;    (* internal name of the constructor plus universes *)
  cs_params : constr list;  (* parameters of the constructor in current ctx *)
  cs_nargs : int;           (* length of arguments signature (letin included) *)
  cs_args : rel_context;    (* signature of the arguments (letin included) *)
  cs_concl_realargs : constr array; (* actual realargs in the concl of cstr *)
}
val lift_constructor : int -> constructor_summary -> constructor_summary
val get_constructor :
  pinductive * mutual_inductive_body * one_inductive_body * constr list ->
  int -> constructor_summary
val get_arity        : env -> inductive_family -> rel_context * sorts_family
val get_constructors : env -> inductive_family -> constructor_summary array
val get_projections  : env -> inductive_family -> constant array option

val build_dependent_constructor : constructor_summary -> constr
val build_dependent_inductive   : env -> inductive_family -> constr
val make_arity_signature : env -> bool -> inductive_family -> rel_context
val make_arity : env -> bool -> inductive_family -> sorts -> types
val build_branch_type : env -> bool -> constr -> constructor_summary -> types

(** Raise [Not_found] if not given a valid inductive type *)
val extract_mrectype : constr -> pinductive * constr list
val find_mrectype    : env -> evar_map -> types -> pinductive * constr list
val find_rectype     : env -> evar_map -> types -> inductive_type
val find_inductive   : env -> evar_map -> types -> pinductive * constr list
val find_coinductive : env -> evar_map -> types -> pinductive * constr list

(********************)

(** Builds the case predicate arity (dependent or not) *)
val arity_of_case_predicate :
  env -> inductive_family -> bool -> sorts -> types

val type_case_branches_with_names :
  env -> pinductive * constr list -> constr -> constr -> types array * types

(** Annotation for cases *)
val make_case_info : env -> inductive -> case_style -> case_info

(*i Compatibility
val make_default_case_info : env -> case_style -> inductive -> case_info
i*)

(********************)

val type_of_inductive_knowing_conclusion :
  env -> evar_map -> Inductive.mind_specif puniverses -> types -> evar_map * types

(********************)
val control_only_guard : env -> types -> unit
