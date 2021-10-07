(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
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

(** An inductive type with its parameters (transparently supports
    reasoning either with only recursively uniform parameters or with all
    parameters including the recursively non-uniform ones *)
type inductive_family
val make_ind_family : inductive Univ.puniverses * constr list -> inductive_family
val dest_ind_family : inductive_family -> inductive Univ.puniverses * constr list
val map_ind_family : (constr -> constr) -> inductive_family -> inductive_family
val liftn_inductive_family : int -> int -> inductive_family -> inductive_family
val lift_inductive_family  : int -> inductive_family -> inductive_family
val substnl_ind_family :
  constr list -> int -> inductive_family -> inductive_family

val relevance_of_inductive_family : env -> inductive_family -> Sorts.relevance

(** An inductive type with its parameters and real arguments *)
type inductive_type = IndType of inductive_family * EConstr.constr list
val make_ind_type : inductive_family * EConstr.constr list -> inductive_type
val dest_ind_type : inductive_type -> inductive_family * EConstr.constr list
val map_inductive_type : (EConstr.constr -> EConstr.constr) -> inductive_type -> inductive_type
val liftn_inductive_type : int -> int -> inductive_type -> inductive_type
val lift_inductive_type  : int -> inductive_type -> inductive_type
val substnl_ind_type : EConstr.constr list -> int -> inductive_type -> inductive_type
val ind_of_ind_type : inductive_type -> inductive

val relevance_of_inductive_type : env -> inductive_type -> Sorts.relevance

val mkAppliedInd : inductive_type -> EConstr.constr
val mis_is_recursive_subset : int list -> wf_paths -> bool
val mis_is_recursive :
  inductive * mutual_inductive_body * one_inductive_body -> bool
val mis_nf_constructor_type :
  pinductive * mutual_inductive_body * one_inductive_body -> int -> constr

(** {6 Extract information from an inductive name} *)

(** @return number of constructors *)
val nconstructors : env -> inductive -> int
val nconstructors_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.nconstructors"]

(** @return arity of constructors excluding parameters, excluding local defs *)
val constructors_nrealargs : env -> inductive -> int array
val constructors_nrealargs_env : env -> inductive -> int array
[@@ocaml.deprecated "Alias for Inductiveops.constructors_nrealargs"]

(** @return arity of constructors excluding parameters, including local defs *)
val constructors_nrealdecls : env -> inductive -> int array
val constructors_nrealdecls_env : env -> inductive -> int array
[@@ocaml.deprecated "Alias for Inductiveops.constructors_nrealdecls"]

(** @return the arity, excluding params, excluding local defs *)
val inductive_nrealargs : env -> inductive -> int
val inductive_nrealargs_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nrealargs"]

(** @return the arity, excluding params, including local defs *)
val inductive_nrealdecls : env -> inductive -> int
val inductive_nrealdecls_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nrealdecls"]

(** @return the arity, including params, excluding local defs *)
val inductive_nallargs : env -> inductive -> int
val inductive_nallargs_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nallargs"]

(** @return the arity, including params, including local defs *)
val inductive_nalldecls : env -> inductive -> int
val inductive_nalldecls_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nalldecls"]

(** @return nb of params without local defs *)
val inductive_nparams : env -> inductive -> int
val inductive_nparams_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nparams"]

(** @return nb of params with local defs *)
val inductive_nparamdecls : env -> inductive -> int
val inductive_nparamdecls_env : env -> inductive -> int
[@@ocaml.deprecated "Alias for Inductiveops.inductive_nparamsdecls"]

(** @return params context *)
val inductive_paramdecls : env -> pinductive -> Constr.rel_context
val inductive_paramdecls_env : env -> pinductive -> Constr.rel_context
[@@ocaml.deprecated "Alias for Inductiveops.inductive_paramsdecl"]

(** @return full arity context, hence with letin *)
val inductive_alldecls : env -> pinductive -> Constr.rel_context
val inductive_alldecls_env : env -> pinductive -> Constr.rel_context
[@@ocaml.deprecated "Alias for Inductiveops.inductive_alldecls"]

(** {7 Extract information from a constructor name} *)

(** @return param + args without letin *)
val constructor_nallargs : env -> constructor -> int
val constructor_nallargs_env : env -> constructor -> int
[@@ocaml.deprecated "Alias for Inductiveops.constructor_nallargs"]

(** @return param + args with letin *)
val constructor_nalldecls : env -> constructor -> int
val constructor_nalldecls_env : env -> constructor -> int
[@@ocaml.deprecated "Alias for Inductiveops.constructor_nalldecls"]

(** @return args without letin *)
val constructor_nrealargs : env -> constructor -> int
val constructor_nrealargs_env : env -> constructor -> int
[@@ocaml.deprecated "Alias for Inductiveops.constructor_nrealargs"]

(** @return args with letin *)
val constructor_nrealdecls : env -> constructor -> int
val constructor_nrealdecls_env : env -> constructor -> int
[@@ocaml.deprecated "Alias for Inductiveops.constructor_nrealdecls"]

(** @return tags of all decls: true = assumption, false = letin *)
val inductive_alltags : env -> inductive -> bool list
val constructor_alltags : env -> constructor -> bool list

(** Is there local defs in params or args ? *)
val constructor_has_local_defs : env -> constructor -> bool
val inductive_has_local_defs : env -> inductive -> bool

val sorts_below : Sorts.family -> Sorts.family list

val top_allowed_sort : env -> inductive -> Sorts.family

(** (Co)Inductive records with primitive projections do not have eta-conversion,
    hence no dependent elimination. *)
val has_dependent_elim : mutual_inductive_body -> bool

(** Primitive projections *)
val type_of_projection_knowing_arg : env -> evar_map -> Projection.t ->
                                     EConstr.t -> EConstr.types -> types

(** Extract information from an inductive family *)

type constructor_summary = {
  cs_cstr : pconstructor;    (* internal name of the constructor plus universes *)
  cs_params : constr list;   (* parameters of the constructor in current ctx *)
  cs_nargs : int;            (* length of arguments signature (letin included) *)
  cs_args : Constr.rel_context;   (* signature of the arguments (letin included) *)
  cs_concl_realargs : constr array; (* actual realargs in the concl of cstr *)
}
val lift_constructor : int -> constructor_summary -> constructor_summary
val get_constructor :
  pinductive * mutual_inductive_body * one_inductive_body * constr list ->
  int -> constructor_summary
val get_constructors : env -> inductive_family -> constructor_summary array

(** [get_arity] returns the arity of the inductive family instantiated
    with the parameters; if recursively non-uniform parameters are not
    part of the inductive family, they appears in the arity *)
val get_arity        : env -> inductive_family -> Constr.rel_context * Sorts.family

val build_dependent_constructor : constructor_summary -> constr
val build_dependent_inductive   : env -> inductive_family -> constr
val make_arity_signature : env -> evar_map -> bool -> inductive_family -> EConstr.rel_context
val make_arity : env -> evar_map -> bool -> inductive_family -> Sorts.t -> EConstr.types
val build_branch_type : env -> evar_map -> bool -> constr -> constructor_summary -> types

(** Raise [Not_found] if not given a valid inductive type *)
val extract_mrectype : evar_map -> EConstr.t -> (inductive * EConstr.EInstance.t) * EConstr.constr list
val find_mrectype    : env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * EConstr.constr list
val find_mrectype_vect : env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * EConstr.constr array
val find_rectype     : env -> evar_map -> EConstr.types -> inductive_type
val find_inductive   : env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * constr list
val find_coinductive : env -> evar_map -> EConstr.types -> (inductive * EConstr.EInstance.t) * constr list

(********************)

(** Builds the case predicate arity (dependent or not) *)
val arity_of_case_predicate :
  env -> inductive_family -> bool -> Sorts.t -> types

val type_case_branches_with_names :
  env -> evar_map -> pinductive * EConstr.constr list -> constr -> constr -> EConstr.types array * types

(** Annotation for cases *)
val make_case_info : env -> inductive -> Sorts.relevance -> case_style -> case_info

(** Make a case or substitute projections if the inductive type is a record
    with primitive projections.
    Fail with an error if the elimination is dependent while the
    inductive type does not allow dependent elimination. *)
val make_case_or_project :
  env -> evar_map -> inductive_type -> case_info ->
  (* pred *) EConstr.constr -> (* term *) EConstr.constr -> (* branches *) EConstr.constr array -> EConstr.constr

(** Sometimes [make_case_or_project] is nicer to call with a pre-built
   [case_invert] than [inductive_type]. *)
val simple_make_case_or_project :
  env -> evar_map -> case_info ->
  (* pred *) EConstr.constr -> EConstr.case_invert -> (* term *) EConstr.constr -> (* branches *) EConstr.constr array -> EConstr.constr

val make_case_invert : env -> inductive_type -> case_info
  -> EConstr.case_invert

(*i Compatibility
val make_default_case_info : env -> case_style -> inductive -> case_info
i*)

val compute_projections : Environ.env -> inductive -> (constr * types) array
(** Given a primitive record type, for every field computes the eta-expanded
    projection and its type. *)

(********************)

val type_of_inductive_knowing_conclusion :
  env -> evar_map -> Inductive.mind_specif Univ.puniverses -> EConstr.types -> evar_map * EConstr.types

(********************)
val control_only_guard : env -> Evd.evar_map -> EConstr.types -> unit
