(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open EConstr
open Evd
open Mod_subst

(** {6 This is the type of class kinds } *)
type cl_typ =
  | CL_SORT
  | CL_FUN
  | CL_SECVAR of variable
  | CL_CONST of Constant.t
  | CL_IND of inductive
  | CL_PROJ of Projection.Repr.t

(** Equality over [cl_typ] *)
val cl_typ_eq : cl_typ -> cl_typ -> bool

val subst_cl_typ : env -> substitution -> cl_typ -> cl_typ

(** Comparison of [cl_typ] *)
val cl_typ_ord : cl_typ -> cl_typ -> int

(** This is the type of coercion kinds *)
type coe_typ = GlobRef.t

(** This is the type of infos for declared coercions *)
type coe_info_typ = {
  coe_value : GlobRef.t;
  coe_local : bool;
  coe_reversible : bool;
  coe_is_identity : bool;
  coe_is_projection : Projection.Repr.t option;
  coe_source : cl_typ;
  coe_target : cl_typ;
  coe_param : int;
}

(** This is the type of paths from a class to another *)
type inheritance_path = coe_info_typ list

(** {6 Access to classes infos } *)

val class_exists : cl_typ -> bool

(** @raise Not_found if this type is not a class *)
val class_nparams : cl_typ -> int

(** [find_class_type env sigma c] returns the head reference of [c],
    its universe instance and its arguments *)
val find_class_type : env -> evar_map -> types -> cl_typ * EInstance.t * constr list

val find_class_glob_type : 'a Glob_term.glob_constr_g -> cl_typ

(** raises [Not_found] if not convertible to a class *)
val class_of : env -> evar_map -> types -> types * cl_typ

val class_args_of : env -> evar_map -> types -> constr list

val subst_coercion : substitution -> coe_info_typ -> coe_info_typ

(** Set [update] to update an already declared coercion (default [false]). *)
val declare_coercion : env -> evar_map -> ?update:bool -> coe_info_typ -> unit

(** {6 Access to coercions infos } *)
val coercion_exists : coe_typ -> bool

val coercion_info : coe_typ -> coe_info_typ

val coercion_type : Environ.env -> Evd.evar_map -> coe_info_typ EConstr.puniverses -> EConstr.t

(** {6 Lookup functions for coercion paths } *)

(** @raise Not_found in the following functions when no path exists *)

(** given one (or two) types these function also return the class (classes)
    of the type and its class_args_of *)

val lookup_path_between_class : cl_typ * cl_typ -> inheritance_path
val lookup_path_between : env -> evar_map -> src:types -> tgt:types ->
  inheritance_path
val lookup_path_to_fun_from : env -> evar_map -> types -> inheritance_path
val lookup_path_to_sort_from : env -> evar_map -> types -> inheritance_path
val lookup_pattern_path_between :
  env -> inductive * inductive -> (constructor * int) list

val path_is_reversible : inheritance_path -> bool

(**/**)
(* Crade *)
val install_path_printer :
  ((cl_typ * cl_typ) * inheritance_path -> Pp.t) -> unit
val install_path_comparator :
  (env -> evar_map -> cl_typ -> inheritance_path -> inheritance_path -> bool) -> unit
(**/**)

(** {6 This is for printing purpose } *)
val string_of_class : cl_typ -> string
val pr_class : cl_typ -> Pp.t
val inheritance_graph : unit -> ((cl_typ * cl_typ) * inheritance_path) list
val classes : unit -> cl_typ list
val coercions : unit -> coe_info_typ list

(** [hide_coercion] returns the number of params to skip if the coercion must
   be hidden, [None] otherwise; it raises [Not_found] if not a coercion *)
val hide_coercion : coe_typ -> int option

module ClTypSet : CSet.ExtS with type elt = cl_typ

val reachable_from : cl_typ -> ClTypSet.t
