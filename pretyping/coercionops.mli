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

(** This is the type of infos for declared classes *)
type cl_info_typ = {
  cl_param : int }

(** This is the type of coercion kinds *)
type coe_typ = GlobRef.t

(** This is the type of infos for declared coercions *)
type coe_info_typ = {
  coe_value : GlobRef.t;
  coe_local : bool;
  coe_is_identity : bool;
  coe_is_projection : Projection.Repr.t option;
  coe_param : int;
}

(** [cl_index] is the type of class keys *)
type cl_index

(** This is the type of paths from a class to another *)
type inheritance_path = coe_info_typ list

(** {6 Access to classes infos } *)

val class_exists : cl_typ -> bool

val class_info : cl_typ -> (cl_index * cl_info_typ)
(** @raise Not_found if this type is not a class *)

val class_info_from_index : cl_index -> cl_typ * cl_info_typ

(** [find_class_type env sigma c] returns the head reference of [c],
    its universe instance and its arguments *)
val find_class_type : env -> evar_map -> types -> cl_typ * EInstance.t * constr list

(** raises [Not_found] if not convertible to a class *)
val class_of : env -> evar_map -> types -> types * cl_index

(** raises [Not_found] if not mapped to a class *)
val inductive_class_of : inductive -> cl_index

val class_args_of : env -> evar_map -> types -> constr list

(** {6 [declare_coercion] adds a coercion in the graph of coercion paths } *)
type coercion = {
  coercion_type   : coe_typ;
  coercion_local  : bool;
  coercion_is_id  : bool;
  coercion_is_proj  : Projection.Repr.t option;
  coercion_source : cl_typ;
  coercion_target : cl_typ;
  coercion_params : int;
}

val subst_coercion : substitution -> coercion -> coercion

val declare_coercion : env -> evar_map -> coercion -> unit

(** {6 Access to coercions infos } *)
val coercion_exists : coe_typ -> bool

(** {6 Lookup functions for coercion paths } *)

(** @raise Not_found in the following functions when no path exists *)

val lookup_path_between_class : cl_index * cl_index -> inheritance_path
val lookup_path_between : env -> evar_map -> types * types ->
      types * types * inheritance_path
val lookup_path_to_fun_from : env -> evar_map -> types ->
      types * inheritance_path
val lookup_path_to_sort_from : env -> evar_map -> types ->
      types * inheritance_path
val lookup_pattern_path_between :
  env -> inductive * inductive -> (constructor * int) list

(**/**)
(* Crade *)
val install_path_printer :
  ((cl_index * cl_index) * inheritance_path -> Pp.t) -> unit
val install_path_comparator :
  (env -> evar_map -> cl_index -> inheritance_path -> inheritance_path -> bool) -> unit
(**/**)

(** {6 This is for printing purpose } *)
val string_of_class : cl_typ -> string
val pr_class : cl_typ -> Pp.t
val pr_cl_index : cl_index -> Pp.t
val inheritance_graph : unit -> ((cl_index * cl_index) * inheritance_path) list
val classes : unit -> cl_typ list
val coercions : unit -> coe_info_typ list

(** [hide_coercion] returns the number of params to skip if the coercion must
   be hidden, [None] otherwise; it raises [Not_found] if not a coercion *)
val hide_coercion : coe_typ -> int option
