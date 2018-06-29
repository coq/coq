(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open Reductionops
open Libnames
open Evd

(** A Pretty-Printer for the Calculus of Inductive Constructions. *)

val assumptions_for_print : Name.t list -> Termops.names_context

val print_closed_sections : bool ref
val print_context : env -> Evd.evar_map -> bool -> int option -> Lib.library_segment -> Pp.t
val print_library_entry : env -> Evd.evar_map -> bool -> (object_name * Lib.node) -> Pp.t option
val print_full_context : env -> Evd.evar_map -> Pp.t
val print_full_context_typ : env -> Evd.evar_map -> Pp.t
val print_full_pure_context : env -> Evd.evar_map -> Pp.t
val print_sec_context : env -> Evd.evar_map -> qualid -> Pp.t
val print_sec_context_typ : env -> Evd.evar_map -> qualid -> Pp.t
val print_judgment : env -> Evd.evar_map -> EConstr.unsafe_judgment -> Pp.t
val print_safe_judgment : env -> Evd.evar_map -> Safe_typing.judgment -> Pp.t
val print_eval :
  reduction_function -> env -> Evd.evar_map ->
    Constrexpr.constr_expr -> EConstr.unsafe_judgment -> Pp.t

val print_name : env -> Evd.evar_map -> qualid Constrexpr.or_by_notation ->
  UnivNames.univ_name_list option -> Pp.t
val print_opaque_name : env -> Evd.evar_map -> qualid -> Pp.t
val print_about : env -> Evd.evar_map -> qualid Constrexpr.or_by_notation ->
  UnivNames.univ_name_list option -> Pp.t
val print_impargs : qualid Constrexpr.or_by_notation -> Pp.t

(** Pretty-printing functions for classes and coercions *)
val print_graph : env -> evar_map -> Pp.t
val print_classes : unit -> Pp.t
val print_coercions : env -> Evd.evar_map -> Pp.t
val print_path_between : env -> evar_map -> Classops.cl_typ -> Classops.cl_typ -> Pp.t
val print_canonical_projections : env -> Evd.evar_map -> Pp.t

(** Pretty-printing functions for type classes and instances *)
val print_typeclasses : unit -> Pp.t
val print_instances : GlobRef.t -> Pp.t
val print_all_instances : unit -> Pp.t

val inspect : env -> Evd.evar_map -> int -> Pp.t

(** {5 Locate} *)

type 'a locatable_info = {
  locate : qualid -> 'a option;
  (** Locate the most precise object with the provided name if any. *)
  locate_all : qualid -> 'a list;
  (** Locate all objects whose name is a suffix of the provided name *)
  shortest_qualid : 'a -> qualid;
  (** Return the shortest name in the current context *)
  name : 'a -> Pp.t;
  (** Data as printed by the Locate command *)
  print : 'a -> Pp.t;
  (** Data as printed by the Print command *)
  about : 'a -> Pp.t;
  (** Data as printed by the About command *)
}
(** Generic data structure representing locatable objects. *)

val register_locatable : string -> 'a locatable_info -> unit
(** Define a new type of locatable objects that can be reached via the
    corresponding generic vernacular commands. The string should be a unique
    name describing the kind of objects considered and that is added as a
    grammar command prefix for vernacular commands Locate. *)

val print_located_qualid : qualid -> Pp.t
val print_located_term : qualid -> Pp.t
val print_located_module : qualid -> Pp.t
val print_located_other : string -> qualid -> Pp.t

type object_pr = {
  print_inductive           : MutInd.t -> UnivNames.univ_name_list option -> Pp.t;
  print_constant_with_infos : Constant.t -> UnivNames.univ_name_list option -> Pp.t;
  print_section_variable    : env -> Evd.evar_map -> variable -> Pp.t;
  print_syntactic_def       : env -> KerName.t -> Pp.t;
  print_module              : bool -> ModPath.t -> Pp.t;
  print_modtype             : ModPath.t -> Pp.t;
  print_named_decl          : env -> Evd.evar_map -> Constr.named_declaration -> Pp.t;
  print_library_entry       : env -> Evd.evar_map -> bool -> (object_name * Lib.node) -> Pp.t option;
  print_context             : env -> Evd.evar_map -> bool -> int option -> Lib.library_segment -> Pp.t;
  print_typed_value_in_env  : Environ.env -> Evd.evar_map -> EConstr.constr * EConstr.types -> Pp.t;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Constrexpr.constr_expr -> EConstr.unsafe_judgment -> Pp.t;
}

val set_object_pr : object_pr -> unit
val default_object_pr : object_pr
