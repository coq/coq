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
open Libnames

(** This module implements Print/About/Locate commands *)

val assumptions_for_print : Name.t list -> Termops.names_context (* unused? *)

val print_closed_sections : bool ref
val print_context (* unused? *)
  : env
  -> Evd.evar_map
  -> with_values:Global.indirect_accessor option -> int option -> 'a Lib.library_segment -> Pp.t
val print_library_leaf
  : env
  -> Evd.evar_map
  -> with_values:Global.indirect_accessor option
  -> ModPath.t
  -> Libobject.t
  -> Pp.t option
val print_library_node : Summary.Interp.frozen Lib.node -> Pp.t (* unused? *)
val print_full_context : Global.indirect_accessor -> env -> Evd.evar_map -> Pp.t
val print_full_context_typ : env -> Evd.evar_map -> Pp.t

val print_full_pure_context : Global.indirect_accessor -> env -> Evd.evar_map -> Pp.t

val print_sec_context : Global.indirect_accessor -> env -> Evd.evar_map -> qualid -> Pp.t
val print_sec_context_typ : env -> Evd.evar_map -> qualid -> Pp.t
val print_judgment : env -> Evd.evar_map -> EConstr.unsafe_judgment -> Pp.t
val print_safe_judgment : Safe_typing.judgment -> Pp.t

val print_name : Global.indirect_accessor -> env -> Evd.evar_map
  -> qualid Constrexpr.or_by_notation
  -> UnivNames.full_name_list option
  -> Pp.t
val print_notation : env -> Evd.evar_map
  -> Constrexpr.notation_entry
  -> string
  -> Pp.t

val print_abbreviation : Global.indirect_accessor -> env -> Evd.evar_map -> KerName.t -> Pp.t

val print_about : env -> Evd.evar_map -> qualid Constrexpr.or_by_notation ->
  UnivNames.full_name_list option -> Pp.t
val print_impargs : env -> GlobRef.t -> Pp.t

(** Pretty-printing functions for classes and coercions *)
val print_graph : unit -> Pp.t
val print_classes : unit -> Pp.t
val print_coercions : unit -> Pp.t
val print_coercion_paths : Coercionops.cl_typ -> Coercionops.cl_typ -> Pp.t
val print_canonical_projections : env -> Evd.evar_map -> GlobRef.t list -> Pp.t

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

val print_located_qualid : env -> qualid -> Pp.t
val print_located_term : env -> qualid -> Pp.t
val print_located_module : env -> qualid -> Pp.t
val print_located_other : env -> string -> qualid -> Pp.t
