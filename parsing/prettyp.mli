(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Sign
open Term
open Environ
open Reductionops
open Libnames
open Nametab
open Genarg

(** A Pretty-Printer for the Calculus of Inductive Constructions. *)

val assumptions_for_print : name list -> Termops.names_context

val print_closed_sections : bool ref
val print_impl_args : Impargs.implicits_list -> std_ppcmds
val print_context : bool -> int option -> Lib.library_segment -> std_ppcmds
val print_library_entry : bool -> (object_name * Lib.node) -> std_ppcmds option
val print_full_context : unit -> std_ppcmds
val print_full_context_typ : unit -> std_ppcmds
val print_full_pure_context : unit -> std_ppcmds
val print_sec_context : reference -> std_ppcmds
val print_sec_context_typ : reference -> std_ppcmds
val print_judgment : env -> unsafe_judgment -> std_ppcmds
val print_safe_judgment : env -> Safe_typing.judgment -> std_ppcmds
val print_eval :
  reduction_function -> env -> Evd.evar_map -> Topconstr.constr_expr -> unsafe_judgment -> std_ppcmds

(** This function is exported for the graphical user-interface pcoq *)
val build_inductive : mutual_inductive -> int ->
  global_reference * rel_context * types * identifier array * types array
val print_name : reference or_by_notation -> std_ppcmds
val print_opaque_name : reference -> std_ppcmds
val print_about : reference or_by_notation -> std_ppcmds
val print_impargs : reference or_by_notation -> std_ppcmds

(*i
val print_extracted_name : identifier -> std_ppcmds
val print_extraction : unit -> std_ppcmds
val print_extracted_vars : unit -> std_ppcmds
i*)

(** Pretty-printing functions for classes and coercions *)
val print_graph : unit -> std_ppcmds
val print_classes : unit -> std_ppcmds
val print_coercions : unit -> std_ppcmds
val print_path_between : Classops.cl_typ -> Classops.cl_typ -> std_ppcmds
val print_canonical_projections : unit -> std_ppcmds

(** Pretty-printing functions for type classes and instances *)
val print_typeclasses : unit -> std_ppcmds
val print_instances : global_reference -> std_ppcmds
val print_all_instances : unit -> std_ppcmds

val inspect : int -> std_ppcmds

(** Locate *)
val print_located_qualid : reference -> std_ppcmds

type object_pr = {
  print_inductive           : mutual_inductive -> std_ppcmds;
  print_constant_with_infos : constant -> std_ppcmds;
  print_section_variable    : variable -> std_ppcmds;
  print_syntactic_def       : kernel_name -> std_ppcmds;
  print_module              : bool -> Names.module_path -> std_ppcmds;
  print_modtype             : module_path -> std_ppcmds;
  print_named_decl          : identifier * constr option * types -> std_ppcmds;
  print_library_entry       : bool -> (object_name * Lib.node) -> std_ppcmds option;
  print_context             : bool -> int option -> Lib.library_segment -> std_ppcmds;
  print_typed_value_in_env  : Environ.env -> Term.constr * Term.types -> Pp.std_ppcmds;
  print_eval                : reduction_function -> env -> Evd.evar_map -> Topconstr.constr_expr -> unsafe_judgment -> std_ppcmds
}

val set_object_pr : object_pr -> unit
val default_object_pr : object_pr
