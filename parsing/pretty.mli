
(* $Id$ *)

(*i*)
open Pp
open Names
open Sign
open Term
open Inductive
open Reduction
open Environ
(*i*)

(* A Pretty-Printer for the Calculus of Inductive Constructions. *)

val assumptions_for_print : name list -> names_context

val print_basename : section_path -> string
val print_basename_mind : section_path -> identifier -> string
val print_closed_sections : bool ref
val print_impl_args : int list -> std_ppcmds
val print_context : bool -> Lib.library_segment -> std_ppcmds
val print_library_entry : bool -> (section_path * Lib.node) -> std_ppcmds
val print_full_context : unit -> std_ppcmds
val print_full_context_typ : unit -> std_ppcmds
val print_crible : identifier -> unit
val print_sec_context : string -> std_ppcmds
val print_sec_context_typ : string -> std_ppcmds
val print_val : env -> unsafe_judgment -> std_ppcmds
val print_type : env -> unsafe_judgment -> std_ppcmds
val print_eval :
  'a reduction_function -> env -> unsafe_judgment -> std_ppcmds
val print_mutual :
  section_path -> Declarations.mutual_inductive_body -> std_ppcmds
val print_name : identifier -> std_ppcmds
val print_opaque_name : identifier -> std_ppcmds
val print_local_context : unit -> std_ppcmds

(*i
val print_extracted_name : identifier -> std_ppcmds
val print_extraction : unit -> std_ppcmds
val print_extracted_vars : unit -> std_ppcmds
i*)

(* Pretty-printing functions for classes and coercions *)
val print_graph : unit -> std_ppcmds
val print_classes : unit -> std_ppcmds
val print_coercions : unit -> std_ppcmds
val print_path_between : identifier -> identifier -> std_ppcmds


val crible : (string -> env -> constr -> unit) -> identifier ->
  unit
val inspect : int -> std_ppcmds

