
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

val assumptions_for_print : name list -> unit assumptions

val print_basename : section_path -> string
val print_basename_mind : section_path -> identifier -> string
val print_closed_sections : bool ref
val print_impl_args : int list -> std_ppcmds
val print_env : path_kind -> (name * constr) list -> std_ppcmds
val print_context : bool -> Lib.library_segment -> std_ppcmds
val print_library_entry : bool -> (section_path * Lib.node) -> std_ppcmds
val print_full_context : unit -> std_ppcmds
val print_full_context_typ : unit -> std_ppcmds
val print_crible : identifier -> unit
val print_sec_context : string -> std_ppcmds
val print_sec_context_typ : string -> std_ppcmds
val print_val : context -> unsafe_judgment -> std_ppcmds
val print_type : context -> unsafe_judgment -> std_ppcmds
val print_eval :
  'a reduction_function -> context -> unsafe_judgment -> std_ppcmds
val implicit_args_msg : mutual_inductive_packet array -> std_ppcmds
val print_mutual : path_kind -> mutual_inductive_body -> std_ppcmds
val print_name : identifier -> std_ppcmds
val print_opaque_name : identifier -> std_ppcmds
val print_local_context : unit -> std_ppcmds
val print_extracted_name : identifier -> std_ppcmds
val print_extraction : unit -> std_ppcmds
val print_extracted_vars : unit -> std_ppcmds
val crible : (string -> unit assumptions -> constr -> unit) -> identifier ->
  unit
val inspect : int -> std_ppcmds
