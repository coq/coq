(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Names
open Sign
open Term
open Environ
open Reductionops
open Libnames
open Nametab
(*i*)

(* A Pretty-Printer for the Calculus of Inductive Constructions. *)

val assumptions_for_print : name list -> Termops.names_context

val print_closed_sections : bool ref
val print_impl_args : Impargs.implicits_list -> std_ppcmds
val print_context : bool -> int option -> Lib.library_segment -> std_ppcmds
val print_library_entry : bool -> (object_name * Lib.node) -> std_ppcmds option
val print_full_context : unit -> std_ppcmds
val print_full_context_typ : unit -> std_ppcmds
val print_sec_context : reference -> std_ppcmds
val print_sec_context_typ : reference -> std_ppcmds
val print_judgment : env -> unsafe_judgment -> std_ppcmds
val print_safe_judgment : env -> Safe_typing.judgment -> std_ppcmds
val print_eval :
  reduction_function -> env -> unsafe_judgment -> std_ppcmds
(* This function is exported for the graphical user-interface pcoq *)
val build_inductive : mutual_inductive -> int ->
  global_reference * rel_context * types * identifier array * types array
val print_mutual : mutual_inductive -> std_ppcmds
val print_name : reference -> std_ppcmds
val print_opaque_name : reference -> std_ppcmds
val print_local_context : unit -> std_ppcmds
val print_about : reference -> std_ppcmds
val print_impargs : reference -> std_ppcmds

(*i
val print_extracted_name : identifier -> std_ppcmds
val print_extraction : unit -> std_ppcmds
val print_extracted_vars : unit -> std_ppcmds
i*)

(* Pretty-printing functions for classes and coercions *)
val print_graph : unit -> std_ppcmds
val print_classes : unit -> std_ppcmds
val print_coercions : unit -> std_ppcmds
val print_path_between : Classops.cl_typ -> Classops.cl_typ -> std_ppcmds

val inspect : int -> std_ppcmds

(* Locate *)
val print_located_qualid : reference -> std_ppcmds
