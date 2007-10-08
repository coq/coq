(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Libnames
open Miniml
open Declarations

val id_of_global : global_reference -> identifier

(*s Warning and Error messages. *)

val error_axiom_scheme : global_reference -> int -> 'a
val warning_info_ax : global_reference -> unit
val warning_log_ax : global_reference -> unit
val error_constant : global_reference -> 'a
val error_inductive : global_reference -> 'a
val error_nb_cons : unit -> 'a
val error_module_clash : string -> 'a 
val error_unknown_module : qualid -> 'a
val error_toplevel : unit -> 'a
val error_scheme : unit -> 'a
val error_not_visible : global_reference -> 'a
val error_unqualified_name : string -> string -> 'a 
val error_MPfile_as_mod : dir_path -> 'a
val error_record : global_reference -> 'a 
val check_inside_module : unit -> unit
val check_inside_section : unit -> unit

(*s utilities concerning [module_path]. *)

val occur_kn_in_ref : kernel_name -> global_reference -> bool
val modpath_of_r : global_reference -> module_path
val label_of_r : global_reference -> label

val current_toplevel : unit -> module_path
val base_mp : module_path -> module_path
val is_modfile : module_path -> bool 
val is_toplevel : module_path -> bool
val at_toplevel : module_path -> bool 
val visible_kn : kernel_name -> bool
val visible_con : constant -> bool

(*s Some table-related operations *)

val add_term : constant -> ml_decl -> unit
val lookup_term : constant -> ml_decl

val add_type : constant -> ml_schema -> unit
val lookup_type : constant -> ml_schema

val add_ind : kernel_name -> mutual_inductive_body -> ml_ind -> unit
val lookup_ind : kernel_name -> mutual_inductive_body * ml_ind

val add_recursors : Environ.env -> kernel_name -> unit
val is_recursor : global_reference -> bool 

val add_projection : int -> constant -> unit
val is_projection : global_reference -> bool 
val projection_arity : global_reference -> int

val reset_tables : unit -> unit

(*s AutoInline parameter *) 

val auto_inline : unit -> bool

(*s TypeExpand parameter *) 

val type_expand : unit -> bool

(*s Optimize parameter *) 

type opt_flag = 
    { opt_kill_dum : bool; (* 1 *) 
      opt_fix_fun : bool;   (* 2 *)
      opt_case_iot : bool;  (* 4 *)
      opt_case_idr : bool;  (* 8 *)
      opt_case_idg : bool;  (* 16 *)
      opt_case_cst : bool;  (* 32 *)
      opt_case_fun : bool;  (* 64 *)
      opt_case_app : bool;  (* 128 *)
      opt_let_app : bool;   (* 256 *)
      opt_lin_let : bool;   (* 512 *)
      opt_lin_beta : bool } (* 1024 *)

val optims :  unit -> opt_flag

(*s Target language. *)

type lang = Ocaml | Haskell | Scheme | Toplevel
val lang : unit -> lang 

(*s Table for custom inlining *) 

val to_inline : global_reference -> bool
val to_keep : global_reference -> bool

(*s Table for user-given custom ML extractions. *)

(* UGLY HACK: registration of a function defined in [extraction.ml] *)
val register_type_scheme_nb_args : (Environ.env -> Term.constr -> int) -> unit

val is_custom : global_reference -> bool
val is_inline_custom : global_reference -> bool
val find_custom : global_reference -> string
val find_type_custom : global_reference -> string list * string

(*s Extraction commands. *)

val extraction_language : lang -> unit
val extraction_inline : bool -> reference list -> unit
val print_extraction_inline : unit -> unit
val reset_extraction_inline : unit -> unit
val extract_constant_inline : 
  bool -> reference -> string list -> string -> unit
val extract_inductive : reference -> string * string list -> unit




