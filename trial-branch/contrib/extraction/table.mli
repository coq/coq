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
val pr_long_global : global_reference -> Pp.std_ppcmds


(*s Warning and Error messages. *)

val warning_axioms : unit -> unit
val error_axiom_scheme : global_reference -> int -> 'a
val error_constant : global_reference -> 'a
val error_inductive : global_reference -> 'a
val error_nb_cons : unit -> 'a
val error_module_clash : string -> 'a 
val error_unknown_module : qualid -> 'a
val error_scheme : unit -> 'a
val error_not_visible : global_reference -> 'a
val error_MPfile_as_mod : module_path -> bool -> 'a
val error_record : global_reference -> 'a 
val check_inside_module : unit -> unit
val check_inside_section : unit -> unit
val check_loaded_modfile : module_path -> unit

val info_file : string -> unit

(*s utilities about [module_path] and [kernel_names] and [global_reference] *)

val occur_kn_in_ref : kernel_name -> global_reference -> bool
val modpath_of_r : global_reference -> module_path
val label_of_r : global_reference -> label
val current_toplevel : unit -> module_path
val base_mp : module_path -> module_path
val is_modfile : module_path -> bool
val string_of_modfile : module_path -> string 
val is_toplevel : module_path -> bool
val at_toplevel : module_path -> bool 
val visible_kn : kernel_name -> bool
val visible_con : constant -> bool
val mp_length : module_path -> int
val prefixes_mp : module_path -> MPset.t
val modfile_of_mp : module_path -> module_path
val common_prefix_from_list : module_path -> module_path list -> module_path
val add_labels_mp : module_path -> label list -> module_path
val get_nth_label_mp : int -> module_path -> label
val get_nth_label : int -> global_reference -> label
val labels_of_ref : global_reference -> module_path * label list

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

val add_info_axiom : global_reference -> unit
val add_log_axiom : global_reference -> unit

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

type lang = Ocaml | Haskell | Scheme
val lang : unit -> lang 

(*s Extraction mode: modular or monolithic *)

val set_modular : bool -> unit
val modular : unit -> bool 

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




