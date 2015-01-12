(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Globnames
open Miniml
open Declarations

module Refset' : CSig.SetS with type elt = global_reference
module Refmap' : Map.S with type key = global_reference

val safe_basename_of_global : global_reference -> Id.t

(*s Warning and Error messages. *)

val warning_axioms : unit -> unit
val warning_opaques : bool -> unit
val warning_both_mod_and_cst :
 qualid -> module_path -> global_reference -> unit
val warning_id : string -> unit
val error_axiom_scheme : global_reference -> int -> 'a
val error_constant : global_reference -> 'a
val error_inductive : global_reference -> 'a
val error_nb_cons : unit -> 'a
val error_module_clash : module_path -> module_path -> 'a
val error_no_module_expr : module_path -> 'a
val error_singleton_become_prop : Id.t -> 'a
val error_unknown_module : qualid -> 'a
val error_scheme : unit -> 'a
val error_not_visible : global_reference -> 'a
val error_MPfile_as_mod : module_path -> bool -> 'a
val check_inside_module : unit -> unit
val check_inside_section : unit -> unit
val check_loaded_modfile : module_path -> unit
val msg_non_implicit : global_reference -> int -> Name.t -> string
val error_non_implicit : string -> 'a

val info_file : string -> unit

(*s utilities about [module_path] and [kernel_names] and [global_reference] *)

val occur_kn_in_ref : mutual_inductive -> global_reference -> bool
val repr_of_r : global_reference -> module_path * DirPath.t * Label.t
val modpath_of_r : global_reference -> module_path
val label_of_r : global_reference -> Label.t
val base_mp : module_path -> module_path
val is_modfile : module_path -> bool
val string_of_modfile : module_path -> string
val file_of_modfile : module_path -> string
val is_toplevel : module_path -> bool
val at_toplevel : module_path -> bool
val visible_con : constant -> bool
val mp_length : module_path -> int
val prefixes_mp : module_path -> MPset.t
val common_prefix_from_list :
  module_path -> module_path list -> module_path option
val get_nth_label_mp : int -> module_path -> Label.t
val labels_of_ref : global_reference -> module_path * Label.t list

(*s Some table-related operations *)

val add_term : constant -> ml_decl -> unit
val lookup_term : constant -> ml_decl

val add_type : constant -> ml_schema -> unit
val lookup_type : constant -> ml_schema

val add_ind : mutual_inductive -> mutual_inductive_body -> ml_ind -> unit
val lookup_ind : mutual_inductive -> mutual_inductive_body * ml_ind

val add_inductive_kind : mutual_inductive -> inductive_kind -> unit
val is_coinductive : global_reference -> bool
val is_coinductive_type : ml_type -> bool
(* What are the fields of a record (empty for a non-record) *)
val get_record_fields :
  global_reference -> global_reference option list
val record_fields_of_type : ml_type -> global_reference option list

val add_recursors : Environ.env -> mutual_inductive -> unit
val is_recursor : global_reference -> bool

val add_projection : int -> constant -> inductive -> unit
val is_projection : global_reference -> bool
val projection_arity : global_reference -> int
val projection_info : global_reference -> inductive * int (* arity *)

val add_info_axiom : global_reference -> unit
val remove_info_axiom : global_reference -> unit
val add_log_axiom : global_reference -> unit

val add_opaque : global_reference -> unit
val remove_opaque : global_reference -> unit

val reset_tables : unit -> unit

(*s AccessOpaque parameter *)

val access_opaque : unit -> bool

(*s AutoInline parameter *)

val auto_inline : unit -> bool

(*s TypeExpand parameter *)

val type_expand : unit -> bool

(*s KeepSingleton parameter *)

val keep_singleton : unit -> bool

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

(*s Controls whether dummy lambda are removed *)

val conservative_types : unit -> bool

(*s A comment to print at the beginning of the files *)

val file_comment : unit -> string

(*s Target language. *)

type lang = Ocaml | Haskell | Scheme
val lang : unit -> lang

(*s Extraction modes: modular or monolithic, library or minimal ?

Nota:
 - Recursive Extraction : monolithic, minimal
 - Separate Extraction : modular, minimal
 - Extraction Library : modular, library
*)

val set_modular : bool -> unit
val modular : unit -> bool

val set_library : bool -> unit
val library : unit -> bool

(*s Table for custom inlining *)

val to_inline : global_reference -> bool
val to_keep : global_reference -> bool

(*s Table for implicits arguments *)

val implicits_of_global : global_reference -> int list

(*s Table for user-given custom ML extractions. *)

(* UGLY HACK: registration of a function defined in [extraction.ml] *)
val type_scheme_nb_args_hook : (Environ.env -> Term.constr -> int) Hook.t

val is_custom : global_reference -> bool
val is_inline_custom : global_reference -> bool
val find_custom : global_reference -> string
val find_type_custom : global_reference -> string list * string

val is_custom_match : ml_branch array -> bool
val find_custom_match : ml_branch array -> string

(*s Extraction commands. *)

val extraction_language : lang -> unit
val extraction_inline : bool -> reference list -> unit
val print_extraction_inline : unit -> Pp.std_ppcmds
val reset_extraction_inline : unit -> unit
val extract_constant_inline :
  bool -> reference -> string list -> string -> unit
val extract_inductive :
  reference -> string -> string list -> string option -> unit


type int_or_id = ArgInt of int | ArgId of Id.t
val extraction_implicit : reference -> int_or_id list -> unit

(*s Table of blacklisted filenames *)

val extraction_blacklist : Id.t list -> unit
val reset_extraction_blacklist : unit -> unit
val print_extraction_blacklist : unit -> Pp.std_ppcmds



