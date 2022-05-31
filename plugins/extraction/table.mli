(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Refset' : CSig.SetS with type elt = Names.GlobRef.t
module Refmap' : CSig.MapS with type key = Names.GlobRef.t

val safe_basename_of_global : Names.GlobRef.t -> Names.Id.t

(*s Warning and Error messages. *)

val warning_axioms : unit -> unit
val warning_opaques : bool -> unit
val warning_ambiguous_name : ?loc:Loc.t -> Libnames.qualid * Names.ModPath.t * Names.GlobRef.t -> unit
val warning_id : string -> unit
val error_axiom_scheme : ?loc:Loc.t -> Names.GlobRef.t -> int -> 'a
val error_constant : ?loc:Loc.t -> Names.GlobRef.t -> 'a
val error_inductive : ?loc:Loc.t -> Names.GlobRef.t -> 'a
val error_nb_cons : unit -> 'a
val error_module_clash : Names.ModPath.t -> Names.ModPath.t -> 'a
val error_no_module_expr : Names.ModPath.t -> 'a
val error_singleton_become_prop : Names.Id.t -> Names.GlobRef.t option -> 'a
val error_unknown_module : ?loc:Loc.t -> Libnames.qualid -> 'a
val error_scheme : unit -> 'a
val error_not_visible : Names.GlobRef.t -> 'a
val error_MPfile_as_mod : Names.ModPath.t -> bool -> 'a
val check_inside_module : unit -> unit
val check_inside_section : unit -> unit
val check_loaded_modfile : Names.ModPath.t -> unit
val msg_of_implicit : Miniml.kill_reason -> string
val err_or_warn_remaining_implicit : Miniml.kill_reason -> unit

val info_file : string -> unit

(*s utilities about [module_path] and [kernel_names] and [Names.GlobRef.t] *)

val occur_kn_in_ref : Names.MutInd.t -> Names.GlobRef.t -> bool
val repr_of_r : Names.GlobRef.t -> Names.ModPath.t * Names.Label.t
val modpath_of_r : Names.GlobRef.t -> Names.ModPath.t
val label_of_r : Names.GlobRef.t -> Names.Label.t
val base_mp : Names.ModPath.t -> Names.ModPath.t
val is_modfile : Names.ModPath.t -> bool
val string_of_modfile : Names.ModPath.t -> string
val file_of_modfile : Names.ModPath.t -> string
val is_toplevel : Names.ModPath.t -> bool
val at_toplevel : Names.ModPath.t -> bool
val mp_length : Names.ModPath.t -> int
val prefixes_mp : Names.ModPath.t -> Names.MPset.t
val common_prefix_from_list :
  Names.ModPath.t -> Names.ModPath.t list -> Names.ModPath.t option
val get_nth_label_mp : int -> Names.ModPath.t -> Names.Label.t
val labels_of_ref : Names.GlobRef.t -> Names.ModPath.t * Names.Label.t list

(*s Some table-related operations *)

(* For avoiding repeated extraction of the same constant or inductive,
   we use cache functions below. Indexing by constant name isn't enough,
   due to modules we could have a same constant name but different
   content. So we check that the [constant_body] hasn't changed from
   recording time to retrieving time. Same for inductive : we store
   [mutual_inductive_body] as checksum. In both case, we should ideally
   also check the env *)

val add_typedef : Names.Constant.t -> Declarations.constant_body -> Miniml.ml_type -> unit
val lookup_typedef : Names.Constant.t -> Declarations.constant_body -> Miniml.ml_type option

val add_cst_type : Names.Constant.t -> Declarations.constant_body -> Miniml.ml_schema -> unit
val lookup_cst_type : Names.Constant.t -> Declarations.constant_body -> Miniml.ml_schema option

val add_ind : Names.MutInd.t -> Declarations.mutual_inductive_body -> Miniml.ml_ind -> unit
val lookup_ind : Names.MutInd.t -> Declarations.mutual_inductive_body -> Miniml.ml_ind option

val add_inductive_kind : Names.MutInd.t -> Miniml.inductive_kind -> unit
val is_coinductive : Names.GlobRef.t -> bool
val is_coinductive_type : Miniml.ml_type -> bool
(* What are the fields of a record (empty for a non-record) *)
val get_record_fields :
  Names.GlobRef.t -> Names.GlobRef.t option list
val record_fields_of_type : Miniml.ml_type -> Names.GlobRef.t option list

val add_recursors : Environ.env -> Names.MutInd.t -> unit
val is_recursor : Names.GlobRef.t -> bool

val add_projection : int -> Names.Constant.t -> Names.inductive -> unit
val is_projection : Names.GlobRef.t -> bool
val projection_arity : Names.GlobRef.t -> int
val projection_info : Names.GlobRef.t -> Names.inductive * int (* arity *)

val add_info_axiom : Names.GlobRef.t -> unit
val remove_info_axiom : Names.GlobRef.t -> unit
val add_log_axiom : Names.GlobRef.t -> unit

val add_opaque : Names.GlobRef.t -> unit
val remove_opaque : Names.GlobRef.t -> unit

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

type lang = Ocaml | Haskell | Scheme | JSON
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

val set_extrcompute : bool -> unit
val is_extrcompute : unit -> bool

(*s Table for custom inlining *)

val to_inline : Names.GlobRef.t -> bool
val to_keep : Names.GlobRef.t -> bool

(*s Table for implicits arguments *)

val implicits_of_global : Names.GlobRef.t -> Int.Set.t

(*s Table for user-given custom ML extractions. *)

(* UGLY HACK: registration of a function defined in [extraction.ml] *)
val type_scheme_nb_args_hook : (Environ.env -> Constr.t -> int) Hook.t

val is_custom : Names.GlobRef.t -> bool
val is_inline_custom : Names.GlobRef.t -> bool
val find_custom : Names.GlobRef.t -> string
val find_type_custom : Names.GlobRef.t -> string list * string

val is_custom_match : Miniml.ml_branch array -> bool
val find_custom_match : Miniml.ml_branch array -> string

(*s Extraction commands. *)

val extraction_language : lang -> unit
val extraction_inline : bool -> Libnames.qualid list -> unit
val print_extraction_inline : unit -> Pp.t
val reset_extraction_inline : unit -> unit
val extract_constant_inline :
  bool -> Libnames.qualid -> string list -> string -> unit
val extract_inductive :
Libnames.qualid -> string -> string list -> string option -> unit


type int_or_id = ArgInt of int | ArgId of Names.Id.t
val extraction_implicit : Libnames.qualid -> int_or_id list -> unit

(*s Table of blacklisted filenames *)

val extraction_blacklist : string list -> unit
val reset_extraction_blacklist : unit -> unit
val print_extraction_blacklist : unit -> Pp.t



