(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Global options of the system. *)

val boot : bool ref
val load_init : bool ref

val batch_mode : bool ref
type compilation_mode = BuildVo | BuildVio | Vio2Vo
val compilation_mode : compilation_mode ref

type async_proofs = APoff | APonLazy | APon
val async_proofs_mode : async_proofs ref
type cache = Force
val async_proofs_cache : cache option ref
val async_proofs_n_workers : int ref
val async_proofs_n_tacworkers : int ref
val async_proofs_private_flags : string option ref
val async_proofs_is_worker : unit -> bool
val async_proofs_is_master : unit -> bool
val async_proofs_full : bool ref
val async_proofs_never_reopen_branch : bool ref
val async_proofs_flags_for_workers : string list ref
val async_proofs_worker_id : string ref
type priority = Low | High
val async_proofs_worker_priority : priority ref
val string_of_priority : priority -> string
val priority_of_string : string -> priority

val debug : bool ref
val in_debugger : bool ref
val in_toplevel : bool ref

val profile : bool

val print_emacs : bool ref
val coqtop_ui : bool ref

val ide_slave : bool ref
val ideslave_coqtop_flags : string option ref

val time : bool ref

val we_are_parsing : bool ref

val raw_print : bool ref
val record_print : bool ref
val univ_print : bool ref

type compat_version = V8_2 | V8_3 | V8_4 | Current
val compat_version : compat_version ref
val version_strictly_greater : compat_version -> bool
val version_less_or_equal : compat_version -> bool
val pr_version : compat_version -> string

val beautify : bool ref
val make_beautify : bool -> unit
val do_beautify : unit -> bool
val beautify_file : bool ref

val make_silent : bool -> unit
val is_silent : unit -> bool
val is_verbose : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b
val verbosely : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

val make_auto_intros : bool -> unit
val is_auto_intros : unit -> bool

val program_mode : bool ref
val is_program_mode : unit -> bool

(** Global universe polymorphism flag. *)
val make_universe_polymorphism : bool -> unit
val is_universe_polymorphism : unit -> bool

(** Local universe polymorphism flag. *)
val make_polymorphic_flag : bool -> unit
val use_polymorphic_flag : unit -> bool

val make_warn : bool -> unit
val if_warn : ('a -> unit) -> 'a -> unit

(** Temporarily activate an option (to activate option [o] on [f x y z],
   use [with_option o (f x y) z]) *)
val with_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** As [with_option], but on several flags. *)
val with_options : bool ref list -> ('a -> 'b) -> 'a -> 'b

(** Temporarily deactivate an option *)
val without_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** Temporarily extends the reference to a list *)
val with_extra_values : 'c list ref -> 'c list -> ('a -> 'b) -> 'a -> 'b

(** If [None], no limit *)
val set_print_hyps_limit : int option -> unit
val print_hyps_limit : unit -> int option

(** Options for external tools *)

(** Returns string format for default browser to use from Coq or CoqIDE *)
val browser_cmd_fmt : string

val is_standard_doc_url : string -> bool

(** Options for specifying where coq librairies reside *)
val coqlib_spec : bool ref
val coqlib : string ref

(** Options for specifying where OCaml binaries reside *)
val camlbin_spec : bool ref
val camlbin : string ref
val camlp4bin_spec : bool ref
val camlp4bin : string ref

(** Level of inlining during a functor application *)
val set_inline_level : int -> unit
val get_inline_level : unit -> int
val default_inline_level : int

(* Disabling native code compilation for conversion and normalization *)
val no_native_compiler : bool ref

(* Print the mod uid associated to a vo file by the native compiler *)
val print_mod_uid : bool ref

val tactic_context_compat : bool ref
(** Set to [true] to trigger the compatibility bugged context matching (old
    context vs. appcontext) is set. *)
