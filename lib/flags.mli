(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Global options of the system. *)

val boot : bool ref
val load_init : bool ref

val batch_mode : bool ref
type compilation_mode = BuildVo | BuildVi | Vi2Vo
val compilation_mode : compilation_mode ref

type async_proofs = APoff | APonLazy | APonParallel of int
val async_proofs_mode : async_proofs ref
val async_proofs_n_workers : int ref
val async_proofs_worker_flags : string option ref

val async_proofs_is_worker : unit -> bool

val debug : bool ref

val print_emacs : bool ref

val term_quality : bool ref

val xml_export : bool ref

val ide_slave : bool ref
val ideslave_coqtop_flags : string option ref

val time : bool ref

val we_are_parsing : bool ref

type load_proofs = Force | Lazy | Dont
val load_proofs : load_proofs ref

val raw_print : bool ref
val record_print : bool ref

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

(** Terminal colouring *)
val make_term_color : bool -> unit
val is_term_color : unit -> bool

val program_mode : bool ref
val is_program_mode : unit -> bool

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

val add_unsafe : string -> unit
val is_unsafe : string -> bool

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
