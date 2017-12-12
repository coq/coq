(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Global options of the system. *)

(** Command-line flags  *)

val boot : bool ref

(** Set by coqtop to tell the kernel to output to the aux file; will
    be eventually removed by cleanups such as PR#1103 *)
val record_aux_file : bool ref

(* Flag set when the test-suite is called. Its only effect to display
   verbose information for `Fail` *)
val test_mode : bool ref

(** Async-related flags *)
val async_proofs_worker_id : string ref
val async_proofs_is_worker : unit -> bool

(** Debug flags *)
val debug : bool ref
val in_debugger : bool ref
val in_toplevel : bool ref

val profile : bool

(* -ide_slave: printing will be more verbose, will affect stm caching *)
val ide_slave : bool ref
val ideslave_coqtop_flags : string option ref

(* -time option: every command will be wrapped with `Time` *)
val time : bool ref

(* development flag to detect race conditions, it should go away. *)
val we_are_parsing : bool ref

(* Set Printing All flag. For some reason it is a global flag *)
val raw_print : bool ref

(* Univ print flag, never set anywere. Maybe should belong to Univ? *)
val univ_print : bool ref

type compat_version = VOld | V8_5 | V8_6 | V8_7 | Current
val compat_version : compat_version ref
val version_compare : compat_version -> compat_version -> int
val version_strictly_greater : compat_version -> bool
val version_less_or_equal : compat_version -> bool
val pr_version : compat_version -> string

(* Beautify command line flags, should move to printing? *)
val beautify : bool ref
val beautify_file : bool ref

(* Coq quiet mode. Note that normal mode is called "verbose" here,
   whereas [quiet] supresses normal output such as goals in coqtop *)
val quiet : bool ref
val silently : ('a -> 'b) -> 'a -> 'b
val verbosely : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

(* Miscellaneus flags for vernac *)
val make_auto_intros : bool -> unit
val is_auto_intros : unit -> bool

val program_mode : bool ref
val is_program_mode : unit -> bool

(** Global universe polymorphism flag. *)
val make_universe_polymorphism : bool -> unit
val is_universe_polymorphism : unit -> bool

(** Global polymorphic inductive cumulativity flag. *)
val make_polymorphic_inductive_cumulativity : bool -> unit
val is_polymorphic_inductive_cumulativity : unit -> bool

val warn : bool ref
val make_warn : bool -> unit
val if_warn : ('a -> unit) -> 'a -> unit

(** [with_modified_ref r nf f x] Temporarily modify a reference in the
    call to [f x] . Be very careful with these functions, it is very
    easy to fall in the typical problem with effects:

    with_modified_ref r nf f x y != with_modified_ref r nf (f x) y

*)
val with_modified_ref : 'c ref -> ('c -> 'c) -> ('a -> 'b) -> 'a -> 'b

(** Temporarily activate an option (to activate option [o] on [f x y z],
   use [with_option o (f x y) z]) *)
val with_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** As [with_option], but on several flags. *)
val with_options : bool ref list -> ('a -> 'b) -> 'a -> 'b

(** Temporarily deactivate an option *)
val without_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(** Temporarily extends the reference to a list *)
val with_extra_values : 'c list ref -> 'c list -> ('a -> 'b) -> 'a -> 'b

(** Options for external tools *)

(** Returns string format for default browser to use from Coq or CoqIDE *)
val browser_cmd_fmt : string

val is_standard_doc_url : string -> bool

(** Options for specifying where coq librairies reside *)
val coqlib_spec : bool ref
val coqlib : string ref

(** Level of inlining during a functor application *)
val set_inline_level : int -> unit
val get_inline_level : unit -> int
val default_inline_level : int

(** When producing vo objects, also compile the native-code version *)
val output_native_objects : bool ref

(** Print the mod uid associated to a vo file by the native compiler *)
val print_mod_uid : bool ref

val profile_ltac : bool ref
val profile_ltac_cutoff : float ref

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode : bool ref
val set_dump_bytecode : bool -> unit
val get_dump_bytecode : unit -> bool
