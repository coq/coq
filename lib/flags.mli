(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Global options of the system. *)

val boot : bool ref

val batch_mode : bool ref

val debug : bool ref

val print_emacs : bool ref
val print_emacs_safechar : bool ref

val term_quality : bool ref

val xml_export : bool ref

val dont_load_proofs : bool ref

val raw_print : bool ref

val unicode_syntax : bool ref

type compat_version = V8_2
val compat_version : compat_version option ref
val version_strictly_greater : compat_version -> bool
val version_less_or_equal : compat_version -> bool

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

val make_warn : bool -> unit
val if_warn : ('a -> unit) -> 'a -> unit

val hash_cons_proofs : bool ref

(* Temporary activate an option (to activate option [o] on [f x y z],
   use [with_option o (f x y) z]) *)
val with_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(* Temporary deactivate an option *)
val without_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(* If [None], no limit *)
val set_print_hyps_limit : int option -> unit
val print_hyps_limit : unit -> int option

val add_unsafe : string -> unit
val is_unsafe : string -> bool

(* Options for the virtual machine *)

val set_boxed_definitions : bool -> unit
val boxed_definitions : unit -> bool

(* Options for external tools *)

(* Returns string format for default browser to use from Coq or CoqIDE *)
val browser_cmd_fmt : string

val is_standard_doc_url : string -> bool

(* Substitute %s in the first chain by the second chain *)
val subst_command_placeholder : string -> string -> string

(* Options for specifying where coq librairies reside *)
val coqlib_spec : bool ref
val coqlib : string ref

(* Options for specifying where OCaml binaries reside *)
val camlbin_spec : bool ref
val camlbin : string ref
val camlp4bin_spec : bool ref
val camlp4bin : string ref
