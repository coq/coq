(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global options of the system. *)

(** WARNING: don't add new entries to this file!

    This file is own its way to deprecation in favor of a purely
   functional state, but meanwhile it will contain options that are
   truly global to the system such as [compat] or [debug]

    If you are thinking about adding a global flag, well, just
   don't. First of all, options make testins exponentially more
   expensive, due to the growth of flag combinations. So please make
   some effort in order for your idea to work in a configuration-free
   manner.

    If you absolutely must pass an option to your new system, then do
   so as a functional argument so flags are exposed to unit
   testing. Then, register such parameters with the proper
   state-handling mechanism of the top-level subsystem of Coq.

 *)

(** Command-line flags  *)

(** Set by coqtop to tell the kernel to output to the aux file; will
    be eventually removed by cleanups such as PR#1103 *)
val record_aux_file : bool ref

(** Async-related flags *)
val async_proofs_worker_id : string ref
val async_proofs_is_worker : unit -> bool

(** Debug flags *)
val debug : bool ref
val in_debugger : bool ref
val in_toplevel : bool ref

val profile : bool

(* development flag to detect race conditions, it should go away. *)
val we_are_parsing : bool ref

(* Set Printing All flag. For some reason it is a global flag *)
val raw_print : bool ref

type compat_version = V8_8 | V8_9 | Current
val compat_version : compat_version ref
val version_compare : compat_version -> compat_version -> int
val version_strictly_greater : compat_version -> bool
val version_less_or_equal : compat_version -> bool
val pr_version : compat_version -> string

(* Beautify command line flags, should move to printing? *)
val beautify : bool ref
val beautify_file : bool ref

(* Coq quiet mode. Note that normal mode is called "verbose" here,
   whereas [quiet] suppresses normal output such as goals in coqtop *)
val quiet : bool ref
val silently : ('a -> 'b) -> 'a -> 'b
val verbosely : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

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

(** Level of inlining during a functor application *)
val set_inline_level : int -> unit
val get_inline_level : unit -> int
val default_inline_level : int

(** Global profile_ltac flag  *)
val profile_ltac : bool ref
val profile_ltac_cutoff : float ref
