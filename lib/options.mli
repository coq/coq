(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
val emacs_str : string -> string

val term_quality : bool ref

val xml_export : bool ref

val dont_load_proofs : bool ref

val raw_print : bool ref

val v7 : bool ref
val v7_only : bool ref

val translate : bool ref
val make_translate : bool -> unit
val do_translate : unit -> bool
val translate_file : bool ref
val translate_syntax : bool ref
val translate_strict_impargs : bool ref

val make_silent : bool -> unit
val is_silent : unit -> bool
val is_verbose : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

(* Temporary activate an option ('c must be an atomic type) *)
val with_option : bool ref -> ('a -> 'b) -> 'a -> 'b

(* If [None], no limit *)
val set_print_hyps_limit : int option -> unit
val print_hyps_limit : unit -> int option

val add_unsafe : string -> unit
val is_unsafe : string -> bool

(* Dump of globalization (to be used by coqdoc) *)

val dump : bool ref
val dump_into_file : string -> unit
val dump_string : string -> unit

