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
val print_emacs_safechar : bool ref

val term_quality : bool ref

val xml_export : bool ref

val dont_load_proofs : bool ref

val raw_print : bool ref

val translate : bool ref
val make_translate : bool -> unit
val do_translate : unit -> bool
val translate_file : bool ref
val translate_syntax : bool ref

val make_silent : bool -> unit
val is_silent : unit -> bool
val is_verbose : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

val hash_cons_proofs : bool ref

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

(* Options for the virtual machine *)

val set_boxed_definitions : bool -> unit
val boxed_definitions : unit -> bool

(* Options for external tools *)

(* Returns head and tail of printf string format *)
(* ocaml doesn't allow not applied formats *)
val browser_cmd_fmt : string * string
 
