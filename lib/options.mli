(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* Global options of the system. *)

val boot : bool ref

val batch_mode : bool ref

val debug : bool ref

val print_emacs : bool ref
val emacs_str : string -> string

val make_silent : bool -> unit
val is_silent : unit -> bool
val is_verbose : unit -> bool
val silently : ('a -> 'b) -> 'a -> 'b
val if_silent : ('a -> unit) -> 'a -> unit
val if_verbose : ('a -> unit) -> 'a -> unit

val set_print_hyps_limit : int -> unit
val unset_print_hyps_limit : unit -> unit
val print_hyps_limit : unit -> int option

val make_mes_ambig : bool -> unit
val is_mes_ambig : unit -> bool
val without_mes_ambig : ('a -> 'b) -> 'a -> 'b

val add_unsafe : string -> unit
val is_unsafe : string -> bool

val immediate_discharge : bool
