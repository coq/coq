(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

val pr : string -> unit
val pri : int -> unit
val prch : char -> unit
val pnl : unit -> unit
val prl : string -> unit

val propt : ('a -> unit) -> 'a option -> unit
val prlist : ('a -> unit) -> string -> 'a list -> unit

val init : unit -> unit

val trace : string list -> unit
val untrace : string list -> unit
val untrace_all : unit -> unit

val enter : string -> unit
val enter_pr : string -> ('a -> unit) -> 'a -> unit

val leave : string -> 'a -> 'a
val leave_pr : string -> ('a -> unit) -> 'a -> 'a

val branch : string -> string -> unit
val branch_pr : string -> string -> ('a -> unit) -> 'a -> unit
