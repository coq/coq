
(* $Id$ *)

(*i*)
open Names
(*i*)

(* Module markers. *)

type 'a stock

type module_mark

type 'a stocked

type 'a stock_args = {
  name : string;
  proc : string -> 'a }

val make_stock : 'a stock_args -> 'a stock
val make_module_marker : 'a stock -> string list -> module_mark
val stock : 'a stock -> module_mark -> string -> 'a stocked
val retrieve : 'a stock -> 'a stocked -> 'a

