
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
(*i*)

val gencompr  : path_kind -> Coqast.t -> std_ppcmds
val gentermpr : path_kind -> 'a assumptions -> constr -> std_ppcmds
val gentacpr  : Coqast.t -> std_ppcmds

val print_arguments : bool ref
val print_casts     : bool ref
val print_emacs     : bool ref
val with_implicits  : ('a -> 'b) -> 'a -> 'b
