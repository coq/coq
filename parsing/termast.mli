
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Rawterm
(*i*)

val print_implicits : bool ref

(* Translation of pattern, rawterm and term into syntax trees for printing *)

val ast_of_pattern : pattern -> Coqast.t
val ast_of_rawconstr : rawconstr -> Coqast.t
val bdize : bool -> unit assumptions -> constr -> Coqast.t
val bdize_no_casts : bool -> unit assumptions -> constr -> Coqast.t

(* look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_renamed :
  unit assumptions -> constr -> identifier -> int option
val lookup_index_as_renamed : constr -> int -> int option
