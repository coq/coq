
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
(*i*)

(* Translation of terms into syntax trees. Used for pretty-printing. *)

val print_implicits : bool ref

val bdize : bool -> unit assumptions -> constr -> Coqast.t
val bdize_no_casts : bool -> unit assumptions -> constr -> Coqast.t

(* look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_renamed :
  unit assumptions -> constr -> identifier -> int option
val lookup_index_as_renamed : constr -> int -> int option
