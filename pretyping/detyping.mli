
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Environ
open Rawterm
(*i*)

(* [detype avoid env c] turns [c], typed in [env], into a rawconstr. *)
(* De Bruijn indexes are turned to bound names, avoiding names in [avoid] *)

val detype : identifier list -> names_context -> constr -> rawconstr

(* look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_renamed : named_context -> constr -> identifier -> int option
val lookup_index_as_renamed : constr -> int -> int option


val force_wildcard : unit -> bool
val synthetize_type : unit -> bool
val force_if : case_info -> bool
val force_let : case_info -> bool
