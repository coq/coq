
(* $Id$ *)

(*i*)
open Names
open Term
open Evd
open Environ
(*i*)

(* This family of functions assumes its constr argument is known to be
   well-typable. It does not type-check, just recompute the type
   without any costly verifications. On non well-typable terms, it
   either produces a wrong result or raise an anomaly. Use with care.
   It doesn't handle predicative universes too. *)

type metamap = (int * constr) list

val get_type_of : env -> 'a evar_map -> constr -> constr
val get_type_of_with_meta : env -> 'a evar_map -> metamap -> constr -> constr
val get_sort_of : env -> 'a evar_map -> constr -> sorts

(*Makes an unsafe judgment from a constr*)
val mk_unsafe_judgment:env->'a evar_map->constr ->unsafe_judgment;;
