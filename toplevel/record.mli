
(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
(*i*)

(* [declare_projections id coers params fields] declare projections of
   record [id] (if allowed), and put them as coercions accordingly to
   [coers] *)

val declare_projections :
  identifier -> bool list -> 
   named_context -> named_context -> constant_path option list

val definition_structure :
   bool * identifier * (identifier * Coqast.t) list *
  (bool * (identifier * bool * Coqast.t)) list * identifier * sorts -> unit
