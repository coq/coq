
(*i $Id$ i*)

(*i*)
open Names
open Term
(*i*)

(* [declare_projections id coers params fields] declare projections of
   record [id] (if allowed), and put them as coercions accordingly to
   [coers] *)

val declare_projections :
  identifier -> bool list -> 
   (identifier * types) list -> (identifier * types) list -> 
      constant_path option list

val definition_structure :
   bool * identifier * (identifier * Coqast.t) list *
  (bool * (identifier * Coqast.t)) list * identifier *
  Coqast.t -> unit
