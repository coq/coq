
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Rawterm
open Pattern
(*i*)

(* Translation from AST to terms. *)

val interp_rawconstr     : 'a evar_map -> env -> Coqast.t -> rawconstr
val interp_constr        : 'a evar_map -> env -> Coqast.t -> constr
val interp_casted_constr : 'a evar_map -> env -> Coqast.t -> constr -> constr
val interp_type          : 'a evar_map -> env -> Coqast.t -> constr
val interp_sort          : Coqast.t -> sorts

val interp_openconstr    :
  'a evar_map -> env -> Coqast.t -> (int * constr) list * constr
val interp_casted_openconstr    :
  'a evar_map -> env -> Coqast.t -> constr -> (int * constr) list * constr

val judgment_of_rawconstr : 'a evar_map -> env -> Coqast.t -> unsafe_judgment
val type_judgment_of_rawconstr :
  'a evar_map -> env -> Coqast.t -> unsafe_type_judgment

(*Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it*)
val interp_constr_gen     :
  'a evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> Coqast.t -> constr option -> constr

(*Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it, and turning unresolved evar into metas*)
val interp_openconstr_gen     :
  'a evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> Coqast.t -> constr option
      -> (int * constr) list * constr

(*Interprets constr patterns according to a list of instantiations
  (variables)*)
val interp_constrpattern_gen :
  'a evar_map -> env -> (identifier * constr) list -> Coqast.t ->
    int list * constr_pattern

val interp_constrpattern : 
  'a evar_map -> env -> Coqast.t -> int list * constr_pattern

(*s Globalization of AST quotations (mainly used to get statically
    bound idents in grammar or pretty-printing rules) *)
val globalize_constr : Coqast.t -> Coqast.t
val globalize_ast    : Coqast.t -> Coqast.t

(* This transforms args of a qualid keyword into a qualified ident *)
(* it does no relocation *)
val interp_qualid : Coqast.t list -> qualid

(* Translation rules from V6 to V7:

constr_of_com_casted -> interp_casted_constr
constr_of_com_sort   -> interp_type
constr_of_com        -> interp_constr
rawconstr_of_com     -> interp_rawconstr  [+ env instead of sign]
type_of_com          -> types_of_com Evd.empty
constr_of_com1 true  -> interp_type
*)
