
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
open Environ
(*i*)

(* The type of mappings for existential variables.
   The keys are integers and the associated information is a record
   containing the type of the evar ([concl]), the signature under which 
   it was introduced ([hyps]) and its definition ([body]). 
   [evar_info] is used to add any other kind of information. *)

type evar = int

val new_evar : unit -> evar

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type 'a evar_info = {
  evar_concl : constr;
  evar_env : unsafe_env;
  evar_body : evar_body;
  evar_info : 'a }

type 'a evar_map

val empty : 'a evar_map

val add : 'a evar_map -> evar -> 'a evar_info -> 'a evar_map

val dom : 'a evar_map -> evar list
val map : 'a evar_map -> evar -> 'a evar_info
val rmv : 'a evar_map -> evar -> 'a evar_map
val remap : 'a evar_map -> evar -> 'a evar_info -> 'a evar_map
val in_dom : 'a evar_map -> evar -> bool
val to_list : 'a evar_map -> (evar * 'a evar_info) list

val define : 'a evar_map -> evar -> constr -> 'a evar_map

val non_instantiated : 'a evar_map -> (evar * 'a evar_info) list
val is_evar : 'a evar_map -> evar -> bool

val is_defined : 'a evar_map -> evar -> bool

val metamap : 'a evar_map -> (int * constr) list

val evar_hyps : 'a evar_info -> typed_type signature
