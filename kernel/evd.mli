
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
(*i*)

(* The type of mappings for existential variables.
   The keys are integers and the associated information is a record
   containing the type of the evar ([concl]), the signature under which 
   it was introduced ([hyps]) and its definition ([body]). *)

type evar = int

val new_evar : unit -> evar

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type evar_info = {
  evar_concl : typed_type;
  evar_hyps  : typed_type signature;
  evar_body  : evar_body }

type evar_map

val dom : evar_map -> evar list
val map : evar_map -> evar -> evar_info
val rmv : evar_map -> evar -> evar_map
val remap : evar_map -> evar -> evar_info -> evar_map
val in_dom : evar_map -> evar -> bool
val to_list : evar_map -> (evar * evar_info) list

val mt_evd : evar_map
val add_with_info : evar_map -> evar -> evar_info -> evar_map
val add_noinfo : 
  evar_map -> evar -> typed_type signature -> typed_type -> evar_map

val define : evar_map -> evar -> constr -> evar_map

val non_instantiated : evar_map -> (evar * evar_info) list
val is_evar : evar_map -> evar -> bool

val is_defined : evar_map -> evar -> bool

