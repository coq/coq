
(* $Id$ *)

(*i*)
open Names
open Term
open Sign
(*i*)

(* The type of mappings for existential variables.
   The keys are section paths and the associated information is a record
   containing the type of the evar ([concl]), the signature under which 
   it was introduced ([hyps]), its definition ([body]) and any other 
   possible information if necessary ([info]).
*)

type evar_body =
  | EVAR_EMPTY 
  | EVAR_DEFINED of constr

type 'a evar_info = {
  evar_concl : typed_type;
  evar_hyps  : typed_type signature;
  evar_body  : evar_body;
  evar_info  : 'a option }

type 'a evar_map

val dom    : 'a evar_map -> section_path list
val map    : 'a evar_map -> section_path -> 'a evar_info
val rmv    : 'a evar_map -> section_path -> 'a evar_map
val remap  : 'a evar_map -> section_path -> 'a evar_info -> 'a evar_map
val in_dom : 'a evar_map -> section_path -> bool
val toList : 'a evar_map -> (section_path * 'a evar_info) list

val mt_evd : 'a evar_map
val add_with_info : 'a evar_map -> section_path -> 'a evar_info -> 'a evar_map
val add_noinfo : 
  'a evar_map -> section_path -> typed_type signature -> typed_type 
    -> 'a evar_map

val define : 'a evar_map -> section_path -> constr -> 'a evar_map

val non_instantiated : 'a evar_map -> (section_path * 'a evar_info) list
val is_evar : 'a evar_map -> section_path -> bool

val is_defined : 'a evar_map -> section_path -> bool

