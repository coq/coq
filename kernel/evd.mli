
(* $Id$ *)

open Names
open Term
open Sign

(* The type of mappings for existential variables *)

type evar_body =
  | EVAR_EMPTY 
  | EVAR_DEFINED of constr

type 'a evar_info = {
  concl : constr;            (* the type of the evar ...                 *)
  hyps  : context;           (* ... under a certain signature            *)
  body  : evar_body;         (* its definition                           *) 
  info  : 'a option          (* any other possible information necessary *)
}         

type 'a evar_map

val dom    : 'c evar_map -> section_path list
val map    : 'c evar_map -> section_path -> 'c evar_info
val rmv    : 'c evar_map -> section_path -> 'c evar_map
val remap  : 'c evar_map -> section_path -> 'c evar_info -> 'c evar_map
val in_dom : 'c evar_map -> section_path -> bool
val toList : 'c evar_map -> (section_path * 'c evar_info) list

val mt_evd : 'c evar_map
val add_with_info : 'a evar_map -> section_path -> 'a evar_info -> 'a evar_map
val add_noinfo : 'a evar_map -> section_path -> context -> 
                 constr -> 'a evar_map
val define : 'a evar_map -> section_path -> constr -> 'a evar_map

val non_instantiated : 'a evar_map -> (section_path * 'a evar_info) list
val is_evar : 'a evar_map -> section_path -> bool
