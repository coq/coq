
(* $Id$ *)

open Names
open Sign
open Univ
open Term

type 'a unsafe_env = {
  context : environment;
  inf_context : environment option;
  sigma : 'a evar_map;
  metamap : (int * constr) list;
  constraints : universes
}
  
(* First character of a constr *)

let lowercase_first_char id = String.lowercase (first_char id)

let rec hdchar = function
  | DOP2(Prod,_,DLAM(_,c))     -> hdchar c
  | DOP2(Cast,c,_)             -> hdchar c
  | DOPN(AppL,cl)              -> hdchar (array_hd cl)
  | DOP2(Lambda,_,DLAM(_,c))   -> hdchar c
  | DOPN(Const _,_) as x ->
      let c = lowercase_first_char (basename (path_of_const x)) in
      if c = "?" then "y" else c
  | DOPN(Abst _,_) as x ->
      lowercase_first_char (basename (path_of_abst x))
  | DOPN(MutInd (sp,i) as x,_) ->
      if i=0 then 
	lowercase_first_char (basename sp)
      else 
	let na = id_of_global x in lowercase_first_char na
  | DOPN(MutConstruct(sp,i) as x,_) ->
      let na = id_of_global x  in String.lowercase(List.hd(explode_id na))
  | VAR id  -> lowercase_first_char id
  | DOP0(Sort s) -> sort_hdchar s
  | _ -> "y"

let id_of_name_using_hdchar a = function
  | Anonymous -> id_of_string (hdchar a) 
  | Name id   -> id

let named_hd a = function
  | Anonymous -> Name (id_of_string (hdchar a)) 
  | x         -> x
