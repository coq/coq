(* Reserved names *)

open Util
open Names
open Nameops
open Summary
open Libobject
open Lib

let reserve_table = ref Idmap.empty

let cache_reserved_type (_,(id,t)) =
  reserve_table := Idmap.add id t !reserve_table

let (in_reserved, _) =
  declare_object {(default_object "RESERVED-TYPE") with 
    cache_function = cache_reserved_type }

let _ = 
  Summary.declare_summary "reserved-type"
    { Summary.freeze_function = (fun () -> !reserve_table);
      Summary.unfreeze_function = (fun r -> reserve_table := r);
      Summary.init_function = (fun () -> reserve_table := Idmap.empty);
      Summary.survive_section = false }

let declare_reserved_type id t = 
  if id <> root_of_id id then
    error ((string_of_id id)^
    " is not reservable: it must have no trailing digits, quote, or _");
  begin try
    let _ = Idmap.find id !reserve_table in 
    error ((string_of_id id)^" is already bound to a type")
  with Not_found -> () end;
  add_anonymous_leaf (in_reserved (id,t))

let find_reserved_type id = Idmap.find (root_of_id id) !reserve_table

open Rawterm

let rec unloc = function
  | RVar (_,id) -> RVar (dummy_loc,id)
  | RApp (_,g,args) -> RApp (dummy_loc,unloc g, List.map unloc args)
  | RLambda (_,na,ty,c) -> RLambda (dummy_loc,na,unloc ty,unloc c)
  | RProd (_,na,ty,c) -> RProd (dummy_loc,na,unloc ty,unloc c)
  | RLetIn (_,na,b,c) -> RLetIn (dummy_loc,na,unloc b,unloc c)
  | RCases (_,(tyopt,rtntypopt),tml,pl) ->
      RCases (dummy_loc,
        (option_app unloc tyopt,ref (option_app unloc !rtntypopt)),
	List.map (fun (tm,x) -> (unloc tm,x)) tml,
        List.map (fun (_,idl,p,c) -> (dummy_loc,idl,p,unloc c)) pl)
  | ROrderedCase (_,b,tyopt,tm,bv,x) ->
      ROrderedCase 
      (dummy_loc,b,option_app unloc tyopt,unloc tm, Array.map unloc bv,x)
  | RRec (_,fk,idl,tyl,bv) ->
      RRec (dummy_loc,fk,idl,Array.map unloc tyl,Array.map unloc bv)
  | RCast (_,c,t) -> RCast (dummy_loc,unloc c,unloc t)
  | RSort (_,x) -> RSort (dummy_loc,x)
  | RHole (_,x)  -> RHole (dummy_loc,x)
  | RRef (_,x) -> RRef (dummy_loc,x)
  | REvar (_,x) -> REvar (dummy_loc,x)
  | RPatVar (_,x) -> RPatVar (dummy_loc,x)
  | RDynamic (_,x) -> RDynamic (dummy_loc,x)

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try 
	if unloc t = find_reserved_type id
	then RHole (dummy_loc,BinderType na)
	else t
      with Not_found -> t)
  | Anonymous -> t
