(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Reserved names *)

open Util
open Pp
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
      Summary.init_function = (fun () -> reserve_table := Idmap.empty) }

let declare_reserved_type (loc,id) t = 
  if id <> root_of_id id then
    user_err_loc(loc,"declare_reserved_type",
    (pr_id id ++ str
      " is not reservable: it must have no trailing digits, quote, or _"));
  begin try
    let _ = Idmap.find id !reserve_table in 
    user_err_loc(loc,"declare_reserved_type",
    (pr_id id++str" is already bound to a type"))
  with Not_found -> () end;
  add_anonymous_leaf (in_reserved (id,t))

let find_reserved_type id = Idmap.find (root_of_id id) !reserve_table

open Rawterm

let rec unloc = function
  | RVar (_,id) -> RVar (dummy_loc,id)
  | RApp (_,g,args) -> RApp (dummy_loc,unloc g, List.map unloc args)
  | RLambda (_,na,bk,ty,c) -> RLambda (dummy_loc,na,bk,unloc ty,unloc c)
  | RProd (_,na,bk,ty,c) -> RProd (dummy_loc,na,bk,unloc ty,unloc c)
  | RLetIn (_,na,b,c) -> RLetIn (dummy_loc,na,unloc b,unloc c)
  | RCases (_,sty,rtntypopt,tml,pl) ->
      RCases (dummy_loc,sty,
        (Option.map unloc rtntypopt),
	List.map (fun (tm,x) -> (unloc tm,x)) tml,
        List.map (fun (_,idl,p,c) -> (dummy_loc,idl,p,unloc c)) pl)
  | RLetTuple (_,nal,(na,po),b,c) ->
      RLetTuple (dummy_loc,nal,(na,Option.map unloc po),unloc b,unloc c)
  | RIf (_,c,(na,po),b1,b2) ->
      RIf (dummy_loc,unloc c,(na,Option.map unloc po),unloc b1,unloc b2)
  | RRec (_,fk,idl,bl,tyl,bv) ->
      RRec (dummy_loc,fk,idl,
            Array.map (List.map 
              (fun (na,k,obd,ty) -> (na,k,Option.map unloc obd, unloc ty)))
              bl,
            Array.map unloc tyl,
            Array.map unloc bv)
  | RCast (_,c, CastConv (k,t)) -> RCast (dummy_loc,unloc c, CastConv (k,unloc t))
  | RCast (_,c, CastCoerce) -> RCast (dummy_loc,unloc c, CastCoerce)
  | RSort (_,x) -> RSort (dummy_loc,x)
  | RHole (_,x)  -> RHole (dummy_loc,x)
  | RRef (_,x) -> RRef (dummy_loc,x)
  | REvar (_,x,l) -> REvar (dummy_loc,x,l)
  | RPatVar (_,x) -> RPatVar (dummy_loc,x)
  | RDynamic (_,x) -> RDynamic (dummy_loc,x)

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try 
	if not !Flags.raw_print & unloc t = find_reserved_type id
	then RHole (dummy_loc,Evd.BinderType na)
	else t
      with Not_found -> t)
  | Anonymous -> t
