(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Reserved names *)

open Util
open Pp
open Names
open Nameops
open Summary
open Libobject
open Lib
open Topconstr

let reserve_table = ref Idmap.empty

let cache_reserved_type (_,(id,t)) =
  reserve_table := Idmap.add id t !reserve_table

let in_reserved =
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
  | GVar (_,id) -> GVar (dummy_loc,id)
  | GApp (_,g,args) -> GApp (dummy_loc,unloc g, List.map unloc args)
  | GLambda (_,na,bk,ty,c) -> GLambda (dummy_loc,na,bk,unloc ty,unloc c)
  | GProd (_,na,bk,ty,c) -> GProd (dummy_loc,na,bk,unloc ty,unloc c)
  | GLetIn (_,na,b,c) -> GLetIn (dummy_loc,na,unloc b,unloc c)
  | GCases (_,sty,rtntypopt,tml,pl) ->
      GCases (dummy_loc,sty,
        (Option.map unloc rtntypopt),
	List.map (fun (tm,x) -> (unloc tm,x)) tml,
        List.map (fun (_,idl,p,c) -> (dummy_loc,idl,p,unloc c)) pl)
  | GLetTuple (_,nal,(na,po),b,c) ->
      GLetTuple (dummy_loc,nal,(na,Option.map unloc po),unloc b,unloc c)
  | GIf (_,c,(na,po),b1,b2) ->
      GIf (dummy_loc,unloc c,(na,Option.map unloc po),unloc b1,unloc b2)
  | GRec (_,fk,idl,bl,tyl,bv) ->
      GRec (dummy_loc,fk,idl,
            Array.map (List.map
              (fun (na,k,obd,ty) -> (na,k,Option.map unloc obd, unloc ty)))
              bl,
            Array.map unloc tyl,
            Array.map unloc bv)
  | GCast (_,c, CastConv (k,t)) -> GCast (dummy_loc,unloc c, CastConv (k,unloc t))
  | GCast (_,c, CastCoerce) -> GCast (dummy_loc,unloc c, CastCoerce)
  | GSort (_,x) -> GSort (dummy_loc,x)
  | GHole (_,x)  -> GHole (dummy_loc,x)
  | GRef (_,x) -> GRef (dummy_loc,x)
  | GEvar (_,x,l) -> GEvar (dummy_loc,x,l)
  | GPatVar (_,x) -> GPatVar (dummy_loc,x)
  | GDynamic (_,x) -> GDynamic (dummy_loc,x)

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try
	if not !Flags.raw_print &
	   aconstr_of_glob_constr [] [] t = find_reserved_type id
	then GHole (dummy_loc,Evd.BinderType na)
	else t
      with Not_found -> t)
  | Anonymous -> t
