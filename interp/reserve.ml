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
open Libnames

type key =
  | RefKey of global_reference
  | Oth

let reserve_table = ref Idmap.empty
let reserve_revtable = ref Gmapl.empty

let aconstr_key = function (* Rem: AApp(ARef ref,[]) stands for @ref *)
  | AApp (ARef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | AList (_,_,AApp (ARef ref,args),_,_)
  | ABinderList (_,_,AApp (ARef ref,args),_) -> RefKey (canonical_gr ref), Some (List.length args)
  | ARef ref -> RefKey(canonical_gr ref), None
  | _ -> Oth, None

let cache_reserved_type (_,(id,t)) =
  let key = fst (aconstr_key t) in
  reserve_table := Idmap.add id t !reserve_table;
  reserve_revtable := Gmapl.add key (t,id) !reserve_revtable

let in_reserved =
  declare_object {(default_object "RESERVED-TYPE") with
    cache_function = cache_reserved_type }

let freeze_reserved () = (!reserve_table,!reserve_revtable)
let unfreeze_reserved (r,rr) = reserve_table := r; reserve_revtable := rr
let init_reserved () =
  reserve_table := Idmap.empty; reserve_revtable := Gmapl.empty

let _ =
  Summary.declare_summary "reserved-type"
    { Summary.freeze_function = freeze_reserved;
      Summary.unfreeze_function = unfreeze_reserved;
      Summary.init_function = init_reserved }

let declare_reserved_type_binding (loc,id) t =
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

let declare_reserved_type idl t =
  List.iter (fun id -> declare_reserved_type_binding id t) (List.rev idl)

let find_reserved_type id = Idmap.find (root_of_id id) !reserve_table

let constr_key c =
  try RefKey (canonical_gr (global_of_constr (fst (Term.decompose_app c))))
  with Not_found -> Oth

let revert_reserved_type t =
  try
    let l = Gmapl.find (constr_key t) !reserve_revtable in
    let t = Detyping.detype false [] [] t in
    list_try_find
      (fun (pat,id) ->
	try let _ = match_aconstr false t ([],pat) in Name id
	with No_match -> failwith "") l
  with Not_found | Failure _ -> Anonymous

let _ = Namegen.set_reserved_typed_name revert_reserved_type

open Glob_term

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try
	if not !Flags.raw_print &
	   aconstr_of_glob_constr [] [] t = find_reserved_type id
	then GHole (dummy_loc,Evd.BinderType na)
	else t
      with Not_found -> t)
  | Anonymous -> t
