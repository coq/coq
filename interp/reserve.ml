(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Reserved names *)

open Errors
open Util
open Pp
open Names
open Nameops
open Libobject
open Lib
open Notation_term
open Globnames

type key =
  | RefKey of global_reference
  | Oth

let reserve_table = ref Idmap.empty
let reserve_revtable = ref Gmapl.empty

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | NList (_,_,NApp (NRef ref,args),_,_)
  | NBinderList (_,_,NApp (NRef ref,args),_) -> RefKey (canonical_gr ref), Some (List.length args)
  | NRef ref -> RefKey(canonical_gr ref), None
  | _ -> Oth, None

let cache_reserved_type (_,(id,t)) =
  let key = fst (notation_constr_key t) in
  reserve_table := Idmap.add id t !reserve_table;
  reserve_revtable := Gmapl.add key (t,id) !reserve_revtable

let in_reserved : identifier * notation_constr -> obj =
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
  if not (id_eq id (root_of_id id)) then
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
    (* pedrot: if [Notation_ops.match_notation_constr] may raise [Failure _]
        then I've introduced a bug... *)
    let find (pat, id) =
      try let _ = Notation_ops.match_notation_constr false t ([], pat) in true
      with Notation_ops.No_match -> false
    in
    let (_, id) = List.find find l in
    Name id
  with Not_found | Failure _ -> Anonymous

let _ = Namegen.set_reserved_typed_name revert_reserved_type

open Glob_term

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try
	if not !Flags.raw_print &&
	   (try
            let ntn = Notation_ops.notation_constr_of_glob_constr [] [] t in
            Pervasives.(=) ntn (find_reserved_type id) (** FIXME *)
            with UserError _ -> false)
	then GHole (Loc.ghost,Evar_kinds.BinderType na)
	else t
      with Not_found -> t)
  | Anonymous -> t
