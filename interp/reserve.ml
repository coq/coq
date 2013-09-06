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
open Notation_ops
open Globnames

type key =
  | RefKey of global_reference
  | Oth

(** TODO: share code from Notation *)

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> RefOrdered.compare gr1 gr2
| RefKey _, Oth -> -1
| Oth, RefKey _ -> 1
| Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

module ReservedOrd =
struct
  type t = notation_constr * Id.t
  let compare = Pervasives.compare (* FIXME *)
end

module ReservedSet = Set.Make(ReservedOrd)

let keymap_add key data map =
  let old = try KeyMap.find key map with Not_found -> ReservedSet.empty in
  KeyMap.add key (ReservedSet.add data old) map

let reserve_table = Summary.ref Id.Map.empty ~name:"reserved-type"
let reserve_revtable = Summary.ref KeyMap.empty ~name:"reserved-type-rev"

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | NList (_,_,NApp (NRef ref,args),_,_)
  | NBinderList (_,_,NApp (NRef ref,args),_) -> RefKey (canonical_gr ref), Some (List.length args)
  | NRef ref -> RefKey(canonical_gr ref), None
  | _ -> Oth, None

let cache_reserved_type (_,(id,t)) =
  let key = fst (notation_constr_key t) in
  reserve_table := Id.Map.add id t !reserve_table;
  reserve_revtable := keymap_add key (t,id) !reserve_revtable

let in_reserved : Id.t * notation_constr -> obj =
  declare_object {(default_object "RESERVED-TYPE") with
    cache_function = cache_reserved_type }

let declare_reserved_type_binding (loc,id) t =
  if not (Id.equal id (root_of_id id)) then
    user_err_loc(loc,"declare_reserved_type",
    (pr_id id ++ str
      " is not reservable: it must have no trailing digits, quote, or _"));
  begin try
    let _ = Id.Map.find id !reserve_table in
    user_err_loc(loc,"declare_reserved_type",
    (pr_id id++str" is already bound to a type"))
  with Not_found -> () end;
  add_anonymous_leaf (in_reserved (id,t))

let declare_reserved_type idl t =
  List.iter (fun id -> declare_reserved_type_binding id t) (List.rev idl)

let find_reserved_type id = Id.Map.find (root_of_id id) !reserve_table

let constr_key c =
  try RefKey (canonical_gr (global_of_constr (fst (Term.decompose_app c))))
  with Not_found -> Oth

let revert_reserved_type t =
  try
    let reserved = KeyMap.find (constr_key t) !reserve_revtable in
    let t = Detyping.detype false [] [] t in
    (* pedrot: if [Notation_ops.match_notation_constr] may raise [Failure _]
        then I've introduced a bug... *)
    let filter (pat, id) =
      try
        let _ = match_notation_constr false t ([], pat) in
        true
      with No_match -> false
    in
    let reserved = ReservedSet.filter filter reserved in
    let (_, id) = ReservedSet.choose reserved in
    Name id
  with Not_found | Failure _ -> Anonymous

let _ = Namegen.set_reserved_typed_name revert_reserved_type

open Glob_term

let anonymize_if_reserved na t = match na with
  | Name id as na ->
      (try
	if not !Flags.raw_print &&
	   (try
            let ntn = notation_constr_of_glob_constr Id.Map.empty Id.Map.empty t in
            Pervasives.(=) ntn (find_reserved_type id) (** FIXME *)
            with UserError _ -> false)
	then GHole (Loc.ghost,Evar_kinds.BinderType na,None)
	else t
      with Not_found -> t)
  | Anonymous -> t
