(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Reserved names *)

open CErrors
open Util
open Pp
open Names
open Nameops
open Notation_term
open Notation_ops

type key =
  | RefKey of GlobRef.t
  | Oth

(** TODO: share code from Notation *)

let canonize_key env k = match k with
| Oth -> Oth
| RefKey gr ->
  let gr' = Environ.QGlobRef.canonize env gr in
  if gr' == gr then k else RefKey gr'

let mkRefKey env gr =
  RefKey (Environ.QGlobRef.canonize env gr)

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> GlobRef.UserOrd.compare gr1 gr2
| RefKey _, Oth -> -1
| Oth, RefKey _ -> 1
| Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

module ReservedSet :
sig
  type t
  val empty : t
  val add : (Id.t * notation_constr) -> t -> t
  val find : (Id.t -> notation_constr -> bool) -> t -> Id.t * notation_constr
end =
struct
  type t = (Id.t * notation_constr) list

  let empty = []

  let rec mem id c = function
  | [] -> false
  | (id', c') :: l ->
    if c == c' && Id.equal id id' then true else mem id c l

  let add p l =
    let (id, c) = p in
    if mem id c l then l else p :: l

  let rec find f = function
  | [] -> raise Not_found
  | (id, c) as p :: l -> if f id c then p else find f l
end


let keymap_add env key data map =
  let key = canonize_key env key in
  let old = try KeyMap.find key map with Not_found -> ReservedSet.empty in
  KeyMap.add key (ReservedSet.add data old) map

let reserve_table = Summary.ref Id.Map.empty ~name:"reserved-type"
let reserve_revtable = Summary.ref KeyMap.empty ~name:"reserved-type-rev"

let notation_constr_key env = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef (ref,_),args) -> mkRefKey env ref, Some (List.length args)
  | NList (_,_,NApp (NRef (ref,_),args),_,_)
  | NBinderList (_,_,NApp (NRef (ref,_),args),_,_) -> mkRefKey env ref, Some (List.length args)
  | NRef (ref,_) -> mkRefKey env ref, None
  | _ -> Oth, None

let add_reserved_type env (id,t) =
  let key = fst (notation_constr_key env t) in
  reserve_table := Id.Map.add id t !reserve_table;
  reserve_revtable := keymap_add env key (id, t) !reserve_revtable

let declare_reserved_type_binding env {CAst.loc;v=id} t =
  if not (Id.equal id (root_of_id id)) then
    user_err ?loc
      ((Id.print id ++ str
      " is not reservable: it must have no trailing digits, quote, or _."));
  begin try
    let _ = Id.Map.find id !reserve_table in
    user_err ?loc
    ((Id.print id ++ str " is already bound to a type."))
  with Not_found -> () end;
  add_reserved_type env (id,t)

let declare_reserved_type idl t =
  let env = Global.env () in
  List.iter (fun id -> declare_reserved_type_binding env id t) (List.rev idl)

let find_reserved_type id = Id.Map.find (root_of_id id) !reserve_table

let constr_key env c =
  try mkRefKey env (fst @@ Constr.destRef (fst (Constr.decompose_app c)))
  with Constr.DestKO -> Oth

let revert_reserved_type t =
  try
    let env = Global.env () in
    let t = EConstr.Unsafe.to_constr t in
    let reserved = KeyMap.find (constr_key env t) !reserve_revtable in
    let t = EConstr.of_constr t in
    let evd = Evd.from_env env in
    let t = Detyping.detype Detyping.Now env evd t in
    (* pedrot: if [Notation_ops.match_notation_constr] may raise [Failure _]
        then I've introduced a bug... *)
    let filter _ pat =
      try
        let _ = match_notation_constr ~print_univ:false t ~vars:Id.Set.empty ([], pat) in
        true
      with No_match -> false
    in
    let (id, _) = ReservedSet.find filter reserved in
    Name id
  with Not_found | Failure _ -> Anonymous

let _ = Namegen.set_reserved_typed_name revert_reserved_type
