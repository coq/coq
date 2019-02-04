(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Keys for unification and indexing *)

open Names
open Constr
open Libobject
open Globnames

type key =
  | KGlob of GlobRef.t
  | KLam
  | KLet
  | KProd
  | KSort
  | KCase
  | KFix
  | KCoFix
  | KRel
  | KInt

module KeyOrdered = struct
  type t = key

  let hash gr =
    match gr with
    | KGlob gr -> 9 + GlobRef.Ordered.hash gr
    | KLam -> 0
    | KLet -> 1
    | KProd -> 2
    | KSort -> 3
    | KCase -> 4
    | KFix -> 5
    | KCoFix -> 6
    | KRel -> 7
    | KInt -> 8

  let compare gr1 gr2 =
    match gr1, gr2 with
    | KGlob gr1, KGlob gr2 -> GlobRef.Ordered.compare gr1 gr2
    | _, KGlob _ -> -1
    | KGlob _, _ -> 1
    | k, k' -> Int.compare (hash k) (hash k')
    
  let equal k1 k2 =
    match k1, k2 with
    | KGlob gr1, KGlob gr2 -> GlobRef.Ordered.equal gr1 gr2
    | _, KGlob _ -> false
    | KGlob _, _ -> false
    | k, k' -> k == k'
end

module Keymap = HMap.Make(KeyOrdered)
module Keyset = Keymap.Set

(* Mapping structure for references to be considered equivalent *)

let keys = Summary.ref Keymap.empty ~name:"Keys_decl"

let add_kv k v m =
  try Keymap.modify k (fun k' vs -> Keyset.add v vs) m
  with Not_found -> Keymap.add k (Keyset.singleton v) m

let add_keys k v = 
  keys := add_kv k v (add_kv v k !keys)

let equiv_keys k k' =
  k == k' || KeyOrdered.equal k k' ||
    try Keyset.mem k' (Keymap.find k !keys)
    with Not_found -> false

(** Registration of keys as an object *)

let load_keys _ (_,(ref,ref')) =
  add_keys ref ref'

let cache_keys o =
  load_keys 1 o

let subst_key subst k = 
  match k with
  | KGlob gr -> KGlob (subst_global_reference subst gr)
  | _ -> k

let subst_keys (subst,(k,k')) =
  (subst_key subst k, subst_key subst k')

let discharge_key = function
  | KGlob (VarRef _ as g) when Lib.is_in_section g -> None
  | x -> Some x

let discharge_keys (_,(k,k')) =
  match discharge_key k, discharge_key k' with 
  | Some x, Some y -> Some (x, y)
  | _ -> None

type key_obj = key * key

let inKeys : key_obj -> obj =
  declare_object @@ superglobal_object "KEYS"
    ~cache:cache_keys
    ~subst:(Some subst_keys)
    ~discharge:discharge_keys

let declare_equiv_keys ref ref' =
  Lib.add_anonymous_leaf (inKeys (ref,ref'))

let constr_key kind c =
  let open Globnames in 
  try 
    let rec aux k = 
      match kind k with
      | Const (c, _) -> KGlob (ConstRef c)
      | Ind (i, u) -> KGlob (IndRef i)
      | Construct (c,u) -> KGlob (ConstructRef c)
      | Var id -> KGlob (VarRef id)
      | App (f, _) -> aux f
      | Proj (p, _) -> KGlob (ConstRef (Projection.constant p))
      | Cast (p, _, _) -> aux p
      | Lambda _ -> KLam 
      | Prod _ -> KProd
      | Case _ -> KCase
      | Fix _ -> KFix
      | CoFix _ -> KCoFix
      | Rel _ -> KRel
      | Meta _ -> raise Not_found
      | Evar _ -> raise Not_found
      | Sort _ -> KSort 
      | LetIn _ -> KLet
      | Int _ -> KInt
    in Some (aux c)
  with Not_found -> None

open Pp

let pr_key pr_global = function
  | KGlob gr -> pr_global gr
  | KLam -> str"Lambda"
  | KLet -> str"Let"
  | KProd -> str"Product"
  | KSort -> str"Sort"
  | KCase -> str"Case"
  | KFix -> str"Fix"
  | KCoFix -> str"CoFix"
  | KRel -> str"Rel"
  | KInt -> str"Int"

let pr_keyset pr_global v = 
  prlist_with_sep spc (pr_key pr_global) (Keyset.elements v)

let pr_mapping pr_global k v = 
  pr_key pr_global k ++ str" <-> " ++ pr_keyset pr_global v

let pr_keys pr_global =
  Keymap.fold (fun k v acc -> pr_mapping pr_global k v ++ fnl () ++ acc) !keys (mt())
