open Globnames
open Term
open Libobject


type key = 
  | KGlob of global_reference
  | KLam 
  | KLet
  | KProd
  | KSort
  | KEvar
  | KCase 
  | KFix 
  | KCoFix
  | KRel 
  | KMeta

module KeyOrdered = struct
  type t = key

  let hash gr =
    match gr with
    | KGlob gr -> 10 + RefOrdered.hash gr
    | KLam -> 0
    | KLet -> 1
    | KProd -> 2
    | KSort -> 3
    | KEvar -> 4
    | KCase -> 5
    | KFix -> 6
    | KCoFix -> 7
    | KRel -> 8
    | KMeta -> 9

  let compare gr1 gr2 =
    match gr1, gr2 with
    | KGlob gr1, KGlob gr2 -> RefOrdered.compare gr1 gr2
    | _, KGlob _ -> -1
    | KGlob _, _ -> 1
    | k, k' -> Int.compare (hash k) (hash k')
    
  let equal k1 k2 =
    match k1, k2 with
    | KGlob gr1, KGlob gr2 -> RefOrdered.equal gr1 gr2
    | _, KGlob _ -> false
    | KGlob _, _ -> false
    | k, k' -> k == k'
end

module Keymap = HMap.Make(KeyOrdered)
module Keyset = Keymap.Set

(* Union-find structure for references to be considered equivalent *)

module KeyUF = Unionfind.Make(Keyset)(Keymap)

let keys = (* Summary.ref ( *)KeyUF.create ()(* ) ~name:"Keys_decl" *)

let add_keys k v = KeyUF.union k v keys

let equiv_keys k k' =
  k == k' || KeyUF.find k keys == KeyUF.find k' keys

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
  | KGlob (VarRef _) -> None
  | KGlob g -> Some (KGlob (pop_global_reference g))
  | x -> Some x

let discharge_keys (_,(k,k')) =
  match discharge_key k, discharge_key k' with 
  | Some x, Some y -> Some (x, y)
  | _ -> None

let rebuild_keys (ref,ref') = (ref, ref')

type key_obj = key * key

let inKeys : key_obj -> obj =
  declare_object {(default_object "KEYS") with
    cache_function = cache_keys;
    load_function = load_keys;
    subst_function = subst_keys;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_keys;
    rebuild_function = rebuild_keys }

let declare_keys ref ref' =
  Lib.add_anonymous_leaf (inKeys (ref,ref'))

let rec constr_key c =
  let open Globnames in 
  match kind_of_term c with
  | Const (c, _) -> KGlob (ConstRef c)
  | Ind (i, u) -> KGlob (IndRef i)
  | Construct (c,u) -> KGlob (ConstructRef c)
  | Var id -> KGlob (VarRef id)
  | App (f, _) -> constr_key f
  | Proj (p, _) -> KGlob (ConstRef p)
  | Cast (p, _, _) -> constr_key p
  | Lambda _ -> KLam 
  | Prod _ -> KProd
  | Case _ -> KCase
  | Fix _ -> KFix
  | CoFix _ -> KCoFix
  | Rel _ -> KRel
  | Meta _ -> KMeta
  | Evar _ -> KEvar
  | Sort _ -> KSort 
  | LetIn _ -> KLet
