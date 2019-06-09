(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open CAst
open CErrors
open Names
open Libnames
open Locus
open Tac2env
open Tac2print
open Tac2expr

(** Hardwired types and constants *)

let coq_type n = KerName.make Tac2env.coq_prefix (Label.make n)

let t_int = coq_type "int"
let t_string = coq_type "string"
let t_constr = coq_type "constr"

(** Union find *)

module UF :
sig
type elt
type 'a t
val equal : elt -> elt -> bool
val create : unit -> 'a t
val fresh : 'a t -> elt
val find : elt -> 'a t -> (elt * 'a option)
val union : elt -> elt -> 'a t -> unit
val set : elt -> 'a -> 'a t -> unit
module Map :
sig
  type key = elt
  type +'a t
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val exists : (key -> 'a -> bool) -> 'a t -> bool
end
end
=
struct
type elt = int
let equal = Int.equal
module Map = Int.Map

type 'a node =
| Canon of int * 'a option
| Equiv of elt

type 'a t = {
  mutable uf_data : 'a node array;
  mutable uf_size : int;
}

let resize p =
  if Int.equal (Array.length p.uf_data) p.uf_size then begin
    let nsize = 2 * p.uf_size + 1 in
    let v = Array.make nsize (Equiv 0) in
    Array.blit p.uf_data 0 v 0 (Array.length p.uf_data);
    p.uf_data <- v;
  end

let create () = { uf_data = [||]; uf_size = 0 }

let fresh p =
  resize p;
  let n = p.uf_size in
  p.uf_data.(n) <- (Canon (1, None));
  p.uf_size <- n + 1;
  n

let rec lookup n p =
  let node = Array.get p.uf_data n in
  match node with
  | Canon (size, v) -> n, size, v
  | Equiv y ->
    let ((z, _, _) as res) = lookup y p in
    if not (Int.equal z y) then Array.set p.uf_data n (Equiv z);
    res

let find n p =
  let (x, _, v) = lookup n p in (x, v)

let union x y p =
  let ((x, size1, _) as xcan) = lookup x p in
  let ((y, size2, _) as ycan) = lookup y p in
  let xcan, ycan = if size1 < size2 then xcan, ycan else ycan, xcan in
  let x, _, xnode = xcan in
  let y, _, ynode = ycan in
  assert (Option.is_empty xnode);
  assert (Option.is_empty ynode);
  p.uf_data.(x) <- Equiv y;
  p.uf_data.(y) <- Canon (size1 + size2, None)

let set x v p =
  let (x, s, v') = lookup x p in
  assert (Option.is_empty v');
  p.uf_data.(x) <- Canon (s, Some v)

end

type mix_var =
| GVar of UF.elt
| LVar of int

type mix_type_scheme = int * mix_var glb_typexpr

type environment = {
  env_var : mix_type_scheme Id.Map.t;
  (** Type schemes of bound variables *)
  env_cst : UF.elt glb_typexpr UF.t;
  (** Unification state *)
  env_als : UF.elt Id.Map.t ref;
  (** Map user-facing type variables to unification variables *)
  env_opn : bool;
  (** Accept unbound type variables *)
  env_rec : (KerName.t * int) Id.Map.t;
  (** Recursive type definitions *)
  env_str : bool;
  (** True iff in strict mode *)
}

let empty_env () = {
  env_var = Id.Map.empty;
  env_cst = UF.create ();
  env_als = ref Id.Map.empty;
  env_opn = true;
  env_rec = Id.Map.empty;
  env_str = true;
}

let env_name env =
  (* Generate names according to a provided environment *)
  let mk num =
    let base = num mod 26 in
    let rem = num / 26 in
    let name = String.make 1 (Char.chr (97 + base)) in
    let suff = if Int.equal rem 0 then "" else string_of_int rem in
    let name = name ^ suff in
    name
  in
  let fold id elt acc = UF.Map.add elt (Id.to_string id) acc in
  let vars = Id.Map.fold fold env.env_als.contents UF.Map.empty in
  let vars = ref vars in
  let rec fresh n =
    let name = mk n in
    if UF.Map.exists (fun _ name' -> String.equal name name') !vars then fresh (succ n)
    else name
  in
  fun n ->
    if UF.Map.mem n !vars then UF.Map.find n !vars
    else
      let ans = fresh 0 in
      let () = vars := UF.Map.add n ans !vars in
      ans

let ltac2_env : environment Genintern.Store.field =
  Genintern.Store.field ()

let drop_ltac2_env store =
  Genintern.Store.remove store ltac2_env

let fresh_id env = UF.fresh env.env_cst

let get_alias {loc;v=id} env =
  try Id.Map.find id env.env_als.contents
  with Not_found ->
    if env.env_opn then
      let n = fresh_id env in
      let () = env.env_als := Id.Map.add id n env.env_als.contents in
      n
    else user_err ?loc (str "Unbound type parameter " ++ Id.print id)

let push_name id t env = match id with
| Anonymous -> env
| Name id -> { env with env_var = Id.Map.add id t env.env_var }

let error_nargs_mismatch ?loc kn nargs nfound =
  let cstr = Tac2env.shortest_qualid_of_constructor kn in
  user_err ?loc (str "Constructor " ++ pr_qualid cstr ++ str " expects " ++
    int nargs ++ str " arguments, but is applied to " ++ int nfound ++
    str " arguments")

let error_nparams_mismatch ?loc nargs nfound =
  user_err ?loc (str "Type expects " ++ int nargs ++
    str " arguments, but is applied to " ++ int nfound ++
    str " arguments")

let rec subst_type subst (t : 'a glb_typexpr) = match t with
| GTypVar id -> subst id
| GTypArrow (t1, t2) -> GTypArrow (subst_type subst t1, subst_type subst t2)
| GTypRef (qid, args) ->
  GTypRef (qid, List.map (fun t -> subst_type subst t) args)

let rec intern_type env ({loc;v=t} : raw_typexpr) : UF.elt glb_typexpr = match t with
| CTypVar (Name id) -> GTypVar (get_alias (CAst.make ?loc id) env)
| CTypVar Anonymous -> GTypVar (fresh_id env)
| CTypRef (rel, args) ->
  let (kn, nparams) = match rel with
  | RelId qid ->
    let id = qualid_basename qid in
    if qualid_is_ident qid && Id.Map.mem id env.env_rec then
      let (kn, n) = Id.Map.find id env.env_rec in
      (Other kn, n)
    else
      let kn =
        try Tac2env.locate_type qid
        with Not_found ->
          user_err ?loc (str "Unbound type constructor " ++ pr_qualid qid)
      in
      let (nparams, _) = Tac2env.interp_type kn in
      (Other kn, nparams)
  | AbsKn (Other kn) ->
    let (nparams, _) = Tac2env.interp_type kn in
    (Other kn, nparams)
  | AbsKn (Tuple n) ->
    (Tuple n, n)
  in
  let nargs = List.length args in
  let () =
    if not (Int.equal nparams nargs) then
      let qid = match rel with
      | RelId lid -> lid
      | AbsKn (Other kn) -> shortest_qualid_of_type ?loc kn
      | AbsKn (Tuple _) -> assert false
      in
      user_err ?loc (strbrk "The type constructor " ++ pr_qualid qid ++
        strbrk " expects " ++ int nparams ++ strbrk " argument(s), but is here \
        applied to " ++ int nargs ++ strbrk "argument(s)")
  in
  GTypRef (kn, List.map (fun t -> intern_type env t) args)
| CTypArrow (t1, t2) -> GTypArrow (intern_type env t1, intern_type env t2)

let fresh_type_scheme env (t : type_scheme) : UF.elt glb_typexpr =
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf i = GTypVar subst.(i) in
  subst_type substf t

let fresh_mix_type_scheme env (t : mix_type_scheme) : UF.elt glb_typexpr =
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf = function
  | LVar i -> GTypVar subst.(i)
  | GVar n -> GTypVar n
  in
  subst_type substf t

let fresh_reftype env (kn : KerName.t or_tuple) =
  let n = match kn with
  | Other kn -> fst (Tac2env.interp_type kn)
  | Tuple n -> n
  in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let t = GTypRef (kn, Array.map_to_list (fun i -> GTypVar i) subst) in
  (subst, t)

(** First-order unification algorithm *)
let is_unfoldable kn = match snd (Tac2env.interp_type kn) with
| GTydDef (Some _) -> true
| GTydDef None | GTydAlg _ | GTydRec _ | GTydOpn -> false

let unfold env kn args =
  let (nparams, def) = Tac2env.interp_type kn in
  let def = match def with
  | GTydDef (Some t) -> t
  | _ -> assert false
  in
  let args = Array.of_list args in
  let subst n = args.(n) in
  subst_type subst def

(** View function, allows to ensure head normal forms *)
let rec kind env t = match t with
| GTypVar id ->
  let (id, v) = UF.find id env.env_cst in
  begin match v with
  | None -> GTypVar id
  | Some t -> kind env t
  end
| GTypRef (Other kn, tl) ->
  if is_unfoldable kn then kind env (unfold env kn tl) else t
| GTypArrow _ | GTypRef (Tuple _, _) -> t

(** Normalize unification variables without unfolding type aliases *)
let rec nf env t = match t with
| GTypVar id ->
  let (id, v) = UF.find id env.env_cst in
  begin match v with
  | None -> GTypVar id
  | Some t -> nf env t
  end
| GTypRef (kn, tl) ->
  let tl = List.map (fun t -> nf env t) tl in
  GTypRef (kn, tl)
| GTypArrow (t, u) ->
  let t = nf env t in
  let u = nf env u in
  GTypArrow (t, u)

let pr_glbtype env t =
  let t = nf env t in
  let name = env_name env in
  pr_glbtype name t

exception Occur

let rec occur_check env id t = match kind env t with
| GTypVar id' -> if UF.equal id id' then raise Occur
| GTypArrow (t1, t2) ->
  let () = occur_check env id t1 in
  occur_check env id t2
| GTypRef (kn, tl) ->
  List.iter (fun t -> occur_check env id t) tl

exception CannotUnify of UF.elt glb_typexpr * UF.elt glb_typexpr

let unify_var env id t = match kind env t with
| GTypVar id' ->
  if not (UF.equal id id') then UF.union id id' env.env_cst
| GTypArrow _ | GTypRef _ ->
  try
    let () = occur_check env id t in
    UF.set id t env.env_cst
  with Occur -> raise (CannotUnify (GTypVar id, t))

let eq_or_tuple eq t1 t2 = match t1, t2 with
| Tuple n1, Tuple n2 -> Int.equal n1 n2
| Other o1, Other o2 -> eq o1 o2
| _ -> false

let rec unify0 env t1 t2 = match kind env t1, kind env t2 with
| GTypVar id, t | t, GTypVar id ->
  unify_var env id t
| GTypArrow (t1, u1), GTypArrow (t2, u2) ->
  let () = unify0 env t1 t2 in
  unify0 env u1 u2
| GTypRef (kn1, tl1), GTypRef (kn2, tl2) ->
  if eq_or_tuple KerName.equal kn1 kn2 then
    List.iter2 (fun t1 t2 -> unify0 env t1 t2) tl1 tl2
  else raise (CannotUnify (t1, t2))
| _ -> raise (CannotUnify (t1, t2))

let unify ?loc env t1 t2 =
  try unify0 env t1 t2
  with CannotUnify (u1, u2) ->
    user_err ?loc (str "This expression has type" ++ spc () ++ pr_glbtype env t1 ++
      spc () ++ str "but an expression was expected of type" ++ spc () ++ pr_glbtype env t2)

let unify_arrow ?loc env ft args =
  let ft0 = ft in
  let rec iter ft args is_fun = match kind env ft, args with
  | t, [] -> t
  | GTypArrow (t1, ft), (loc, t2) :: args ->
    let () = unify ?loc env t2 t1 in
    iter ft args true
  | GTypVar id, (_, t) :: args ->
    let ft = GTypVar (fresh_id env) in
    let () = unify ?loc env (GTypVar id) (GTypArrow (t, ft)) in
    iter ft args true
  | GTypRef _, _ :: _ ->
    if is_fun then
      user_err ?loc (str "This function has type" ++ spc () ++ pr_glbtype env ft0 ++
        spc () ++ str "and is applied to too many arguments")
    else
      user_err ?loc (str "This expression has type" ++ spc () ++ pr_glbtype env ft0 ++
        spc () ++ str "and is not a function")
  in
  iter ft args false

(** Term typing *)

let is_pure_constructor kn =
  match snd (Tac2env.interp_type kn) with
  | GTydAlg _ | GTydOpn -> true
  | GTydRec fields ->
    let is_pure (_, mut, _) = not mut in
    List.for_all is_pure fields
  | GTydDef _ -> assert false (** Type definitions have no constructors *)

let rec is_value = function
| GTacAtm (AtmInt _) | GTacVar _ | GTacRef _ | GTacFun _ -> true
| GTacAtm (AtmStr _) | GTacApp _ | GTacLet _ -> false
| GTacCst (Tuple _, _, el) -> List.for_all is_value el
| GTacCst (_, _, []) -> true
| GTacOpn (_, el) -> List.for_all is_value el
| GTacCst (Other kn, _, el) -> is_pure_constructor kn && List.for_all is_value el
| GTacCse _ | GTacPrj _ | GTacSet _ | GTacExt _ | GTacPrm _
| GTacWth _ -> false

let is_rec_rhs = function
| GTacFun _ -> true
| GTacAtm _ | GTacVar _ | GTacRef _ | GTacApp _ | GTacLet _ | GTacPrj _
| GTacSet _ | GTacExt _ | GTacPrm _ | GTacCst _
| GTacCse _ | GTacOpn _ | GTacWth _ -> false

let rec fv_type f t accu = match t with
| GTypVar id -> f id accu
| GTypArrow (t1, t2) -> fv_type f t1 (fv_type f t2 accu)
| GTypRef (kn, tl) -> List.fold_left (fun accu t -> fv_type f t accu) accu tl

let fv_env env =
  let rec f id accu = match UF.find id env.env_cst with
  | id, None -> UF.Map.add id () accu
  | _, Some t -> fv_type f t accu
  in
  let fold_var id (_, t) accu =
    let fmix id accu = match id with
    | LVar _ -> accu
    | GVar id -> f id accu
    in
    fv_type fmix t accu
  in
  let fv_var = Id.Map.fold fold_var env.env_var UF.Map.empty in
  let fold_als _ id accu = f id accu in
  Id.Map.fold fold_als !(env.env_als) fv_var

let abstract_var env (t : UF.elt glb_typexpr) : mix_type_scheme =
  let fv = fv_env env in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let rec subst id =
    let (id, t) = UF.find id env.env_cst in
    match t with
    | None ->
      if UF.Map.mem id fv then GTypVar (GVar id)
      else
        begin try UF.Map.find id !vars
        with Not_found ->
          let n = !count in
          let var = GTypVar (LVar n) in
          let () = incr count in
          let () = vars := UF.Map.add id var !vars in
          var
        end
    | Some t -> subst_type subst t
  in
  let t = subst_type subst t in
  (!count, t)

let monomorphic (t : UF.elt glb_typexpr) : mix_type_scheme =
  let subst id = GTypVar (GVar id) in
  (0, subst_type subst t)

let warn_not_unit =
  CWarnings.create ~name:"not-unit" ~category:"ltac"
    (fun () -> strbrk "The following expression should have type unit.")

let warn_redundant_clause =
  CWarnings.create ~name:"redundant-clause" ~category:"ltac"
    (fun () -> strbrk "The following clause is redundant.")

let check_elt_unit loc env t =
  let maybe_unit = match kind env t with
  | GTypVar _ -> true
  | GTypArrow _ -> false
  | GTypRef (Tuple 0, []) -> true
  | GTypRef _ -> false
  in
  if not maybe_unit then warn_not_unit ?loc ()

let check_elt_empty loc env t = match kind env t with
| GTypVar _ ->
  user_err ?loc (str "Cannot infer an empty type for this expression")
| GTypArrow _ | GTypRef (Tuple _, _) ->
  user_err ?loc (str "Type" ++ spc () ++ pr_glbtype env t ++ spc () ++ str "is not an empty type")
| GTypRef (Other kn, _) ->
  let def = Tac2env.interp_type kn in
  match def with
  | _, GTydAlg { galg_constructors = [] } -> kn
  | _ ->
    user_err ?loc (str "Type" ++ spc () ++ pr_glbtype env t ++ spc () ++ str "is not an empty type")

let check_unit ?loc t =
  let env = empty_env () in
  (* Should not matter, t should be closed. *)
  let t = fresh_type_scheme env t in
  let maybe_unit = match kind env t with
  | GTypVar _ -> true
  | GTypArrow _ -> false
  | GTypRef (Tuple 0, []) -> true
  | GTypRef _ -> false
  in
  if not maybe_unit then warn_not_unit ?loc ()

let check_redundant_clause = function
| [] -> ()
| (p, _) :: _ -> warn_redundant_clause ?loc:p.loc ()

let get_variable0 mem var = match var with
| RelId qid ->
  let id = qualid_basename qid in
  if qualid_is_ident qid && mem id then ArgVar CAst.(make ?loc:qid.CAst.loc id)
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found ->
        CErrors.user_err ?loc:qid.CAst.loc (str "Unbound value " ++ pr_qualid qid)
    in
    ArgArg kn
| AbsKn kn -> ArgArg kn

let get_variable env var =
  let mem id = Id.Map.mem id env.env_var in
  get_variable0 mem var

let get_constructor env var = match var with
| RelId qid ->
  let c = try Some (Tac2env.locate_constructor qid) with Not_found -> None in
  begin match c with
  | Some knc -> Other knc
  | None ->
    CErrors.user_err ?loc:qid.CAst.loc (str "Unbound constructor " ++ pr_qualid qid)
  end
| AbsKn knc -> knc

let get_projection var = match var with
| RelId qid ->
  let kn = try Tac2env.locate_projection qid with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++ str " is not a projection")
  in
  Tac2env.interp_projection kn
| AbsKn kn ->
  Tac2env.interp_projection kn

let intern_atm env = function
| AtmInt n -> (GTacAtm (AtmInt n), GTypRef (Other t_int, []))
| AtmStr s -> (GTacAtm (AtmStr s), GTypRef (Other t_string, []))

let invalid_pattern ?loc kn kn' =
  let pr t = match t with
  | Other kn' -> str "type " ++  pr_typref kn'
  | Tuple n -> str "tuple of size " ++ int n
  in
  user_err ?loc (str "Invalid pattern, expected a pattern for " ++
    pr kn ++ str ", found a pattern for " ++ pr kn') (** FIXME *)

(** Pattern view *)

type glb_patexpr =
| GPatVar of Name.t
| GPatRef of ltac_constructor or_tuple * glb_patexpr list

let rec intern_patexpr env {loc;v=pat} = match pat with
| CPatVar na -> GPatVar na
| CPatRef (qid, pl) ->
  let kn = get_constructor env qid in
  GPatRef (kn, List.map (fun p -> intern_patexpr env p) pl)
| CPatCnv (pat, ty) ->
  user_err ?loc (str "Pattern not handled yet")

type pattern_kind =
| PKind_empty
| PKind_variant of type_constant or_tuple
| PKind_open of type_constant
| PKind_any

let get_pattern_kind env pl = match pl with
| [] -> PKind_empty
| p :: pl ->
  let rec get_kind (p, _) pl = match intern_patexpr env p with
  | GPatVar _ ->
    begin match pl with
    | [] -> PKind_any
    | p :: pl -> get_kind p pl
    end
  | GPatRef (Other kn, pl) ->
    let data = Tac2env.interp_constructor kn in
    if Option.is_empty data.cdata_indx then PKind_open data.cdata_type
    else PKind_variant (Other data.cdata_type)
  | GPatRef (Tuple _, tp) -> PKind_variant (Tuple (List.length tp))
  in
  get_kind p pl

(** Internalization *)

(** Used to generate a fresh tactic variable for pattern-expansion *)
let fresh_var avoid =
  let bad id =
    Id.Set.mem id avoid ||
    (try ignore (locate_ltac (qualid_of_ident id)); true with Not_found -> false)
  in
  Namegen.next_ident_away_from (Id.of_string "p") bad

let add_name accu = function
| Name id -> Id.Set.add id accu
| Anonymous -> accu

let rec ids_of_pattern accu {v=pat} = match pat with
| CPatVar Anonymous -> accu
| CPatVar (Name id) -> Id.Set.add id accu
| CPatRef (_, pl) ->
  List.fold_left ids_of_pattern accu pl
| CPatCnv (pat, _) -> ids_of_pattern accu pat

let loc_of_relid = function
| RelId {loc} -> loc
| AbsKn _ -> None

let extract_pattern_type ({loc;v=p} as pat) = match p with
| CPatCnv (pat, ty) -> pat, Some ty
| CPatVar _ | CPatRef _ -> pat, None

(** Expand pattern: [p => t] becomes [x => match x with p => t end] *)
let expand_pattern avoid bnd =
  let fold (avoid, bnd) (pat, t) =
    let na, expand = match pat.v with
    | CPatVar na ->
      (* Don't expand variable patterns *)
      na, None
    | _ ->
      let id = fresh_var avoid in
      let qid = RelId (qualid_of_ident ?loc:pat.loc id) in
      Name id, Some qid
    in
    let avoid = ids_of_pattern avoid pat in
    let avoid = add_name avoid na in
    (avoid, (na, pat, expand) :: bnd)
  in
  let (_, bnd) = List.fold_left fold (avoid, []) bnd in
  let fold e (na, pat, expand) = match expand with
  | None -> e
  | Some qid ->
    let loc = loc_of_relid qid in
    CAst.make ?loc @@ CTacCse (CAst.make ?loc @@ CTacRef qid, [pat, e])
  in
  let expand e = List.fold_left fold e bnd in
  let nas = List.rev_map (fun (na, _, _) -> na) bnd in
  (nas, expand)

let is_alias env qid = match get_variable env qid with
| ArgArg (TacAlias _) -> true
| ArgVar _ | (ArgArg (TacConstant _)) -> false

let rec intern_rec env {loc;v=e} = match e with
| CTacAtm atm -> intern_atm env atm
| CTacRef qid ->
  begin match get_variable env qid with
  | ArgVar {CAst.v=id} ->
    let sch = Id.Map.find id env.env_var in
    (GTacVar id, fresh_mix_type_scheme env sch)
  | ArgArg (TacConstant kn) ->
    let { Tac2env.gdata_type = sch } =
      try Tac2env.interp_global kn
      with Not_found ->
        CErrors.anomaly (str "Missing hardwired primitive " ++ KerName.print kn)
    in
    (GTacRef kn, fresh_type_scheme env sch)
  | ArgArg (TacAlias kn) ->
    let e =
      try Tac2env.interp_alias kn
      with Not_found ->
        CErrors.anomaly (str "Missing hardwired alias " ++ KerName.print kn)
    in
    intern_rec env e
  end
| CTacCst qid ->
  let kn = get_constructor env qid in
  intern_constructor env loc kn []
| CTacFun (bnd, e) ->
  let bnd = List.map extract_pattern_type bnd in
  let map (_, t) = match t with
  | None -> GTypVar (fresh_id env)
  | Some t -> intern_type env t
  in
  let tl = List.map map bnd in
  let (nas, exp) = expand_pattern (Id.Map.domain env.env_var) bnd in
  let env = List.fold_left2 (fun env na t -> push_name na (monomorphic t) env) env nas tl in
  let (e, t) = intern_rec env (exp e) in
  let t = List.fold_right (fun t accu -> GTypArrow (t, accu)) tl t in
  (GTacFun (nas, e), t)
| CTacApp ({loc;v=CTacCst qid}, args) ->
  let kn = get_constructor env qid in
  intern_constructor env loc kn args
| CTacApp ({v=CTacRef qid}, args) when is_alias env qid ->
  let kn = match get_variable env qid with
  | ArgArg (TacAlias kn) -> kn
  | ArgVar _ | (ArgArg (TacConstant _)) -> assert false
  in
  let e = Tac2env.interp_alias kn in
  let map arg =
    (* Thunk alias arguments *)
    let loc = arg.loc in
    let t_unit = CAst.make ?loc @@ CTypRef (AbsKn (Tuple 0), []) in
    let var = CAst.make ?loc @@ CPatCnv (CAst.make ?loc @@ CPatVar Anonymous, t_unit) in
    CAst.make ?loc @@ CTacFun ([var], arg)
  in
  let args = List.map map args in
  intern_rec env (CAst.make ?loc @@ CTacApp (e, args))
| CTacApp (f, args) ->
  let loc = f.loc in
  let (f, ft) = intern_rec env f in
  let fold arg (args, t) =
    let loc = arg.loc in
    let (arg, argt) = intern_rec env arg in
    (arg :: args, (loc, argt) :: t)
  in
  let (args, t) = List.fold_right fold args ([], []) in
  let ret = unify_arrow ?loc env ft t in
  (GTacApp (f, args), ret)
| CTacLet (is_rec, el, e) ->
  let map (pat, e) =
    let (pat, ty) = extract_pattern_type pat in
    (pat, ty, e)
  in
  let el = List.map map el in
  let fold accu (pat, _, e) =
    let ids = ids_of_pattern Id.Set.empty pat in
    let common = Id.Set.inter ids accu in
    if Id.Set.is_empty common then Id.Set.union ids accu
    else
      let id = Id.Set.choose common in
      user_err ?loc:pat.loc (str "Variable " ++ Id.print id ++ str " is bound several \
        times in this matching")
  in
  let ids = List.fold_left fold Id.Set.empty el in
  if is_rec then intern_let_rec env loc ids el e
  else intern_let env loc ids el e
| CTacCnv (e, tc) ->
  let (e, t) = intern_rec env e in
  let tc = intern_type env tc in
  let () = unify ?loc env t tc in
  (e, tc)
| CTacSeq (e1, e2) ->
  let loc1 = e1.loc in
  let (e1, t1) = intern_rec env e1 in
  let (e2, t2) = intern_rec env e2 in
  let () = check_elt_unit loc1 env t1 in
  (GTacLet (false, [Anonymous, e1], e2), t2)
| CTacCse (e, pl) ->
  intern_case env loc e pl
| CTacRec fs ->
  intern_record env loc fs
| CTacPrj (e, proj) ->
  let pinfo = get_projection proj in
  let loc = e.loc in
  let (e, t) = intern_rec env e in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (Other pinfo.pdata_type, params) in
  let () = unify ?loc env t exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  (GTacPrj (pinfo.pdata_type, e, pinfo.pdata_indx), ret)
| CTacSet (e, proj, r) ->
  let pinfo = get_projection proj in
  let () =
    if not pinfo.pdata_mutb then
      let loc = match proj with
      | RelId {CAst.loc} -> loc
      | AbsKn _ -> None
      in
      user_err ?loc (str "Field is not mutable")
  in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (Other pinfo.pdata_type, params) in
  let e = intern_rec_with_constraint env e exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  let r = intern_rec_with_constraint env r ret in
  (GTacSet (pinfo.pdata_type, e, pinfo.pdata_indx, r), GTypRef (Tuple 0, []))
| CTacExt (tag, arg) ->
  let open Genintern in
  let self ist e =
    let env = match Store.get ist.extra ltac2_env with
    | None -> empty_env ()
    | Some env -> env
    in
    intern_rec env e
  in
  let obj = interp_ml_object tag in
  (* External objects do not have access to the named context because this is
     not stable by dynamic semantics. *)
  let genv = Global.env_of_context Environ.empty_named_context_val in
  let ist = empty_glob_sign genv in
  let ist = { ist with extra = Store.set ist.extra ltac2_env env } in
  let arg, tpe =
    if env.env_str then
      let arg () = obj.ml_intern self ist arg in
      Flags.with_option Ltac_plugin.Tacintern.strict_check arg ()
    else
      obj.ml_intern self ist arg
  in
  let e = match arg with
  | GlbVal arg -> GTacExt (tag, arg)
  | GlbTacexpr e -> e
  in
  (e, tpe)

and intern_rec_with_constraint env e exp =
  let (er, t) = intern_rec env e in
  let () = unify ?loc:e.loc env t exp in
  er

and intern_let env loc ids el e =
  let avoid = Id.Set.union ids (Id.Map.domain env.env_var) in
  let fold (pat, t, e) (avoid, accu) =
    let nas, exp = expand_pattern avoid [pat, t] in
    let na = match nas with [x] -> x | _ -> assert false in
    let avoid = List.fold_left add_name avoid nas in
    (avoid, (na, exp, t, e) :: accu)
  in
  let (_, el) = List.fold_right fold el (avoid, []) in
  let fold (na, exp, tc, e) (body, el, p) =
    let (e, t) = match tc with
    | None -> intern_rec env e
    | Some tc ->
      let tc = intern_type env tc in
      (intern_rec_with_constraint env e tc, tc)
    in
    let t = if is_value e then abstract_var env t else monomorphic t in
    (exp body, (na, e) :: el, (na, t) :: p)
  in
  let (e, el, p) = List.fold_right fold el (e, [], []) in
  let env = List.fold_left (fun accu (na, t) -> push_name na t accu) env p in
  let (e, t) = intern_rec env e in
  (GTacLet (false, el, e), t)

and intern_let_rec env loc ids el e =
  let map env (pat, t, e) =
    let na = match pat.v with
    | CPatVar na -> na
    | CPatRef _ | CPatCnv _ ->
      user_err ?loc:pat.loc (str "This kind of pattern is forbidden in let-rec bindings")
    in
    let id = fresh_id env in
    let env = push_name na (monomorphic (GTypVar id)) env in
    (env, (loc, na, t, e, id))
  in
  let (env, el) = List.fold_left_map map env el in
  let fold (loc, na, tc, e, id) (el, tl) =
    let loc_e = e.loc in
    let (e, t) = intern_rec env e in
    let () =
      if not (is_rec_rhs e) then
        user_err ?loc:loc_e (str "This kind of expression is not allowed as \
          right-hand side of a recursive binding")
    in
    let () = unify ?loc env t (GTypVar id) in
    let () = match tc with
    | None -> ()
    | Some tc ->
      let tc = intern_type env tc in
      unify ?loc env t tc
    in
    ((na, e) :: el, t :: tl)
  in
  let (el, tl) = List.fold_right fold el ([], []) in
  let (e, t) = intern_rec env e in
  (GTacLet (true, el, e), t)

(** For now, patterns recognized by the pattern-matching compiling are limited
    to depth-one where leaves are either variables or catch-all *)
and intern_case env loc e pl =
  let (e', t) = intern_rec env e in
  let todo ?loc () = user_err ?loc (str "Pattern not handled yet") in
  match get_pattern_kind env pl with
  | PKind_any ->
    let (pat, b) = List.hd pl in
    let na = match intern_patexpr env pat with
    | GPatVar na -> na
    | _ -> assert false
    in
    let () = check_redundant_clause (List.tl pl) in
    let env = push_name na (monomorphic t) env in
    let (b, tb) = intern_rec env b in
    (GTacLet (false, [na, e'], b), tb)
  | PKind_empty ->
    let kn = check_elt_empty loc env t in
    let r = fresh_id env in
    (GTacCse (e', Other kn, [||], [||]), GTypVar r)
  | PKind_variant kn ->
    let subst, tc = fresh_reftype env kn in
    let () = unify ?loc:e.loc env t tc in
    let (nconst, nnonconst, arities) = match kn with
    | Tuple 0 -> 1, 0, [0]
    | Tuple n -> 0, 1, [n]
    | Other kn ->
      let (_, def) = Tac2env.interp_type kn in
      let galg = match def with | GTydAlg c -> c | _ -> assert false in
      let arities = List.map (fun (_, args) -> List.length args) galg.galg_constructors in
      galg.galg_nconst, galg.galg_nnonconst, arities
    in
    let const = Array.make nconst None in
    let nonconst = Array.make nnonconst None in
    let ret = GTypVar (fresh_id env) in
    let rec intern_branch = function
    | [] -> ()
    | (pat, br) :: rem ->
      let tbr = match pat.v with
      | CPatVar (Name _) ->
        let loc = pat.loc in
        todo ?loc ()
      | CPatVar Anonymous ->
        let () = check_redundant_clause rem in
        let (br', brT) = intern_rec env br in
        (* Fill all remaining branches *)
        let fill (ncst, narg) arity =
          if Int.equal arity 0 then
            let () =
              if Option.is_empty const.(ncst) then const.(ncst) <- Some br'
            in
            (succ ncst, narg)
          else
            let () =
              if Option.is_empty nonconst.(narg) then
                let ids = Array.make arity Anonymous in
                nonconst.(narg) <- Some (ids, br')
            in
            (ncst, succ narg)
        in
        let _ = List.fold_left fill (0, 0) arities in
        brT
      | CPatRef (qid, args) ->
        let loc = pat.loc in
        let knc = get_constructor env qid in
        let kn', index, arity = match knc with
        | Tuple n -> Tuple n, 0, List.init n (fun i -> GTypVar i)
        | Other knc ->
          let data = Tac2env.interp_constructor knc in
          let index = Option.get data.cdata_indx in
          Other data.cdata_type, index, data.cdata_args
        in
        let () =
          if not (eq_or_tuple KerName.equal kn kn') then
            invalid_pattern ?loc kn kn'
        in
        let get_id pat = match pat with
        | {v=CPatVar na} -> na
        | {loc} -> todo ?loc ()
        in
        let ids = List.map get_id args in
        let nids = List.length ids in
        let nargs = List.length arity in
        let () = match knc with
        | Tuple n -> assert (n == nids)
        | Other knc ->
          if not (Int.equal nids nargs) then error_nargs_mismatch ?loc knc nargs nids
        in
        let fold env id tpe =
          (* Instantiate all arguments *)
          let subst n = GTypVar subst.(n) in
          let tpe = subst_type subst tpe in
          push_name id (monomorphic tpe) env
        in
        let nenv = List.fold_left2 fold env ids arity in
        let (br', brT) = intern_rec nenv br in
        let () =
          if List.is_empty args then
            if Option.is_empty const.(index) then const.(index) <- Some br'
            else warn_redundant_clause ?loc ()
          else
            let ids = Array.of_list ids in
            if Option.is_empty nonconst.(index) then nonconst.(index) <- Some (ids, br')
            else warn_redundant_clause ?loc ()
        in
        brT
      | CPatCnv _ ->
        user_err ?loc (str "Pattern not handled yet")
      in
      let () = unify ?loc:br.loc env tbr ret in
      intern_branch rem
    in
    let () = intern_branch pl in
    let map n is_const = function
    | None ->
      let kn = match kn with Other kn -> kn | _ -> assert false in
      let cstr = pr_internal_constructor kn n is_const in
      user_err ?loc (str "Unhandled match case for constructor " ++ cstr)
    | Some x -> x
    in
    let const = Array.mapi (fun i o -> map i true o) const in
    let nonconst = Array.mapi (fun i o -> map i false o) nonconst in
    let ce = GTacCse (e', kn, const, nonconst) in
    (ce, ret)
  | PKind_open kn ->
    let subst, tc = fresh_reftype env (Other kn) in
    let () = unify ?loc:e.loc env t tc in
    let ret = GTypVar (fresh_id env) in
    let rec intern_branch map = function
    | [] ->
      user_err ?loc (str "Missing default case")
    | (pat, br) :: rem ->
      match intern_patexpr env pat with
      | GPatVar na ->
        let () = check_redundant_clause rem in
        let nenv = push_name na (monomorphic tc) env in
        let br' = intern_rec_with_constraint nenv br ret in
        let def = (na, br') in
        (map, def)
      | GPatRef (knc, args) ->
        let get = function
        | GPatVar na -> na
        | GPatRef _ ->
          user_err ?loc (str "TODO: Unhandled match case") (* FIXME *)
        in
        let loc = pat.loc in
        let knc = match knc with
        | Other knc -> knc
        | Tuple n -> invalid_pattern ?loc (Other kn) (Tuple n)
        in
        let ids = List.map get args in
        let data = Tac2env.interp_constructor knc in
        let () =
          if not (KerName.equal kn data.cdata_type) then
            invalid_pattern ?loc (Other kn) (Other data.cdata_type)
        in
        let nids = List.length ids in
        let nargs = List.length data.cdata_args in
        let () =
          if not (Int.equal nids nargs) then error_nargs_mismatch ?loc knc nargs nids
        in
        let fold env id tpe =
          (* Instantiate all arguments *)
          let subst n = GTypVar subst.(n) in
          let tpe = subst_type subst tpe in
          push_name id (monomorphic tpe) env
        in
        let nenv = List.fold_left2 fold env ids data.cdata_args in
        let br' = intern_rec_with_constraint nenv br ret in
        let map =
          if KNmap.mem knc map then
            let () = warn_redundant_clause ?loc () in
            map
          else
            KNmap.add knc (Anonymous, Array.of_list ids, br') map
        in
        intern_branch map rem
    in
    let (map, def) = intern_branch KNmap.empty pl in
    (GTacWth { opn_match = e'; opn_branch = map; opn_default = def }, ret)

and intern_constructor env loc kn args = match kn with
| Other kn ->
  let cstr = interp_constructor kn in
  let nargs = List.length cstr.cdata_args in
  if Int.equal nargs (List.length args) then
    let subst = Array.init cstr.cdata_prms (fun _ -> fresh_id env) in
    let substf i = GTypVar subst.(i) in
    let types = List.map (fun t -> subst_type substf t) cstr.cdata_args in
    let targs = List.init cstr.cdata_prms (fun i -> GTypVar subst.(i)) in
    let ans = GTypRef (Other cstr.cdata_type, targs) in
    let map arg tpe = intern_rec_with_constraint env arg tpe in
    let args = List.map2 map args types in
    match cstr.cdata_indx with
    | Some idx ->
      (GTacCst (Other cstr.cdata_type, idx, args), ans)
    | None ->
      (GTacOpn (kn, args), ans)
  else
    error_nargs_mismatch ?loc kn nargs (List.length args)
| Tuple n ->
  assert (Int.equal n (List.length args));
  let types = List.init n (fun i -> GTypVar (fresh_id env)) in
  let map arg tpe = intern_rec_with_constraint env arg tpe in
  let args = List.map2 map args types in
  let ans = GTypRef (Tuple n, types) in
  GTacCst (Tuple n, 0, args), ans

and intern_record env loc fs =
  let map (proj, e) =
    let loc = match proj with
    | RelId {CAst.loc} -> loc
    | AbsKn _ -> None
    in
    let proj = get_projection proj in
    (loc, proj, e)
  in
  let fs = List.map map fs in
  let kn = match fs with
  | [] -> user_err ?loc (str "Cannot infer the corresponding record type")
  | (_, proj, _) :: _ -> proj.pdata_type
  in
  let params, typdef = match Tac2env.interp_type kn with
  | n, GTydRec def -> n, def
  | _ -> assert false
  in
  let subst = Array.init params (fun _ -> fresh_id env) in
  (* Set the answer [args] imperatively *)
  let args = Array.make (List.length typdef) None in
  let iter (loc, pinfo, e) =
    if KerName.equal kn pinfo.pdata_type then
      let index = pinfo.pdata_indx in
      match args.(index) with
      | None ->
        let exp = subst_type (fun i -> GTypVar subst.(i)) pinfo.pdata_ptyp in
        let e = intern_rec_with_constraint env e exp in
        args.(index) <- Some e
      | Some _ ->
        let (name, _, _) = List.nth typdef pinfo.pdata_indx in
        user_err ?loc (str "Field " ++ Id.print name ++ str " is defined \
          several times")
    else
      user_err ?loc (str "Field " ++ (*KerName.print knp ++*) str " does not \
        pertain to record definition " ++ pr_typref pinfo.pdata_type)
  in
  let () = List.iter iter fs in
  let () = match Array.findi (fun _ o -> Option.is_empty o) args with
  | None -> ()
  | Some i ->
    let (field, _, _) = List.nth typdef i in
    user_err ?loc (str "Field " ++ Id.print field ++ str " is undefined")
  in
  let args = Array.map_to_list Option.get args in
  let tparam = List.init params (fun i -> GTypVar subst.(i)) in
  (GTacCst (Other kn, 0, args), GTypRef (Other kn, tparam))

let normalize env (count, vars) (t : UF.elt glb_typexpr) =
  let get_var id =
    try UF.Map.find id !vars
    with Not_found ->
      let () = assert env.env_opn in
      let n = GTypVar !count in
      let () = incr count in
      let () = vars := UF.Map.add id n !vars in
      n
  in
  let rec subst id = match UF.find id env.env_cst with
  | id, None -> get_var id
  | _, Some t -> subst_type subst t
  in
  subst_type subst t

let intern ~strict e =
  let env = empty_env () in
  let env = if strict then env else { env with env_str = false } in
  let (e, t) = intern_rec env e in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let t = normalize env (count, vars) t in
  (e, (!count, t))

let intern_typedef self (ids, t) : glb_quant_typedef =
  let env = { (empty_env ()) with env_rec = self } in
  (* Initialize type parameters *)
  let map id = get_alias id env in
  let ids = List.map map ids in
  let count = ref (List.length ids) in
  let vars = ref UF.Map.empty in
  let iter n id = vars := UF.Map.add id (GTypVar n) !vars in
  let () = List.iteri iter ids in
  (* Do not accept unbound type variables *)
  let env = { env with env_opn = false } in
  let intern t =
    let t = intern_type env t in
    normalize env (count, vars) t
  in
  let count = !count in
  match t with
  | CTydDef None -> (count, GTydDef None)
  | CTydDef (Some t) -> (count, GTydDef (Some (intern t)))
  | CTydAlg constrs ->
    let map (c, t) = (c, List.map intern t) in
    let constrs = List.map map constrs in
    let getn (const, nonconst) (c, args) = match args with
    | [] -> (succ const, nonconst)
    | _ :: _ -> (const, succ nonconst)
    in
    let nconst, nnonconst = List.fold_left getn (0, 0) constrs in
    let galg = {
      galg_constructors = constrs;
      galg_nconst = nconst;
      galg_nnonconst = nnonconst;
    } in
    (count, GTydAlg galg)
  | CTydRec fields ->
    let map (c, mut, t) = (c, mut, intern t) in
    let fields = List.map map fields in
    (count, GTydRec fields)
  | CTydOpn -> (count, GTydOpn)

let intern_open_type t =
  let env = empty_env () in
  let t = intern_type env t in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let t = normalize env (count, vars) t in
  (!count, t)

(** Subtyping *)

let check_subtype t1 t2 =
  let env = empty_env () in
  let t1 = fresh_type_scheme env t1 in
  (* We build a substitution mimicking rigid variable by using dummy tuples *)
  let rigid i = GTypRef (Tuple (i + 1), []) in
  let (n, t2) = t2 in
  let subst = Array.init n rigid in
  let substf i = subst.(i) in
  let t2 = subst_type substf t2 in
  try unify0 env t1 t2; true with CannotUnify _ -> false

(** Globalization *)

let get_projection0 var = match var with
| RelId qid ->
  let kn = try Tac2env.locate_projection qid with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++ str " is not a projection")
  in
  kn
| AbsKn kn -> kn

let rec globalize ids ({loc;v=er} as e) = match er with
| CTacAtm _ -> e
| CTacRef ref ->
  let mem id = Id.Set.mem id ids in
  begin match get_variable0 mem ref with
  | ArgVar _ -> e
  | ArgArg kn -> CAst.make ?loc @@ CTacRef (AbsKn kn)
  end
| CTacCst qid ->
  let knc = get_constructor () qid in
  CAst.make ?loc @@ CTacCst (AbsKn knc)
| CTacFun (bnd, e) ->
  let fold (pats, accu) pat =
    let accu = ids_of_pattern accu pat in
    let pat = globalize_pattern ids pat in
    (pat :: pats, accu)
  in
  let bnd, ids = List.fold_left fold ([], ids) bnd in
  let bnd = List.rev bnd in
  let e = globalize ids e in
  CAst.make ?loc @@ CTacFun (bnd, e)
| CTacApp (e, el) ->
  let e = globalize ids e in
  let el = List.map (fun e -> globalize ids e) el in
  CAst.make ?loc @@ CTacApp (e, el)
| CTacLet (isrec, bnd, e) ->
  let fold accu (pat, _) = ids_of_pattern accu pat in
  let ext = List.fold_left fold Id.Set.empty bnd in
  let eids = Id.Set.union ext ids in
  let e = globalize eids e in
  let map (qid, e) =
    let ids = if isrec then eids else ids in
    let qid = globalize_pattern ids qid in
    (qid, globalize ids e)
  in
  let bnd = List.map map bnd in
  CAst.make ?loc @@ CTacLet (isrec, bnd, e)
| CTacCnv (e, t) ->
  let e = globalize ids e in
  CAst.make ?loc @@ CTacCnv (e, t)
| CTacSeq (e1, e2) ->
  let e1 = globalize ids e1 in
  let e2 = globalize ids e2 in
  CAst.make ?loc @@ CTacSeq (e1, e2)
| CTacCse (e, bl) ->
  let e = globalize ids e in
  let bl = List.map (fun b -> globalize_case ids b) bl in
  CAst.make ?loc @@ CTacCse (e, bl)
| CTacRec r ->
  let map (p, e) =
    let p = get_projection0 p in
    let e = globalize ids e in
    (AbsKn p, e)
  in
  CAst.make ?loc @@ CTacRec (List.map map r)
| CTacPrj (e, p) ->
  let e = globalize ids e in
  let p = get_projection0 p in
  CAst.make ?loc @@ CTacPrj (e, AbsKn p)
| CTacSet (e, p, e') ->
  let e = globalize ids e in
  let p = get_projection0 p in
  let e' = globalize ids e' in
  CAst.make ?loc @@ CTacSet (e, AbsKn p, e')
| CTacExt (tag, arg) ->
  let arg = str (Tac2dyn.Arg.repr tag) in
  CErrors.user_err ?loc (str "Cannot globalize generic arguments of type" ++ spc () ++ arg)

and globalize_case ids (p, e) =
  (globalize_pattern ids p, globalize ids e)

and globalize_pattern ids ({loc;v=pr} as p) = match pr with
| CPatVar _ -> p
| CPatRef (cst, pl) ->
  let knc = get_constructor () cst in
  let cst = AbsKn knc in
  let pl = List.map (fun p -> globalize_pattern ids p) pl in
  CAst.make ?loc @@ CPatRef (cst, pl)
| CPatCnv (pat, ty) ->
  let pat = globalize_pattern ids pat in
  CAst.make ?loc @@ CPatCnv (pat, ty)

(** Kernel substitution *)

open Mod_subst

let subst_or_tuple f subst o = match o with
| Tuple _ -> o
| Other v ->
  let v' = f subst v in
  if v' == v then o else Other v'

let rec subst_type subst t = match t with
| GTypVar _ -> t
| GTypArrow (t1, t2) ->
  let t1' = subst_type subst t1 in
  let t2' = subst_type subst t2 in
  if t1' == t1 && t2' == t2 then t
  else GTypArrow (t1', t2')
| GTypRef (kn, tl) ->
  let kn' = subst_or_tuple subst_kn subst kn in
  let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
  if kn' == kn && tl' == tl then t else GTypRef (kn', tl')

let rec subst_expr subst e = match e with
| GTacAtm _ | GTacVar _ | GTacPrm _ -> e
| GTacRef kn -> GTacRef (subst_kn subst kn)
| GTacFun (ids, e) -> GTacFun (ids, subst_expr subst e)
| GTacApp (f, args) ->
  GTacApp (subst_expr subst f, List.map (fun e -> subst_expr subst e) args)
| GTacLet (r, bs, e) ->
  let bs = List.map (fun (na, e) -> (na, subst_expr subst e)) bs in
  GTacLet (r, bs, subst_expr subst e)
| GTacCst (t, n, el) as e0 ->
  let t' = subst_or_tuple subst_kn subst t in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if t' == t && el' == el then e0 else GTacCst (t', n, el')
| GTacCse (e, ci, cse0, cse1) ->
  let cse0' = Array.map (fun e -> subst_expr subst e) cse0 in
  let cse1' = Array.map (fun (ids, e) -> (ids, subst_expr subst e)) cse1 in
  let ci' = subst_or_tuple subst_kn subst ci in
  GTacCse (subst_expr subst e, ci', cse0', cse1')
| GTacWth { opn_match = e; opn_branch = br; opn_default = (na, def) } as e0 ->
  let e' = subst_expr subst e in
  let def' = subst_expr subst def in
  let fold kn (self, vars, p) accu =
    let kn' = subst_kn subst kn in
    let p' = subst_expr subst p in
    if kn' == kn && p' == p then accu
    else KNmap.add kn' (self, vars, p') (KNmap.remove kn accu)
  in
  let br' = KNmap.fold fold br br in
  if e' == e && br' == br && def' == def then e0
  else GTacWth { opn_match = e'; opn_default = (na, def'); opn_branch = br' }
| GTacPrj (kn, e, p) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  if kn' == kn && e' == e then e0 else GTacPrj (kn', e', p)
| GTacSet (kn, e, p, r) as e0 ->
  let kn' = subst_kn subst kn in
  let e' = subst_expr subst e in
  let r' = subst_expr subst r in
  if kn' == kn && e' == e && r' == r then e0 else GTacSet (kn', e', p, r')
| GTacExt (tag, arg) ->
  let tpe = interp_ml_object tag in
  let arg' = tpe.ml_subst subst arg in
  if arg' == arg then e else GTacExt (tag, arg')
| GTacOpn (kn, el) as e0 ->
  let kn' = subst_kn subst kn in
  let el' = List.Smart.map (fun e -> subst_expr subst e) el in
  if kn' == kn && el' == el then e0 else GTacOpn (kn', el')

let subst_typedef subst e = match e with
| GTydDef t ->
  let t' = Option.Smart.map (fun t -> subst_type subst t) t in
  if t' == t then e else GTydDef t'
| GTydAlg galg ->
  let map (c, tl as p) =
    let tl' = List.Smart.map (fun t -> subst_type subst t) tl in
    if tl' == tl then p else (c, tl')
  in
  let constrs' = List.Smart.map map galg.galg_constructors in
  if constrs' == galg.galg_constructors then e
  else GTydAlg { galg with galg_constructors = constrs' }
| GTydRec fields ->
  let map (c, mut, t as p) =
    let t' = subst_type subst t in
    if t' == t then p else (c, mut, t')
  in
  let fields' = List.Smart.map map fields in
  if fields' == fields then e else GTydRec fields'
| GTydOpn -> GTydOpn

let subst_quant_typedef subst (prm, def as qdef) =
  let def' = subst_typedef subst def in
  if def' == def then qdef else (prm, def')

let subst_type_scheme subst (prm, t as sch) =
  let t' = subst_type subst t in
  if t' == t then sch else (prm, t')

let subst_or_relid subst ref = match ref with
| RelId _ -> ref
| AbsKn kn ->
  let kn' = subst_or_tuple subst_kn subst kn in
  if kn' == kn then ref else AbsKn kn'

let rec subst_rawtype subst ({loc;v=tr} as t) = match tr with
| CTypVar _ -> t
| CTypArrow (t1, t2) ->
  let t1' = subst_rawtype subst t1 in
  let t2' = subst_rawtype subst t2 in
  if t1' == t1 && t2' == t2 then t else CAst.make ?loc @@ CTypArrow (t1', t2')
| CTypRef (ref, tl) ->
  let ref' = subst_or_relid subst ref in
  let tl' = List.Smart.map (fun t -> subst_rawtype subst t) tl in
  if ref' == ref && tl' == tl then t else CAst.make ?loc @@ CTypRef (ref', tl')

let subst_tacref subst ref = match ref with
| RelId _ -> ref
| AbsKn (TacConstant kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacConstant kn')
| AbsKn (TacAlias kn) ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ref else AbsKn (TacAlias kn')

let subst_projection subst prj = match prj with
| RelId _ -> prj
| AbsKn kn ->
  let kn' = subst_kn subst kn in
  if kn' == kn then prj else AbsKn kn'

let rec subst_rawpattern subst ({loc;v=pr} as p) = match pr with
| CPatVar _ -> p
| CPatRef (c, pl) ->
  let pl' = List.Smart.map (fun p -> subst_rawpattern subst p) pl in
  let c' = subst_or_relid subst c in
  if pl' == pl && c' == c then p else CAst.make ?loc @@ CPatRef (c', pl')
| CPatCnv (pat, ty) ->
  let pat' = subst_rawpattern subst pat in
  let ty' = subst_rawtype subst ty in
  if pat' == pat && ty' == ty then p else CAst.make ?loc @@ CPatCnv (pat', ty')

(** Used for notations *)
let rec subst_rawexpr subst ({loc;v=tr} as t) = match tr with
| CTacAtm _ -> t
| CTacRef ref ->
  let ref' = subst_tacref subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacRef ref'
| CTacCst ref ->
  let ref' = subst_or_relid subst ref in
  if ref' == ref then t else CAst.make ?loc @@ CTacCst ref'
| CTacFun (bnd, e) ->
  let map pat = subst_rawpattern subst pat in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacFun (bnd', e')
| CTacApp (e, el) ->
  let e' = subst_rawexpr subst e in
  let el' = List.Smart.map (fun e -> subst_rawexpr subst e) el in
  if e' == e && el' == el then t else CAst.make ?loc @@ CTacApp (e', el')
| CTacLet (isrec, bnd, e) ->
  let map (na, e as p) =
    let na' = subst_rawpattern subst na in
    let e' = subst_rawexpr subst e in
    if na' == na && e' == e then p else (na', e')
  in
  let bnd' = List.Smart.map map bnd in
  let e' = subst_rawexpr subst e in
  if bnd' == bnd && e' == e then t else CAst.make ?loc @@ CTacLet (isrec, bnd', e')
| CTacCnv (e, c) ->
  let e' = subst_rawexpr subst e in
  let c' = subst_rawtype subst c in
  if c' == c && e' == e then t else CAst.make ?loc @@ CTacCnv (e', c')
| CTacSeq (e1, e2) ->
  let e1' = subst_rawexpr subst e1 in
  let e2' = subst_rawexpr subst e2 in
  if e1' == e1 && e2' == e2 then t else CAst.make ?loc @@ CTacSeq (e1', e2')
| CTacCse (e, bl) ->
  let map (p, e as x) =
    let p' = subst_rawpattern subst p in
    let e' = subst_rawexpr subst e in
    if p' == p && e' == e then x else (p', e')
  in
  let e' = subst_rawexpr subst e in
  let bl' = List.Smart.map map bl in
  if e' == e && bl' == bl then t else CAst.make ?loc @@ CTacCse (e', bl')
| CTacRec el ->
  let map (prj, e as p) =
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then p else (prj', e')
  in
  let el' = List.Smart.map map el in
  if el' == el then t else CAst.make ?loc @@ CTacRec el'
| CTacPrj (e, prj) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    if prj' == prj && e' == e then t else CAst.make ?loc @@ CTacPrj (e', prj')
| CTacSet (e, prj, r) ->
    let prj' = subst_projection subst prj in
    let e' = subst_rawexpr subst e in
    let r' = subst_rawexpr subst r in
    if prj' == prj && e' == e && r' == r then t else CAst.make ?loc @@ CTacSet (e', prj', r')
| CTacExt _ -> assert false (** Should not be generated by globalization *)

(** Registering *)

let () =
  let open Genintern in
  let intern ist tac =
    let env = match Genintern.Store.get ist.extra ltac2_env with
    | None ->
      (* Only happens when Ltac2 is called from a constr or ltac1 quotation *)
      let env = empty_env () in
      if !Ltac_plugin.Tacintern.strict_check then env
      else { env with env_str = false }
    | Some env -> env
    in
    let loc = tac.loc in
    let (tac, t) = intern_rec env tac in
    let () = check_elt_unit loc env t in
    (ist, tac)
  in
  Genintern.register_intern0 wit_ltac2 intern
let () = Genintern.register_subst0 wit_ltac2 subst_expr

let () =
  let open Genintern in
  let intern ist (loc, id) =
    let env = match Genintern.Store.get ist.extra ltac2_env with
    | None ->
      (* Only happens when Ltac2 is called from a constr or ltac1 quotation *)
      let env = empty_env () in
      if !Ltac_plugin.Tacintern.strict_check then env
      else { env with env_str = false }
    | Some env -> env
    in
    let t =
      try Id.Map.find id env.env_var
      with Not_found ->
        CErrors.user_err ?loc (str "Unbound value " ++ Id.print id)
    in
    let t = fresh_mix_type_scheme env t in
    let () = unify ?loc env t (GTypRef (Other t_constr, [])) in
    (ist, id)
  in
  Genintern.register_intern0 wit_ltac2_quotation intern

let () = Genintern.register_subst0 wit_ltac2_quotation (fun _ id -> id)
