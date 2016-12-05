(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Genarg
open CErrors
open Names
open Libnames
open Misctypes
open Tac2env
open Tac2expr

(** Hardwired types and constants *)

let coq_type n = KerName.make2 Tac2env.coq_prefix (Label.make n)

let t_int = coq_type "int"
let t_string = coq_type "string"
let t_array = coq_type "array"
let t_unit = coq_type "unit"
let t_list = coq_type "list"

let c_nil = GTacCst (t_list, 0, [])
let c_cons e el = GTacCst (t_list, 0, [e; el])

(** Union find *)

module UF :
sig
type elt
type 'a t
val equal : elt -> elt -> bool
val create : unit -> 'a t
val fresh : 'a t -> elt
val size : 'a t -> int
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

let size p = p.uf_size

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
}

let empty_env () = {
  env_var = Id.Map.empty;
  env_cst = UF.create ();
  env_als = ref Id.Map.empty;
  env_opn = true;
  env_rec = Id.Map.empty;
}

let ltac2_env : environment Genintern.Store.field =
  Genintern.Store.field ()

let fresh_id env = UF.fresh env.env_cst

let get_alias (loc, id) env =
  try Id.Map.find id env.env_als.contents
  with Not_found ->
    if env.env_opn then
      let n = fresh_id env in
      let () = env.env_als := Id.Map.add id n env.env_als.contents in
      n
    else user_err ~loc (str "Unbound type parameter " ++ Id.print id)

let push_name id t env = match id with
| Anonymous -> env
| Name id -> { env with env_var = Id.Map.add id t env.env_var }

let loc_of_tacexpr = function
| CTacAtm (loc, _) -> loc
| CTacRef (loc, _) -> loc
| CTacFun (loc, _, _) -> loc
| CTacApp (loc, _, _) -> loc
| CTacLet (loc, _, _, _) -> loc
| CTacTup (loc, _) -> loc
| CTacArr (loc, _) -> loc
| CTacLst (loc, _) -> loc
| CTacCnv (loc, _, _) -> loc
| CTacSeq (loc, _, _) -> loc
| CTacCse (loc, _, _) -> loc
| CTacRec (loc, _) -> loc
| CTacPrj (loc, _, _) -> loc
| CTacSet (loc, _, _, _) -> loc
| CTacExt (loc, _) -> loc

let loc_of_patexpr = function
| CPatAny loc -> loc
| CPatRef (loc, _, _) -> loc
| CPatTup (loc, _) -> loc

let error_nargs_mismatch loc nargs nfound =
  user_err ~loc (str "Constructor expects " ++ int nargs ++
    str " arguments, but is applied to " ++ int nfound ++
    str " arguments")

let rec subst_type subst (t : 'a glb_typexpr) = match t with
| GTypVar id -> subst id
| GTypArrow (t1, t2) -> GTypArrow (subst_type subst t1, subst_type subst t2)
| GTypTuple tl -> GTypTuple (List.map (fun t -> subst_type subst t) tl)
| GTypRef (qid, args) ->
  GTypRef (qid, List.map (fun t -> subst_type subst t) args)

let rec intern_type env (t : raw_typexpr) : UF.elt glb_typexpr = match t with
| CTypVar (loc, Name id) -> GTypVar (get_alias (loc, id) env)
| CTypVar (_, Anonymous) -> GTypVar (fresh_id env)
| CTypRef (_, (loc, qid), args) ->
  let (dp, id) = repr_qualid qid in
  let (kn, nparams) =
    if DirPath.is_empty dp && Id.Map.mem id env.env_rec then
      Id.Map.find id env.env_rec
    else
      let kn =
        try Tac2env.locate_type qid
        with Not_found ->
          user_err ~loc (str "Unbound type constructor " ++ pr_qualid qid)
      in
      let (nparams, _) = Tac2env.interp_type kn in
      (kn, nparams)
  in
  let nargs = List.length args in
  let () =
    if not (Int.equal nparams nargs) then
      user_err ~loc (strbrk "The type constructor " ++ pr_qualid qid ++
        strbrk " expects " ++ int nparams ++ strbrk " argument(s), but is here \
        applied to " ++ int nargs ++ strbrk "argument(s)")
  in
  GTypRef (kn, List.map (fun t -> intern_type env t) args)
| CTypArrow (loc, t1, t2) -> GTypArrow (intern_type env t1, intern_type env t2)
| CTypTuple (loc, tl) -> GTypTuple (List.map (fun t -> intern_type env t) tl)

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

let fresh_reftype env (kn : KerName.t) =
  let (n, _) = Tac2env.interp_type kn in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let t = GTypRef (kn, Array.map_to_list (fun i -> GTypVar i) subst) in
  (subst, t)

(** First-order unification algorithm *)

let is_unfoldable kn = match snd (Tac2env.interp_type kn) with
| GTydDef (Some _) -> true
| GTydDef None | GTydAlg _ | GTydRec _ -> false

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
| GTypRef (kn, tl) ->
  if is_unfoldable kn then kind env (unfold env kn tl) else t
| GTypArrow _ | GTypTuple _ -> t

exception Occur

let rec occur_check env id t = match kind env t with
| GTypVar id' -> if UF.equal id id' then raise Occur
| GTypArrow (t1, t2) ->
  let () = occur_check env id t1 in
  occur_check env id t2
| GTypTuple tl ->
  List.iter (fun t -> occur_check env id t) tl
| GTypRef (kn, tl) ->
  List.iter (fun t -> occur_check env id t) tl

exception CannotUnify of UF.elt glb_typexpr * UF.elt glb_typexpr

let unify_var env id t = match kind env t with
| GTypVar id' ->
  if not (UF.equal id id') then UF.union id id' env.env_cst
| GTypArrow _ | GTypRef _ | GTypTuple _ ->
  try
    let () = occur_check env id t in
    UF.set id t env.env_cst
  with Occur -> raise (CannotUnify (GTypVar id, t))

let rec unify env t1 t2 = match kind env t1, kind env t2 with
| GTypVar id, t | t, GTypVar id ->
  unify_var env id t
| GTypArrow (t1, u1), GTypArrow (t2, u2) ->
  let () = unify env t1 t2 in
  unify env u1 u2
| GTypTuple tl1, GTypTuple tl2 ->
  if Int.equal (List.length tl1) (List.length tl2) then
    List.iter2 (fun t1 t2 -> unify env t1 t2) tl1 tl2
  else raise (CannotUnify (t1, t2))
| GTypRef (kn1, tl1), GTypRef (kn2, tl2) ->
  if KerName.equal kn1 kn2 then
    List.iter2 (fun t1 t2 -> unify env t1 t2) tl1 tl2
  else raise (CannotUnify (t1, t2))
| _ -> raise (CannotUnify (t1, t2))

(** FIXME *)
let rec pr_glbtype = function
| GTypVar n -> str "?"
| GTypRef (kn, tl) ->
  KerName.print kn ++ str "(" ++ prlist_with_sep (fun () -> str ", ") pr_glbtype tl ++ str ")"
| GTypArrow (t1, t2) -> str "Arr(" ++ pr_glbtype t1 ++ str ", " ++ pr_glbtype t2 ++ str ")"
| GTypTuple tl -> str "Tup(" ++ prlist_with_sep (fun () -> str ", ") pr_glbtype tl ++ str ")"

let unify loc env t1 t2 =
  try unify env t1 t2
  with CannotUnify (u1, u2) ->
    user_err ~loc (str "This expression has type " ++ pr_glbtype t1 ++
      str " but an expression what expected of type " ++ pr_glbtype t2)

(** Term typing *)

let is_pure_constructor kn =
  match snd (Tac2env.interp_type kn) with
  | GTydAlg _ -> true
  | GTydRec fields ->
    let is_pure (_, mut, _) = not mut in
    List.for_all is_pure fields
  | GTydDef _ -> assert false (** Type definitions have no constructors *)

let rec is_value = function
| GTacAtm (AtmInt _) | GTacVar _ | GTacRef _ | GTacFun _ -> true
| GTacAtm (AtmStr _) | GTacApp _ | GTacLet _ -> false
| GTacTup el -> List.for_all is_value el
| GTacCst (_, _, []) -> true
| GTacCst (kn, _, el) -> is_pure_constructor kn && List.for_all is_value el
| GTacArr _ | GTacCse _ | GTacPrj _ | GTacSet _ | GTacExt _ | GTacPrm _ -> false

let is_rec_rhs = function
| GTacFun _ -> true
| GTacAtm _ | GTacVar _ | GTacRef _ | GTacApp _ | GTacLet _ | GTacPrj _
| GTacSet _ | GTacTup _ | GTacArr _ | GTacExt _ | GTacPrm _ | GTacCst _
| GTacCse _ -> false

let rec fv_type f t accu = match t with
| GTypVar id -> f id accu
| GTypArrow (t1, t2) -> fv_type f t1 (fv_type f t2 accu)
| GTypTuple tl -> List.fold_left (fun accu t -> fv_type f t accu) accu tl
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
  | GTypArrow _ | GTypTuple _ -> false
  | GTypRef (kn, _) -> KerName.equal kn t_unit
  in
  if not maybe_unit then warn_not_unit ~loc ()

let check_elt_empty loc env t = match kind env t with
| GTypVar _ ->
  user_err ~loc (str "Cannot infer an empty type for this expression")
| GTypArrow _ | GTypTuple _ ->
  user_err ~loc (str "Type " ++ pr_glbtype t ++ str " is not an empty type")
| GTypRef (kn, _) ->
  let def = Tac2env.interp_type kn in
  match def with
  | _, GTydAlg [] -> kn
  | _ ->
    user_err ~loc (str "Type " ++ pr_glbtype t ++ str " is not an empty type")

let check_unit ?loc t =
  let maybe_unit = match t with
  | GTypVar _ -> true
  | GTypArrow _ | GTypTuple _ -> false
  | GTypRef (kn, _) -> KerName.equal kn t_unit
  in
  if not maybe_unit then warn_not_unit ?loc ()

let check_redundant_clause = function
| [] -> ()
| (p, _) :: _ -> warn_redundant_clause ~loc:(loc_of_patexpr p) ()

let get_variable env (loc, qid) =
  let (dp, id) = repr_qualid qid in
  if DirPath.is_empty dp && Id.Map.mem id env.env_var then ArgVar (loc, id)
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found ->
        CErrors.user_err ~loc (str "Unbound value " ++ pr_qualid qid)
    in
    ArgArg kn

let get_constructor env (loc, qid) =
  let c = try Some (Tac2env.locate_ltac qid) with Not_found -> None in
  match c with
  | Some (TacConstructor knc) ->
    let kn = Tac2env.interp_constructor knc in
    ArgArg (kn, knc)
  | Some (TacConstant _) ->
    CErrors.user_err ~loc (str "The term " ++ pr_qualid qid ++
      str " is not the constructor of an inductive type.")
  | None ->
    let (dp, id) = repr_qualid qid in
    if DirPath.is_empty dp then ArgVar (loc, id)
    else CErrors.user_err ~loc (str "Unbound constructor " ++ pr_qualid qid)

let get_projection (loc, qid) =
  let kn = try Tac2env.locate_projection qid with Not_found ->
    user_err ~loc (pr_qualid qid ++ str " is not a projection")
  in
  Tac2env.interp_projection kn

let intern_atm env = function
| AtmInt n -> (GTacAtm (AtmInt n), GTypRef (t_int, []))
| AtmStr s -> (GTacAtm (AtmStr s), GTypRef (t_string, []))

let invalid_pattern ~loc kn t =
  let pt = match t with
  | GCaseAlg kn' -> KerName.print kn
  | GCaseTuple n -> str "tuple"
  in
  user_err ~loc (str "Invalid pattern, expected a pattern for type " ++
    KerName.print kn ++ str ", found a pattern of type " ++ pt) (** FIXME *)

type pattern_kind =
| PKind_empty
| PKind_variant of KerName.t
| PKind_tuple of int
| PKind_any

let get_pattern_kind env pl = match pl with
| [] -> PKind_empty
| p :: pl ->
  let rec get_kind p pl = match fst p with
  | CPatAny _ ->
    begin match pl with
    | [] -> PKind_any
    | p :: pl -> get_kind p pl
    end
  | CPatRef (_, qid, []) ->
    begin match get_constructor env qid with
    | ArgVar _ ->
      begin match pl with
      | [] -> PKind_any
      | p :: pl -> get_kind p pl
      end
    | ArgArg (data, _) -> PKind_variant data.cdata_type
    end
  | CPatRef (_, qid, _ :: _) ->
    begin match get_constructor env qid with
    | ArgVar (loc, _) ->
      user_err ~loc (str "Unbound constructor " ++ pr_qualid (snd qid))
    | ArgArg (data, _) -> PKind_variant data.cdata_type
    end
  | CPatTup (_, tp) -> PKind_tuple (List.length tp)
  in
  get_kind p pl

let is_constructor env qid = match get_variable env qid with
| ArgArg (TacConstructor _) -> true
| _ -> false

let rec intern_rec env = function
| CTacAtm (_, atm) -> intern_atm env atm
| CTacRef qid ->
  begin match get_variable env qid with
  | ArgVar (_, id) ->
    let sch = Id.Map.find id env.env_var in
    (GTacVar id, fresh_mix_type_scheme env sch)
  | ArgArg (TacConstant kn) ->
    let (_, sch) = Tac2env.interp_global kn in
    (GTacRef kn, fresh_type_scheme env sch)
  | ArgArg (TacConstructor kn) ->
    intern_constructor env (fst qid) kn []
  end
| CTacFun (loc, bnd, e) ->
  let fold (env, bnd, tl) ((_, na), t) =
    let t = match t with
    | None -> GTypVar (fresh_id env)
    | Some t -> intern_type env t
    in
    let env = push_name na (monomorphic t) env in
    (env, na :: bnd, t :: tl)
  in
  let (env, bnd, tl) = List.fold_left fold (env, [], []) bnd in
  let (e, t) = intern_rec env e in
  let t = List.fold_left (fun accu t -> GTypArrow (t, accu)) t tl in
  (GTacFun (bnd, e), t)
| CTacApp (loc, CTacRef qid, args) when is_constructor env qid ->
  let kn = match get_variable env qid with
  | ArgArg (TacConstructor kn) -> kn
  | _ -> assert false
  in
  intern_constructor env (fst qid) kn args
| CTacApp (loc, f, args) ->
  let (f, ft) = intern_rec env f in
  let fold arg (args, t) =
    let (arg, argt) = intern_rec env arg in
    (arg :: args, GTypArrow (argt, t))
  in
  let ret = GTypVar (fresh_id env) in
  let (args, t) = List.fold_right fold args ([], ret) in
  let () = unify loc env ft t in
  (GTacApp (f, args), ret)
| CTacLet (loc, false, el, e) ->
  let fold accu ((loc, na), _, _) = match na with
  | Anonymous -> accu
  | Name id ->
    if Id.Set.mem id accu then
      user_err ~loc (str "Variable " ++ Id.print id ++ str " is bound several \
        times in this matching")
    else Id.Set.add id accu
  in
  let _ = List.fold_left fold Id.Set.empty el in
  let fold ((loc, na), tc, e) (el, p) =
    let (e, t) = intern_rec env e in
    let () = match tc with
    | None -> ()
    | Some tc ->
      let tc = intern_type env tc in
      unify loc env t tc
    in
    let t = if is_value e then abstract_var env t else monomorphic t in
    ((na, e) :: el), ((na, t) :: p)
  in
  let (el, p) = List.fold_right fold el ([], []) in
  let nenv = List.fold_left (fun accu (na, t) -> push_name na t env) env p in
  let (e, t) = intern_rec nenv e in
  (GTacLet (false, el, e), t)
| CTacLet (loc, true, el, e) ->
  intern_let_rec env loc el e
| CTacTup (loc, []) ->
  (GTacTup [], GTypRef (t_unit, []))
| CTacTup (loc, el) ->
  let fold e (el, tl) =
    let (e, t) = intern_rec env e in
    (e :: el, t :: tl)
  in
  let (el, tl) = List.fold_right fold el ([], []) in
  (GTacTup el, GTypTuple tl)
| CTacArr (loc, []) ->
  let id = fresh_id env in
  (GTacArr [], GTypRef (t_int, [GTypVar id]))
| CTacArr (loc, e0 :: el) ->
  let (e0, t0) = intern_rec env e0 in
  let fold e el = intern_rec_with_constraint env e t0 :: el in
  let el = e0 :: List.fold_right fold el [] in
  (GTacArr el, GTypRef (t_array, [t0]))
| CTacLst (loc, []) ->
  let id = fresh_id env in
  (c_nil, GTypRef (t_list, [GTypVar id]))
| CTacLst (loc, e0 :: el) ->
  let (e0, t0) = intern_rec env e0 in
  let fold e el = c_cons (intern_rec_with_constraint env e t0) el in
  let el = c_cons e0 (List.fold_right fold el c_nil) in
  (el, GTypRef (t_list, [t0]))
| CTacCnv (loc, e, tc) ->
  let (e, t) = intern_rec env e in
  let tc = intern_type env tc in
  let () = unify loc env t tc in
  (e, tc)
| CTacSeq (loc, e1, e2) ->
  let (e1, t1) = intern_rec env e1 in
  let (e2, t2) = intern_rec env e2 in
  let () = check_elt_unit loc env t1 in
  (GTacLet (false, [Anonymous, e1], e2), t2)
| CTacCse (loc, e, pl) ->
  intern_case env loc e pl
| CTacRec (loc, fs) ->
  intern_record env loc fs
| CTacPrj (loc, e, proj) ->
  let pinfo = get_projection proj in
  let loc = loc_of_tacexpr e in
  let (e, t) = intern_rec env e in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (pinfo.pdata_type, params) in
  let () = unify loc env t exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  (GTacPrj (e, pinfo.pdata_indx), ret)
| CTacSet (loc, e, proj, r) ->
  let pinfo = get_projection proj in
  let () =
    if not pinfo.pdata_mutb then
      let (loc, _) = proj in
      user_err ~loc (str "Field is not mutable")
  in
  let subst = Array.init pinfo.pdata_prms (fun _ -> fresh_id env) in
  let params = Array.map_to_list (fun i -> GTypVar i) subst in
  let exp = GTypRef (pinfo.pdata_type, params) in
  let e = intern_rec_with_constraint env e exp in
  let substf i = GTypVar subst.(i) in
  let ret = subst_type substf pinfo.pdata_ptyp in
  let r = intern_rec_with_constraint env r ret in
  (GTacSet (e, pinfo.pdata_indx, r), GTypRef (t_unit, []))
| CTacExt (loc, ext) ->
  let open Genintern in
  let GenArg (Rawwit tag, _) = ext in
  let tpe = interp_ml_object tag in
  (** External objects do not have access to the named context because this is
      not stable by dynamic semantics. *)
  let genv = Global.env_of_context Environ.empty_named_context_val in
  let ist = empty_glob_sign genv in
  let ist = { ist with extra = Store.set ist.extra ltac2_env env } in
  let (_, ext) = Flags.with_option Ltac_plugin.Tacintern.strict_check (fun () -> generic_intern ist ext) () in
  (GTacExt ext, GTypRef (tpe.ml_type, []))

and intern_rec_with_constraint env e exp =
  let loc = loc_of_tacexpr e in
  let (e, t) = intern_rec env e in
  let () = unify loc env t exp in
  e

and intern_let_rec env loc el e =
  let fold accu ((loc, na), _, _) = match na with
  | Anonymous -> accu
  | Name id ->
    if Id.Set.mem id accu then
      user_err ~loc (str "Variable " ++ Id.print id ++ str " is bound several \
        times in this matching")
    else Id.Set.add id accu
  in
  let _ = List.fold_left fold Id.Set.empty el in
  let map env ((loc, na), t, e) =
    let id = fresh_id env in
    let env = push_name na (monomorphic (GTypVar id)) env in
    (env, (loc, na, t, e, id))
  in
  let (env, el) = List.fold_map map env el in
  let fold (loc, na, tc, e, id) (el, tl) =
    let loc_e = loc_of_tacexpr e in
    let (e, t) = intern_rec env e in
    let () =
      if not (is_rec_rhs e) then
        user_err ~loc:loc_e (str "This kind of expression is not allowed as \
          right-hand side of a recursive binding")
    in
    let () = unify loc env t (GTypVar id) in
    let () = match tc with
    | None -> ()
    | Some tc ->
      let tc = intern_type env tc in
      unify loc env t tc
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
  let todo ~loc () = user_err ~loc (str "Pattern not handled yet") in
  match get_pattern_kind env pl with
  | PKind_any ->
    let (pat, b) = List.hd pl in
    let na = match pat with
    | CPatAny _ -> Anonymous
    | CPatRef (_, (_, qid), _) -> Name (snd (repr_qualid qid))
    | _ -> assert false
    in
    let () = check_redundant_clause (List.tl pl) in
    let env = push_name na (monomorphic t) env in
    let (b, tb) = intern_rec env b in
    (GTacLet (false, [na, e'], b), tb)
  | PKind_empty ->
    let kn = check_elt_empty loc env t in
    let r = fresh_id env in
    (GTacCse (e', GCaseAlg kn, [||], [||]), GTypVar r)
  | PKind_tuple len ->
    begin match pl with
    | [] -> assert false
    | [CPatTup (_, []), b] ->
      let () = unify (loc_of_tacexpr e) env t (GTypRef (t_unit, [])) in
      let (b, tb) = intern_rec env b in
      (GTacCse (e', GCaseAlg t_unit, [|b|], [||]), tb)
    | [CPatTup (_, pl), b] ->
      let map = function
      | CPatAny _ -> Anonymous
      | CPatRef (loc, qid, []) ->
        begin match get_constructor env qid with
        | ArgVar (_, id) -> Name id
        | ArgArg _ -> todo ~loc ()
        end
      | p -> todo ~loc:(loc_of_patexpr p) ()
      in
      let ids = Array.map_of_list map pl in
      let tc = GTypTuple (List.map (fun _ -> GTypVar (fresh_id env)) pl) in
      let () = unify (loc_of_tacexpr e) env t tc in
      let (b, tb) = intern_rec env b in
      (GTacCse (e', GCaseTuple len, [||], [|ids, b|]), tb)
    | (p, _) :: _ -> todo ~loc:(loc_of_patexpr p) ()
    end
  | PKind_variant kn ->
    let subst, tc = fresh_reftype env kn in
    let () = unify (loc_of_tacexpr e) env t tc in
    let (params, def) = Tac2env.interp_type kn in
    let cstrs = match def with
    | GTydAlg c -> c
    | _ -> assert false
    in
    let count (const, nonconst) (c, args) = match args with
    | [] -> (succ const, nonconst)
    | _ :: _ -> (const, succ nonconst)
    in
    let nconst, nnonconst = List.fold_left count (0, 0) cstrs in
    let const = Array.make nconst None in
    let nonconst = Array.make nnonconst None in
    let ret = GTypVar (fresh_id env) in
    let rec intern_branch = function
    | [] -> ()
    | (pat, br) :: rem ->
      let tbr = match pat with
      | CPatAny _ ->
        let () = check_redundant_clause rem in
        let (br', brT) = intern_rec env br in
        (** Fill all remaining branches *)
        let fill (ncst, narg) (_, args) =
          if List.is_empty args then
            let () =
              if Option.is_empty const.(ncst) then const.(ncst) <- Some br'
            in
            (succ ncst, narg)
          else
            let () =
              if Option.is_empty const.(narg) then
                let ids = Array.map_of_list (fun _ -> Anonymous) args in
                nonconst.(narg) <- Some (ids, br')
            in
            (ncst, succ narg)
        in
        let _ = List.fold_left fill (0, 0) cstrs in
        brT
      | CPatRef (loc, qid, args) ->
        let data = match get_constructor env qid with
        | ArgVar _ -> todo ~loc ()
        | ArgArg (data, _) ->
          let () =
            let kn' = data.cdata_type in
            if not (KerName.equal kn kn') then
              invalid_pattern ~loc kn (GCaseAlg kn')
          in
          data
        in
        let get_id = function
        | CPatAny _ -> Anonymous
        | CPatRef (loc, qid, []) ->
          begin match get_constructor env qid with
          | ArgVar (_, id) -> Name id
          | ArgArg _ -> todo ~loc ()
          end
        | p -> todo ~loc:(loc_of_patexpr p) ()
        in
        let ids = List.map get_id args in
        let nids = List.length ids in
        let nargs = List.length data.cdata_args in
        let () =
          if not (Int.equal nids nargs) then error_nargs_mismatch loc nargs nids
        in
        let fold env id tpe =
          (** Instantiate all arguments *)
          let subst n = GTypVar subst.(n) in
          let tpe = subst_type subst tpe in
          push_name id (monomorphic tpe) env
        in
        let nenv = List.fold_left2 fold env ids data.cdata_args in
        let (br', brT) = intern_rec nenv br in
        let () =
          let index = data.cdata_indx in
          if List.is_empty args then
            if Option.is_empty const.(index) then const.(index) <- Some br'
            else warn_redundant_clause ~loc ()
          else
            let ids = Array.of_list ids in
            if Option.is_empty nonconst.(index) then nonconst.(index) <- Some (ids, br')
            else warn_redundant_clause ~loc ()
        in
        brT
      | CPatTup (loc, tup) ->
        invalid_pattern ~loc kn (GCaseTuple (List.length tup))
      in
      let () = unify (loc_of_tacexpr br) env ret tbr in
      intern_branch rem
    in
    let () = intern_branch pl in
    let map = function
    | None -> user_err ~loc (str "Unhandled match case") (** FIXME *)
    | Some x -> x
    in
    let const = Array.map map const in
    let nonconst = Array.map map nonconst in
    let ce = GTacCse (e', GCaseAlg kn, const, nonconst) in
    (ce, ret)

and intern_constructor env loc kn args =
  let cstr = interp_constructor kn in
  let nargs = List.length cstr.cdata_args in
  if Int.equal nargs (List.length args) then
    let subst = Array.init cstr.cdata_prms (fun _ -> fresh_id env) in
    let substf i = GTypVar subst.(i) in
    let types = List.map (fun t -> subst_type substf t) cstr.cdata_args in
    let ans = GTypRef (cstr.cdata_type, List.init cstr.cdata_prms (fun i -> GTypVar subst.(i))) in
    let map arg tpe = intern_rec_with_constraint env arg tpe in
    let args = List.map2 map args types in
    (GTacCst (cstr.cdata_type, cstr.cdata_indx, args), ans)
  else
    error_nargs_mismatch loc nargs (List.length args)

and intern_record env loc fs =
  let map ((loc, qid), e) =
    let proj = get_projection (loc, qid) in
    (loc, proj, e)
  in
  let fs = List.map map fs in
  let kn = match fs with
  | [] -> user_err ~loc (str "Cannot infer the corresponding record type")
  | (_, proj, _) :: _ -> proj.pdata_type
  in
  let params, typdef = match Tac2env.interp_type kn with
  | n, GTydRec def -> n, def
  | _ -> assert false
  in
  let subst = Array.init params (fun _ -> fresh_id env) in
  (** Set the answer [args] imperatively *)
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
        user_err ~loc (str "Field " ++ Id.print name ++ str " is defined \
          several times")
    else
      user_err ~loc (str "Field " ++ (*KerName.print knp ++*) str " does not \
        pertain to record definition " ++ KerName.print pinfo.pdata_type)
  in
  let () = List.iter iter fs in
  let () = match Array.findi (fun _ o -> Option.is_empty o) args with
  | None -> ()
  | Some i ->
    let (field, _, _) = List.nth typdef i in
    user_err ~loc (str "Field " ++ Id.print field ++ str " is undefined")
  in
  let args = Array.map_to_list Option.get args in
  let tparam = List.init params (fun i -> GTypVar subst.(i)) in
  (GTacCst (kn, 0, args), GTypRef (kn, tparam))

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

let intern e =
  let env = empty_env () in
  let (e, t) = intern_rec env e in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let t = normalize env (count, vars) t in
  (e, (!count, t))

let intern_typedef self (ids, t) : glb_quant_typedef =
  let env = { (empty_env ()) with env_rec = self } in
  (** Initialize type parameters *)
  let map id = get_alias id env in
  let ids = List.map map ids in
  let count = ref (List.length ids) in
  let vars = ref UF.Map.empty in
  let iter n id = vars := UF.Map.add id (GTypVar n) !vars in
  let () = List.iteri iter ids in
  (** Do not accept unbound type variables *)
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
    (count, GTydAlg constrs)
  | CTydRec fields ->
    let map (c, mut, t) = (c, mut, intern t) in
    let fields = List.map map fields in
    (count, GTydRec fields)

let intern_open_type t =
  let env = empty_env () in
  let t = intern_type env t in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let t = normalize env (count, vars) t in
  (!count, t)

(** Kernel substitution *)

open Mod_subst

let rec subst_type subst t = match t with
| GTypVar _ -> t
| GTypArrow (t1, t2) ->
  let t1' = subst_type subst t1 in
  let t2' = subst_type subst t2 in
  if t1' == t1 && t2' == t2 then t
  else GTypArrow (t1', t2')
| GTypTuple tl ->
  let tl'= List.smartmap (fun t -> subst_type subst t) tl in
  if tl' == tl then t else GTypTuple tl'
| GTypRef (kn, tl) ->
  let kn' = subst_kn subst kn in
  let tl' = List.smartmap (fun t -> subst_type subst t) tl in
  if kn' == kn && tl' == tl then t else GTypRef (kn', tl')

let subst_case_info subst ci = match ci with
| GCaseAlg kn ->
  let kn' = subst_kn subst kn in
  if kn' == kn then ci else GCaseAlg kn'
| GCaseTuple _ -> ci

let rec subst_expr subst e = match e with
| GTacAtm _ | GTacVar _ | GTacPrm _ -> e
| GTacRef kn -> GTacRef (subst_kn subst kn)
| GTacFun (ids, e) -> GTacFun (ids, subst_expr subst e)
| GTacApp (f, args) ->
  GTacApp (subst_expr subst f, List.map (fun e -> subst_expr subst e) args)
| GTacLet (r, bs, e) ->
  let bs = List.map (fun (na, e) -> (na, subst_expr subst e)) bs in
  GTacLet (r, bs, subst_expr subst e)
| GTacTup el ->
  GTacTup (List.map (fun e -> subst_expr subst e) el)
| GTacArr el ->
  GTacArr (List.map (fun e -> subst_expr subst e) el)
| GTacCst (kn, n, el) -> 
  GTacCst (subst_kn subst kn, n, List.map (fun e -> subst_expr subst e) el)
| GTacCse (e, ci, cse0, cse1) ->
  let cse0' = Array.map (fun e -> subst_expr subst e) cse0 in
  let cse1' = Array.map (fun (ids, e) -> (ids, subst_expr subst e)) cse1 in
  let ci' = subst_case_info subst ci in
  GTacCse (subst_expr subst e, ci', cse0', cse1')
| GTacPrj (e, p) as e0 ->
  let e' = subst_expr subst e in
  if e' == e then e0 else GTacPrj (e', p)
| GTacSet (e, p, r) as e0 ->
  let e' = subst_expr subst e in
  let r' = subst_expr subst r in
  if e' == e && r' == r then e0 else GTacSet (e', p, r')
| GTacExt ext ->
  let ext' = Genintern.generic_substitute subst ext in
  if ext' == ext then e else GTacExt ext'

let subst_typedef subst e = match e with
| GTydDef t ->
  let t' = Option.smartmap (fun t -> subst_type subst t) t in
  if t' == t then e else GTydDef t'
| GTydAlg constrs ->
  let map (c, tl as p) =
    let tl' = List.smartmap (fun t -> subst_type subst t) tl in
    if tl' == tl then p else (c, tl')
  in
  let constrs' = List.smartmap map constrs in
  if constrs' == constrs then e else GTydAlg constrs'
| GTydRec fields ->
  let map (c, mut, t as p) =
    let t' = subst_type subst t in
    if t' == t then p else (c, mut, t')
  in
  let fields' = List.smartmap map fields in
  if fields' == fields then e else GTydRec fields'

let subst_quant_typedef subst (prm, def as qdef) =
  let def' = subst_typedef subst def in
  if def' == def then qdef else (prm, def')

let subst_type_scheme subst (prm, t as sch) =
  let t' = subst_type subst t in
  if t' == t then sch else (prm, t')
