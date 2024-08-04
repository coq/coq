(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Context
open CoqSharingAnalyser

(* TODO explain how this works *)

module Self = struct

type t = {
  self : constr;
  kind : (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term;
  isRel : int (* 0 -> not a rel, otherwise unique identifier of that binder *);
  unbound_rels : int SList.t;
  hash : int;
  mutable refcount : int;
}

let equal a b =
  a.isRel == b.isRel
  && hasheq_kind a.kind b.kind

let hash x = x.hash

end

include Self

let raw_equal a ~isRel ~kind =
  a.isRel == isRel
  && hasheq_kind a.kind kind

let self x = x.self

let refcount x = x.refcount

module Tbl = struct
  type key = t

  (* The API looks like Hashtbl but implemented using Int.Map ref.

     We don't use Hashtbl for 2 reasons:
     - to provide the pre-hashconsing leaf lookup (not sure why it's so fast but it seems to be)
       (although note we could do this with Hashtbl by using something like
       [type key = Real of t | Fake of int (* hash *) * (t -> bool)],
       equality between [Real] and [Fake] uses the predicate in [Fake],
       wrap [add] so that we only add [Real] keys,
       then [raw_find] is [Hashtbl.find_opt] using [Fake].)

     - for unclear reasons Int.Map ref is dramatically faster on an artificial example
       (balanced binary tree whose leaves are all different primitive ints,
        such that there is no sharing).
       It is a bit slower in the real world.
       It seems that hashtbl produces overly large buckets which then need to be linearly scanned.
       hconsing doesn't seem to have this problem,
       perhaps because of differences between hashtbl and our hashset implementation. *)
  type 'a t = (key * 'a) list Int.Map.t ref

  let create _ = ref Int.Map.empty

  let add tbl key v =
    tbl := Int.Map.update key.hash (function
        | None -> Some [(key,v)]
        | Some l -> Some ((key,v)::l))
        !tbl

  let raw_find tbl h p =
    match Int.Map.find_opt h !tbl with
    | None -> None
    | Some l -> List.find_map (fun (k,v) -> if p k then Some v else None) l

  let find_opt tbl key =
    match Int.Map.find_opt key.hash !tbl with
    | None -> None
    | Some l ->
      List.find_map (fun (k',v) ->
          if equal key k' then Some v else None)
        l

  type stats = {
    hashes : int;
    bindings : int;
    most_collisions : int;
  }

  let empty_stats = {
    hashes = 0;
    bindings = 0;
    most_collisions = 0;
  }

  let stats tbl =
    Int.Map.fold (fun _ l acc ->
        let len = List.length l in
        {
          hashes = acc.hashes + 1;
          bindings = acc.bindings + len;
          most_collisions = max acc.most_collisions len;
        }
      )
      !tbl
      empty_stats

end

module UBRelKey = struct
  type t = int SList.t
  let compare x y = SList.compare Int.compare x y
end

module UBRelMap = Map.Make(UBRelKey)

type seen = {
  seen_self : Constr.t;
  data : t UBRelMap.t;
}

type local_env = {
  (* only used for globals, rel context is not correct *)
  globals : Environ.env;
  (* unique identifiers for each binder crossed *)
  rels : int Range.t;
  (* global counter *)
  cnt : int ref;
  (* how many unknown_rel we have seen *)
  unknown_cnt : int ref;
  (* map from uids to binders (unknown_rels are not present) *)
  uid_revmap : (t option * t) Int.Map.t ref;
  assum_uids : int Tbl.t;
  (* the surrounding table is for the body, the inner table for the type *)
  letin_uids : int Tbl.t Tbl.t;
  (* sharing info (needs to be optional to handle the Case binders,
     also if we want a mode which doesn't exploit sharing,
     also should make jscoq devs's work easier).
     The [int] is the id of this restart, for debugging.
  *)
  sharing_info : SharingAnalyser.analysis ref option;
  (* already seen terms according to sharing info

     XXX now that we have 1-bit refcount on sharing does it still make
     sense to use an array instead of int map? since with the refcount
     we won't be filling every cell. *)
  shared_seen : seen option array;
}

let init_seen = function
  | None -> [||]
  | Some info ->
    Array.make (SharingAnalyser.max_index info + 1) None

let empty_env env info = {
  globals = env;
  rels = Range.empty;
  cnt = ref 0;
  unknown_cnt = ref 0;
  uid_revmap = ref Int.Map.empty;
  assum_uids = Tbl.create 47;
  letin_uids = Tbl.create 47;
  sharing_info = Option.map ref info;
  shared_seen = init_seen info;
}

(* still used in fixpoint *)
let push_unknown_rel env =
  incr env.cnt;
  incr env.unknown_cnt;
  { env with rels = Range.cons !(env.cnt) env.rels }

let push_assum t env =
  let uid = match Tbl.find_opt env.assum_uids t with
  | Some uid -> uid
  | None ->
    incr env.cnt;
    let uid = !(env.cnt) in
    Tbl.add env.assum_uids t uid;
    env.uid_revmap := Int.Map.add uid (None,t) !(env.uid_revmap);
    uid
  in
  { env with rels = Range.cons uid env.rels }

let push_rec ts env =
  (* handling the lifting for mutual fixpoints doesn't seem worth the effort *)
  Array.fold_left_i (fun i env t ->
      if i = 0 then push_assum t env
      else push_unknown_rel env)
    env
    ts

let push_letin ~body ~typ env =
  let uid = match Tbl.find_opt env.letin_uids body with
    | Some tbl -> begin match Tbl.find_opt tbl typ with
        | Some uid -> uid
        | None ->
          incr env.cnt;
          let uid = !(env.cnt) in
          Tbl.add tbl typ uid;
          env.uid_revmap := Int.Map.add uid (Some body,typ) !(env.uid_revmap);
          uid
      end
    | None ->
      incr env.cnt;
      let uid = !(env.cnt) in
      let tbl = Tbl.create 3 in
      Tbl.add tbl typ uid;
      Tbl.add env.letin_uids body tbl;
      env.uid_revmap := Int.Map.add uid (Some body,typ) !(env.uid_revmap);
      uid
  in
  { env with rels = Range.cons uid env.rels }

module RelDecl = Context.Rel.Declaration

let push_decl d env = match d with
  | RelDecl.LocalAssum (_,t) -> push_assum t env
  | RelDecl.LocalDef (_,body,typ) -> push_letin ~body ~typ env

let hash_annot = hash_annot Name.hash

let hash_array hashf a = Array.fold_left (fun hash x -> Hashset.Combine.combine hash (hashf x)) 0 a

let hash_kind = let open Hashset.Combine in function
  | Var i -> combinesmall 1 (Id.hash i)
  | Sort s -> combinesmall 2 (Sorts.hash s)
  | Cast (c,k,t) -> combinesmall 3 (combine3 c.hash (hash_cast_kind k) t.hash)
  | Prod (na,t,c) -> combinesmall 4 (combine3 (hash_annot na) t.hash c.hash)
  | Lambda (na,t,c) -> combinesmall 5 (combine3 (hash_annot na) t.hash c.hash)
  | LetIn (na,b,t,c) -> combinesmall 6 (combine4 (hash_annot na) b.hash t.hash c.hash)
  | App (h,args) -> combinesmall 7 (Array.fold_left (fun hash c -> combine hash c.hash) h.hash args)
  | Evar _ -> assert false
  | Const (c,u) -> combinesmall 9 (combine (Constant.SyntacticOrd.hash c) (UVars.Instance.hash u))
  | Ind (ind,u) -> combinesmall 10 (combine (Ind.SyntacticOrd.hash ind) (UVars.Instance.hash u))
  | Construct (c,u) -> combinesmall 11 (combine (Construct.SyntacticOrd.hash c) (UVars.Instance.hash u))
  | Case (_,u,pms,(p,_),_,c,bl) ->
    let hash_ctx (bnd,c) =
      Array.fold_left (fun hash na -> combine (hash_annot na) hash) c.hash bnd
    in
    let hpms = hash_array hash pms in
    let hbl = hash_array hash_ctx bl in
    let h = combine5 (UVars.Instance.hash u)
        c.hash hpms (hash_ctx p) hbl
    in
    combinesmall 12 h
  | Fix (_,(lna,tl,bl)) ->
    combinesmall 13 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | CoFix (_,(lna,tl,bl)) ->
    combinesmall 14 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | Meta _ -> assert false
  | Rel n -> combinesmall 16 n
  | Proj (p,_,c) -> combinesmall 17 (combine (Projection.SyntacticOrd.hash p) c.hash)
  | Int i -> combinesmall 18 (Uint63.hash i)
  | Float f -> combinesmall 19 (Float64.hash f)
  | String s -> combinesmall 20 (Pstring.hash s)
  | Array (u,t,def,ty) -> combinesmall 21 (combine4 (UVars.Instance.hash u) (hash_array hash t) def.hash ty.hash)

let kind_to_constr = function
  | Rel n -> mkRel n
  | Var i -> mkVar i
  | Meta _ | Evar _ -> assert false
  | Sort s -> mkSort s
  | Cast (c,k,t) -> mkCast (c.self,k,t.self)
  | Prod (na,t,c) -> mkProd (na,t.self,c.self)
  | Lambda (na,t,c) -> mkLambda (na,t.self,c.self)
  | LetIn (na,b,t,c) -> mkLetIn (na,b.self,t.self,c.self)
  | App (h,args) -> mkApp (h.self, Array.map self args)
  | Const cu -> mkConstU cu
  | Ind iu -> mkIndU iu
  | Construct cu -> mkConstructU cu
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let to_ctx (bnd,c) = bnd, c.self in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert x -> CaseInvert {indices=Array.map self x.indices}
    in
    mkCase (ci,u,Array.map self pms,(to_ctx p,r),iv,c.self,Array.map to_ctx bl)
  | Fix (ln,(lna,tl,bl)) ->
    mkFix (ln,(lna,Array.map self tl,Array.map self bl))
  | CoFix (ln,(lna,tl,bl)) ->
    mkCoFix (ln,(lna,Array.map self tl,Array.map self bl))
  | Proj (p,r,c) -> mkProj (p,r,c.self)
  | Int i -> mkInt i
  | Float f -> mkFloat f
  | String s -> mkString s
  | Array (u,t,def,ty) -> mkArray (u,Array.map self t,def.self,ty.self)

let hcons_inplace f a = Array.iteri (fun i x -> Array.unsafe_set a i (f x)) a

let rec pop_unbound_rels n l =
  if n = 0 then l else match l with
    | SList.Nil -> l
    | SList.Cons (_,tl) -> pop_unbound_rels (n-1) tl
    | SList.Default (m,tl) ->
      if n < m then SList.defaultn (m-n) tl
      else pop_unbound_rels (n-m) tl

let rec combine_unbound_rels l1 l2 =
  if l1 == l2 then l1 else match l1, l2 with
  | SList.Nil, _ -> l2
  | _, SList.Nil -> l1
  | SList.Cons (x,tl1), SList.Cons (y,tl2) ->
    assert (Int.equal x y);
    let tl = combine_unbound_rels tl1 tl2 in
    if tl == tl1 then l1 else if tl == tl2 then l2 else SList.cons x tl
  | SList.Cons (x,tl1), SList.Default (n,tl2) ->
    let tl = combine_unbound_rels tl1 (SList.defaultn (n-1) tl2) in
    if tl == tl1 then l1 else SList.cons x tl
  | SList.Default (n,tl1), SList.Cons (y,tl2) ->
    let tl = combine_unbound_rels (SList.defaultn (n-1) tl1) tl2 in
    if tl == tl2 then l2 else SList.cons y tl
  | SList.Default (n,tl1), SList.Default (m,tl2) ->
    let n, m, tl1, tl2, l1 = if n < m then n, m, tl1, tl2, l1 else m, n, tl2, tl1, l2 in
    let tl = combine_unbound_rels tl1 (SList.defaultn (m-n) tl2) in
    if tl == tl1 then l1 else SList.defaultn n tl

let kind_unbound_rels = function
  | Rel _ -> assert false
  | Var _ | Sort _ | Const _ | Construct _ | Ind _ | Int _ | Float _ | String _ -> SList.empty
  | Meta _ | Evar _ -> assert false
  | Cast (c1,_,c2) -> combine_unbound_rels c1.unbound_rels c2.unbound_rels
  | Prod (_,c1,c2) | Lambda (_,c1,c2) ->
    combine_unbound_rels c1.unbound_rels (pop_unbound_rels 1 c2.unbound_rels)
  | LetIn (_,c1,c2,c3) ->
    let rels = combine_unbound_rels c1.unbound_rels c2.unbound_rels in
    combine_unbound_rels rels (pop_unbound_rels 1 c3.unbound_rels)
  | App (h,args) ->
    Array.fold_left (fun rels arg -> combine_unbound_rels rels arg.unbound_rels) h.unbound_rels args
  | Case (_,_,pms,(p,_),iv,c,bl) ->
    let fold_ctx rels (bnd,c) =
      combine_unbound_rels rels (pop_unbound_rels (Array.length bnd) c.unbound_rels)
    in
    let rels = c.unbound_rels in
    let rels = match iv with
      | NoInvert -> rels
      | CaseInvert {indices} ->
        Array.fold_left (fun rels i -> combine_unbound_rels rels i.unbound_rels) rels indices
    in
    let rels = Array.fold_left (fun rels pm -> combine_unbound_rels rels pm.unbound_rels) rels pms in
    let rels = fold_ctx rels p in
    let rels = Array.fold_left fold_ctx rels bl in
    rels
  | Fix (_,recdef) | CoFix (_,recdef) ->
    let nas,tys,bdys = recdef in
    let rels = Array.fold_left (fun rels ty ->
        combine_unbound_rels rels ty.unbound_rels)
        SList.empty
        tys
    in
    Array.fold_left (fun rels bdy ->
        combine_unbound_rels rels (pop_unbound_rels (Array.length nas) bdy.unbound_rels))
      rels
      bdys
  | Proj (_,_,c) -> c.unbound_rels
  | Array (_,elems,def,ty) ->
    let rels = combine_unbound_rels def.unbound_rels ty.unbound_rels in
    Array.fold_left (fun rels elem -> combine_unbound_rels rels elem.unbound_rels) rels elems

(** [diff_rels main other] produces the sublist of [main] which s different from [other]. *)
let rec diff_rels main other =
  let open SList in
  match main, other with
  | Nil, Nil -> SList.empty
  | Cons (x,tl), Cons (y,tl') ->
    let tl0 = diff_rels tl tl' in
    if Int.equal x y then begin match tl0 with
      | Nil -> SList.empty
      | Cons _ | Default _ -> SList.default tl0
    end
    else if tl0 == tl then main else SList.cons x tl0
  | Default (n,tl), Default (m,tl') ->
    assert (Int.equal n m);
    let tl0 = diff_rels tl tl' in
    begin match tl0 with
    | Nil -> SList.empty
    | Cons _ | Default _ ->
      if tl0 == tl then main else SList.defaultn n tl0
    end
  | (Nil | Cons _ | Default _), _ -> assert false

let is_identity_on subst c =
  let rec aux subst ubrels =
    let open SList in
    match subst, ubrels with
    | Nil, _ -> (* rest of ubrels are not modified *) true
    | _, Nil -> (* no more ubrels to modify *) true
    | Cons (x,_), Cons (y, _) ->
      assert (not @@ Int.equal x y);
      false
    | _, Default (m, tl') -> aux (pop_unbound_rels m subst) tl'
    | Default (n, tl), _ -> aux tl (pop_unbound_rels n ubrels)
  in
  aux subst c.unbound_rels

let incr_refcount v = v.refcount <- v.refcount + 1

let make ?unbound_rels tbl local_env self kind =
  let hash = hash_kind kind in
  let isRel, hash = match kind with
    | Rel n ->
      let uid = Range.get local_env.rels (n-1) in
      assert (uid <> 0);
      uid, Hashset.Combine.combine uid hash
    | _ -> 0, hash
  in
  match Tbl.raw_find tbl hash (fun c' -> raw_equal c' ~isRel ~kind) with
  | Some c' -> c'.refcount <- c'.refcount + 1; c'
  | None ->
    let unbound_rels = match unbound_rels with
      | Some v -> v
      | None -> match kind with
        | Rel n -> SList.defaultn (n-1) (SList.cons isRel SList.empty)
        | _ -> kind_unbound_rels kind
    in
    let c =
      let self' = kind_to_constr kind in
      let self = if hasheq_kind (Constr.kind self') (Constr.kind self) then self else self' in
      { self; kind; hash; isRel; unbound_rels; refcount = 1 }
    in
    Tbl.add tbl c c; c

let push1_subst henv subst ubrels =
  let open SList in
  match ubrels with
  | Nil | Default _ -> SList.default subst
  | Cons (x,_) ->
    let y = Range.hd henv.rels in
    if Int.equal x y then SList.default subst
    else SList.cons y subst

(* v tells which rels are bound *)
let ubrels_from_env (type a) local_env (v:a SList.t) =
  let rec aux local_env rels = match rels with
    | SList.Nil -> SList.empty
    | SList.Cons (_,tl) ->
      SList.cons (Range.hd local_env)
        (aux (Range.tl local_env) tl)
    | SList.Default (n,tl) ->
      SList.defaultn n (aux (Range.skipn n local_env) tl)
  in
  aux local_env.rels v

let rec change_bound cache tbl henv subst c =
  if is_identity_on subst c then (incr_refcount c; c)
  else if c.refcount = 1 then
      let kind = change_bound_rec cache tbl henv subst c in
      make tbl henv c.self kind
  else
    let c_cache = Option.default UBRelMap.empty (Tbl.find_opt cache c) in
    let key = ubrels_from_env henv c.unbound_rels in
    match UBRelMap.find_opt key c_cache with
    | Some v -> incr_refcount v; v
    | None ->
      let kind = change_bound_rec cache tbl henv subst c in
      let v = make tbl henv c.self kind in
      Tbl.add cache c (UBRelMap.add key v c_cache);
      v

and change_bound_rec cache tbl henv subst c =
  match c.kind with
  | Rel _ as k ->
    (* the actual change happens in [make] when recomputing unbound_rels *)
    k
  | Var _ | Const _ | Ind _ | Construct _ | Sort _
  | Meta _ | Int _ | Float _ | String _ ->
    (* closed -> always is_identity_on = true *)
    assert false
  | Evar _ -> assert false
  | Cast (c1,k,c2) ->
    let c1 = change_bound cache tbl henv subst c1 in
    let c2 = change_bound cache tbl henv subst c2 in
    Cast (c1,k,c2)
  | Prod (na,t,c) ->
    let t = change_bound cache tbl henv subst t in
    let henv = push_assum t henv in
    let subst = push1_subst henv subst c.unbound_rels in
    let c = change_bound cache tbl henv subst c in
    Prod (na,t,c)
  | Lambda (na,t,c) ->
    let t = change_bound cache tbl henv subst t in
    let henv = push_assum t henv in
    let subst = push1_subst henv subst c.unbound_rels in
    let c = change_bound cache tbl henv subst c in
    Lambda (na,t,c)
  | LetIn (na,b,t,c) ->
    let b = change_bound cache tbl henv subst b in
    let t = change_bound cache tbl henv subst t in
    let henv = push_letin ~body:b ~typ:t henv in
    let subst = push1_subst henv subst c.unbound_rels in
    let c = change_bound cache tbl henv subst c in
    LetIn (na,b,t,c)
  | App (h,args) ->
    let h = change_bound cache tbl henv subst h in
    let args = CArray.Smart.map (change_bound cache tbl henv subst) args in
    App (h,args)
  | Case (ci,u,pms,(p,r as pr),iv,c,bl) ->
    let pms = CArray.Smart.map (change_bound cache tbl henv subst) pms in
    let change_in_ctx (bnd, c) =
      let henv, subst = Array.fold_left_i (fun i (henv,subst) _ ->
          let open SList in
          match pop_unbound_rels (Array.length bnd - i - 1) c.unbound_rels with
          | Nil | Default _ ->
            (* unused binder *)
            { henv with rels = Range.cons (-1) henv.rels }, SList.default subst
          | Cons (x, _) as ubrels ->
            let t = Int.Map.get x !(henv.uid_revmap) in
            let t =
              let f x = change_bound cache tbl henv subst x in
              Option.map f (fst t), f (snd t)
            in
            let henv = match t with
              | (Some body, typ) -> push_letin ~body ~typ henv
              | (None, typ) -> push_assum typ henv
            in
            let subst = push1_subst henv subst ubrels in
            henv, subst)
          (henv, subst)
          bnd
      in
      bnd, change_bound cache tbl henv subst c
    in
    let pr =
      let p' = change_in_ctx p in
      if p' == p then pr else p',r
    in
    let iv = map_invert (change_bound cache tbl henv subst) iv in
    let c = change_bound cache tbl henv subst c in
    let bl = CArray.Smart.map change_in_ctx bl in
    Case (ci,u,pms,pr,iv,c,bl)
  | Fix (x,v) -> Fix (x, change_bound_recdef cache tbl henv subst v)
  | CoFix (x,v) -> CoFix (x, change_bound_recdef cache tbl henv subst v)
  | Proj (p,r,c) ->
    let c = change_bound cache tbl henv subst c in
    Proj (p,r,c)
  | Array (u,elems,def,ty) ->
    let elems = CArray.Smart.map (change_bound cache tbl henv subst) elems in
    let def = change_bound cache tbl henv subst def in
    let ty = change_bound cache tbl henv subst ty in
    Array (u,elems,def,ty)

and change_bound_recdef cache tbl henv subst (na,tl,bl) =
  let tl' = CArray.Smart.map (change_bound cache tbl henv subst) tl in
  let ubrels_orig_bdys = Array.fold_left (fun acc c -> combine_unbound_rels acc c.unbound_rels)
      SList.empty
      bl
  in
  let henv, subst = CArray.fold_left_i (fun i (henv,subst) t' ->
      let ubrels = pop_unbound_rels (Array.length tl - i - 1) ubrels_orig_bdys in
      let open SList in
      match ubrels with
      | Nil | Default _ ->
        (* ith (co)fixpoint not used in the bodies (rare: not actually recursive fixpoints but ok) *)
        { henv with rels = Range.cons (-1) henv.rels }, SList.default subst
      | Cons (x, _) ->
        if t' == tl.(i) then
          (* unchanged binding even if it used unknown_rel *)
          { henv with rels = Range.cons x henv.rels },
          SList.default subst
        else if Int.equal i 0 then
          (* no need to lift *)
          let henv = push_assum t' henv in
          henv, push1_subst henv subst ubrels
        else
          let henv = push_unknown_rel henv in
          henv, SList.cons (Range.hd henv.rels) subst)
      (henv, subst)
      tl'
  in
  let bl = CArray.Smart.map (change_bound cache tbl henv subst) bl in
  (na,tl',bl)

let of_kind_nohashcons = function
  | App (c, [||]) -> c
  | kind ->
  let self = kind_to_constr kind in
  let hash = hash_kind kind in
  let () = match kind with
    | Rel _ -> assert false
    | _ -> ()
  in
  let unbound_rels = kind_unbound_rels kind in
  { self; kind; hash; isRel = 0; unbound_rels; refcount = 1 }

let eq_leaf c c' = match kind c, c'.kind with
  | Var i, Var i' -> Id.equal i i'
  | Const (c,u), Const (c',u') -> Constant.SyntacticOrd.equal c c' && UVars.Instance.equal u u'
  | Ind (i,u), Ind (i',u') -> Ind.SyntacticOrd.equal i i' && UVars.Instance.equal u u'
  | Construct (c,u), Construct (c',u') -> Construct.SyntacticOrd.equal c c' && UVars.Instance.equal u u'
  | _ -> false

let nonrel_leaf tbl c = match kind c with
  | Rel _ -> None
  | Var _ | Const _ | Ind _ | Construct _ as k ->
    let h = hash_kind k in
    Tbl.raw_find tbl h (fun c' -> eq_leaf c c')
  | _ -> None

let dbg_trace = CDebug.create ~name:"hconstr-trace" ()

type sharing_info =
  | Unshared
  | Fresh of {
      idx : int;
    }
  | Seen of t

let sharing_info_core tbl local_env this_info c =
  match this_info with
  | SharingAnalyser.Unshared this ->
    dbg_trace Pp.(fun () -> str "Unshared " ++ int this);
    Unshared
  | SharingAnalyser.Fresh this ->
    dbg_trace Pp.(fun () -> str "Fresh " ++ int this);
    Fresh {idx=this}
  | SharingAnalyser.Seen this ->
    dbg_trace Pp.(fun () -> str "Seen " ++ int this);
    match local_env.shared_seen.(this) with
    | None ->
      (* circular value? *)
      assert false
    | Some seen ->
      if c != seen.seen_self
      then CErrors.anomaly Pp.(str "hconstr sharing_info mismatch at idx " ++ int this);
      let key', v' = UBRelMap.choose seen.data in
      let key = ubrels_from_env local_env key' in
      match UBRelMap.find_opt key seen.data with
      | None ->
        dbg_trace Pp.(fun () -> str"change_bound");
        let v = change_bound (Tbl.create()) tbl local_env (diff_rels key key') v' in
        let () =
          local_env.shared_seen.(this) <-
            Some { seen with data = UBRelMap.add key v seen.data }
        in
        Seen v
      | Some v ->
        Seen v

let sharing_info tbl local_env c =
  match local_env.sharing_info with
  | None -> None
  | Some info ->
    let _debug = mk_debug !info c in
    let next, this_info = SharingAnalyser.step !info in
    info := next;
    match kind c with
    | Rel _ ->
      (* Skip rels, doing [of_constr_fresh] directly seems as efficient. *)
      None
    | _ ->
      Some (sharing_info_core tbl local_env this_info c)

let steps = ref 0

let rec of_constr tbl local_env c =
  incr steps;
  match sharing_info tbl local_env c with
  | None | Some Unshared -> of_constr_fresh tbl local_env ~unbound_rels:None c
  | Some (Fresh {idx}) ->
    let v = of_constr_fresh tbl local_env ~unbound_rels:None c in
    let () =
      local_env.shared_seen.(idx) <-
        (* add [c] NOT [v.self] otherwise we will get false positive mismatch errors *)
        Some {
          seen_self = c;
          data = UBRelMap.singleton v.unbound_rels v;
        }
    in
    v
  | Some (Seen v) -> v.refcount <- v.refcount + 1; v

and of_constr_fresh tbl local_env ~unbound_rels c =
  match nonrel_leaf tbl c with
  | Some v -> v (* v.refcount <- v.refcount + 1? *)
  | None ->
    let kind = of_constr_aux tbl local_env c in
    make ?unbound_rels tbl local_env c kind

and of_constr_aux tbl local_env c =
  match kind c with
  | Var i ->
    let i = Id.hcons i in
    Var i
  | Rel _ as t -> t
  | Sort s ->
    let s = Sorts.hcons s in
    Sort s
  | Cast (c,k,t) ->
    let c = of_constr tbl local_env c in
    let t = of_constr tbl local_env t in
    Cast (c, k, t)
  | Prod (na,t,c) ->
    let na = hcons_annot na in
    let t = of_constr tbl local_env t in
    let c = of_constr tbl (push_assum t local_env) c in
    Prod (na, t, c)
  | Lambda (na, t, c) ->
    let na = hcons_annot na in
    let t = of_constr tbl local_env t in
    let c = of_constr tbl (push_assum t local_env) c in
    Lambda (na,t,c)
  | LetIn (na,b,t,c) ->
    let na = hcons_annot na in
    let b = of_constr tbl local_env b in
    let t = of_constr tbl local_env t in
    let c = of_constr tbl (push_letin ~body:b ~typ:t local_env) c in
    LetIn (na,b,t,c)
  | App (h,args) ->
    let h = of_constr tbl local_env h in
    let args = Array.map (of_constr tbl local_env) args in
    App (h, args)
  | Evar _ -> CErrors.anomaly Pp.(str "evar in typeops")
  | Meta _ -> CErrors.anomaly Pp.(str "meta in typeops")
  | Const (c,u) ->
    let c = hcons_con c in
    let u = UVars.Instance.hcons u in
    Const (c,u)
  | Ind (ind,u) ->
    let ind = hcons_ind ind in
    let u = UVars.Instance.hcons u in
    Ind (ind,u)
  | Construct (c,u) ->
    let c = hcons_construct c in
    let u = UVars.Instance.hcons u in
    Construct (c,u)
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let pctx, blctx =
      let specif = Inductive.lookup_mind_specif local_env.globals ci.ci_ind in
      let pctx = Inductive.expand_arity specif (ci.ci_ind,u) pms (fst p) in
      let blctx = Inductive.expand_branch_contexts specif u pms bl in
      pctx, blctx
    in
    let of_ctx (bnd, c) bnd' =
      assert (Array.length bnd = List.length bnd');
      let () = hcons_inplace hcons_annot bnd in
      let local_env = push_rel_context tbl local_env bnd' in
      let c = of_constr tbl local_env c in
      bnd, c
    in
    let ci = hcons_caseinfo ci in
    let u = UVars.Instance.hcons u in
    let pms = Array.map (of_constr tbl local_env) pms in
    let p = of_ctx p pctx in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert {indices} -> CaseInvert {indices=Array.map (of_constr tbl local_env) indices}
    in
    let c = of_constr tbl local_env c in
    let bl = Array.map2 of_ctx bl blctx in
    Case (ci,u,pms,(p,r),iv,c,bl)
  | Fix (ln,(lna,tl,bl)) ->
    let () = hcons_inplace hcons_annot lna in
    let tl = Array.map (of_constr tbl local_env) tl in
    let body_env = push_rec tl local_env in
    let bl = Array.map (of_constr tbl body_env) bl in
    Fix (ln,(lna,tl,bl))
  | CoFix (ln,(lna,tl,bl)) ->
    let () = hcons_inplace hcons_annot lna in
    let tl = Array.map (of_constr tbl local_env) tl in
    let body_env = push_rec tl local_env in
    let bl = Array.map (of_constr tbl body_env) bl in
    CoFix (ln,(lna,tl,bl))
  | Proj (p,r,c) ->
    let p = Projection.hcons p in
    let c = of_constr tbl local_env c in
    Proj (p,r,c)
  | Int _ as t -> t
  | Float _ as t -> t
  | String _ as t -> t
  | Array (u,t,def,ty) ->
    let u = UVars.Instance.hcons u in
    let t = Array.map (of_constr tbl local_env) t in
    let def = of_constr tbl local_env def in
    let ty = of_constr tbl local_env ty in
    Array (u,t,def,ty)

and push_rel_context tbl local_env ctx =
  List.fold_right (fun d local_env ->
      let d = RelDecl.map_constr_het (fun r -> r)
          (of_constr tbl { local_env with sharing_info = None })
          d
      in
      push_decl d local_env)
    ctx
    local_env

let dbg = CDebug.create ~name:"hconstr" ()

let dbg_sharing = CDebug.create ~name:"constrsharing" ()

let tree_size c =
  let rec aux size c =
    Constr.fold aux (size+1) c
  in
  aux 0 c


(* WARNING very slow *)
let debug_check c info =
  let info = ref info in
  let seen = ref [] in
  let cnt = ref 0 in
  let rec aux c =
    let next_info, this = SharingAnalyser.step !info in
    info := next_info;
    match this, List.find_opt (fun (c',_) -> c == c') !seen with
    | SharingAnalyser.Seen i, Some (_,j) ->
      if not (Int.equal i j) then
        CErrors.anomaly Pp.(str "check-hconstr-sharing mismatch: got " ++ int i ++
                            str " but should be " ++ int j)
    | SharingAnalyser.Fresh i, None ->
      assert (Int.equal i !cnt);
      seen := (c,i) :: !seen;
      incr cnt;
      Constr.iter aux c
    | _ -> assert false
  in
  let () = aux c in
  assert (SharingAnalyser.is_done !info);
  ()

let check_sharing, _ = CDebug.create_full ~name:"check-hconstr-sharing" ()

let hcons_before, _ = CDebug.create_full ~name:"hcons-before-hconstr" ()

let of_constr env c =
  let c = if CDebug.get_flag hcons_before then Constr.hcons c else c in
  let c_sharing_info = NewProfile.profile "sharingAnalyser" (fun () ->
      SharingAnalyser.analyse Constr.constr_descr (Obj.repr (c : Constr.t)))
      ()
  in
  let _debug = mk_debug c_sharing_info c in
  let local_env = empty_env env (Some c_sharing_info) in
  let local_env = iterate push_unknown_rel (Environ.nb_rel env) local_env in
  let tbl = Tbl.create 57 in
  let () =
    dbg_sharing Pp.(fun () ->
        let l = SharingAnalyser.to_list c_sharing_info in
        let (unshared,fresh,shared) = List.fold_left (fun (unshared,fresh,shared) -> function
            | SharingAnalyser.Unshared _ -> unshared+1, fresh, shared
            | SharingAnalyser.Fresh _ -> unshared, fresh+1, shared
            | SharingAnalyser.Seen _ -> unshared, fresh, shared+1)
            (0, 0, 0)
            l
        in
        str "raw length = " ++ int (SharingAnalyser.raw_length c_sharing_info) ++ pr_comma() ++
        str "unshared = " ++ int unshared ++ pr_comma() ++
        str "fresh = " ++ int fresh ++ pr_comma() ++
        str "shared = " ++ int shared
      )
  in
  let () = if CDebug.get_flag check_sharing then debug_check c c_sharing_info in
  steps := 0;
  let c = NewProfile.profile "HConstr.to_constr" (fun () -> of_constr tbl local_env c) () in
  dbg Pp.(fun () ->
      let stats = Tbl.stats tbl in
      let tree_size = tree_size (self c) in
      v 0 (
        str "steps = " ++ int !steps ++ spc() ++
        str "rel cnt = " ++ int !(local_env.cnt) ++ spc() ++
        str "unknwown rels = " ++ int !(local_env.unknown_cnt) ++ spc() ++
        str "hashes = " ++ int stats.Tbl.hashes ++ spc() ++
        str "bindings = " ++ int stats.Tbl.bindings ++ spc() ++
        str "tree size = " ++ int tree_size ++ spc() ++
        str "most_collisions = " ++ int stats.Tbl.most_collisions
    )
    );
  c

let kind x = x.kind

let hcons x =
  let tbl = Tbl.create 47 in
  let module HCons = GenHCons(struct
      type nonrec t = t
      let kind = kind
      let self = self
      let refcount = refcount
        let via_hconstr = true
      module Tbl = struct
        let find_opt x = Tbl.find_opt tbl x
        let add x y = Tbl.add tbl x y
      end
    end) in
  HCons.hcons x
