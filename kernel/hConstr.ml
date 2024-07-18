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

type local_env = {
  (* unique identifiers for each binder crossed *)
  rels : int Range.t;
  (* global counter *)
  cnt : int ref;
  assum_uids : int Tbl.t;
  (* the surrounding table is for the body, the inner table for the type *)
  letin_uids : int Tbl.t Tbl.t;
}

let empty_env () = {
  rels = Range.empty;
  cnt = ref 0;
  assum_uids = Tbl.create 47;
  letin_uids = Tbl.create 47;
}

let push_unknown_rel env =
  incr env.cnt;
  { env with rels = Range.cons !(env.cnt) env.rels }

let push_assum t env =
  let uid = match Tbl.find_opt env.assum_uids t with
  | Some uid -> uid
  | None ->
    incr env.cnt;
    let uid = !(env.cnt) in
    Tbl.add env.assum_uids t uid;
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
          uid
      end
    | None ->
      incr env.cnt;
      let uid = !(env.cnt) in
      let tbl = Tbl.create 3 in
      Tbl.add tbl typ uid;
      Tbl.add env.letin_uids body tbl;
      uid
  in
  { env with rels = Range.cons uid env.rels }

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
    let n, m, tl1, tl2 = if n < m then n, m, tl1, tl2 else m, n, tl2, tl1 in
    let tl = combine_unbound_rels tl1 (SList.defaultn (m-n) tl2) in
    SList.defaultn n tl

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

let compatible local_env v =
  let rec aux local_env rels = match rels with
    | SList.Nil -> true
    | SList.Cons (x,tl) ->
      Int.equal x (Range.hd local_env)
      && aux (Range.tl local_env) tl
    | SList.Default (n,tl) ->
      aux (Range.skipn n local_env) tl
  in
  aux local_env.rels v.unbound_rels

let quickfind (tbl,qtbl) local_env c =
  match kind c with
  | Var _ | Const _ | Ind _ | Construct _ as k ->
    let h = hash_kind k in
    begin match Tbl.raw_find tbl h (fun c' -> eq_leaf c c') with
    | Some v -> Inl v
    | None -> Inr None
    end
  | _ ->
    let qhash = Hashtbl.hash c in
    match Int.Map.find_opt qhash !qtbl with
    | None -> Inr (Some qhash)
    | Some l ->
      match List.find_map (fun (c',v) ->
          if c == c' && compatible local_env v
          then Some v else None) l
      with
      | Some v -> Inl v
      | None -> Inr (Some qhash)

let qadd qtbl qhash c0 c =
  qtbl := Int.Map.update qhash (function
      | None -> Some [c0,c]
      | Some l -> Some ((c0,c)::l))
      !qtbl

let rec of_constr tbl local_env c0 =
  match quickfind tbl local_env c0 with
  | Inl v -> v.refcount <- v.refcount + 1; v
  | Inr qhash ->
  let c =
    let kind = of_constr_aux tbl local_env c0 in
    let self = kind_to_constr kind in
    let self = if hasheq_kind (Constr.kind self) (Constr.kind c0) then c0 else self in
    let hash = hash_kind kind in
    let isRel, hash, unbound_rels = match kind with
      | Rel n ->
        let uid = Range.get local_env.rels (n-1) in
        assert (uid <> 0);
        uid, Hashset.Combine.combine uid hash, SList.defaultn (n-1) (SList.cons uid SList.empty)
      | _ -> 0, hash, kind_unbound_rels kind
    in
    { self; kind; hash; isRel; unbound_rels; refcount = 1 }
  in
  match Tbl.find_opt (fst tbl) c with
  | Some c' ->
    (* should we qadd here? seems likely to increase collisions massively *)
    c'.refcount <- c'.refcount + 1; c'
  | None -> Tbl.add (fst tbl) c c; Option.iter (fun qhash -> qadd (snd tbl) qhash c0 c) qhash; c

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
    let of_ctx (bnd, c) =
      let () = hcons_inplace hcons_annot bnd in
      let local_env = Array.fold_left (fun local_env _ -> push_unknown_rel local_env) local_env bnd in
      let c = of_constr tbl local_env c in
      bnd, c
    in
    let ci = hcons_caseinfo ci in
    let u = UVars.Instance.hcons u in
    let pms = Array.map (of_constr tbl local_env) pms in
    let p = of_ctx p in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert {indices} -> CaseInvert {indices=Array.map (of_constr tbl local_env) indices}
    in
    let c = of_constr tbl local_env c in
    let bl = Array.map of_ctx bl in
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

let dbg = CDebug.create ~name:"hconstr" ()

let tree_size c =
  let rec aux size c =
    Constr.fold aux (size+1) c
  in
  aux 0 c

let of_constr env c =
  let local_env = empty_env () in
  let local_env = iterate push_unknown_rel (Environ.nb_rel env) local_env in
  let tbl = Tbl.create 57 in
  let qtbl = ref Int.Map.empty in
  let c = of_constr (tbl,qtbl) local_env c in
  dbg Pp.(fun () ->
      let stats = Tbl.stats tbl in
      let tree_size = tree_size (self c) in
      v 0 (
        str "hashes = " ++ int stats.Tbl.hashes ++ spc() ++
        str "bindings = " ++ int stats.Tbl.bindings ++ spc() ++
        str "tree size = " ++ int tree_size ++ spc() ++
        str "most_collisions = " ++ int stats.Tbl.most_collisions
    )
    );
  c

let of_constr env c = NewProfile.profile "HConstr.of_constr" (fun () -> of_constr env c) ()

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
