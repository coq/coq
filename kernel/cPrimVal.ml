(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type ('constr, 'types, 'univs) t =
  | Int of Uint63.t
  | Float of Float64.t
  | Array of 'univs * 'constr array * 'constr * 'types

let fold fc ft acc v =
  match v with
  | Float _ | Int _ -> acc
  | Array (_,elems,def,ty) -> ft (fc (Array.fold_left fc acc elems) def) ty

let iter fc ft v =
  match v with
  | Float _ | Int _ -> ()
  | Array (_,elems,def,ty) -> Array.iter fc elems; fc def; ft ty

let map fc ft fu v =
  match v with
  | Float _ | Int _ -> v
  | Array (u,elems,def,ty) ->
      let u' = fu u in
      let elems' = CArray.Smart.map fc elems in
      let def' = fc def in
      let ty' = ft ty in
      if u == u' && elems == elems' && def == def' && ty == ty' then v
      else Array (u',elems',def',ty')

let map_heterogenous fc ft fu v =
  match v with
  | Float f -> Float f
  | Int i -> Int i
  | Array (u,elems,def,ty) -> Array (fu u, Array.map fc elems, fc def, ft ty)

let fold_map f accu v =
  match v with
  | Float _ | Int _ -> accu, v
  | Array (u,elems,def,ty) ->
      let accu, elems' = Util.Array.Smart.fold_left_map f accu elems in
      let accu, def' = f accu def in
      let accu, ty' = f accu ty in
      if elems == elems' && def == def' && ty == ty' then accu, v
      else accu, Array (u, elems', def', ty')

let map_fun1 f l v =
  match v with
  | Float _ | Int _ -> v
  | Array (u,elems,def,ty) ->
      let elems' = Util.Array.Fun1.Smart.map f l elems in
      let def' = f l def in
      let ty' = f l ty in
      if elems == elems' && def == def' && ty == ty' then v
      else Array (u, elems', def', ty')

let equal eq_univ eq v1 v2 =
  match v1, v2 with
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | Array (u1,elems1,def1,ty1), Array (u2,elems2,def2,ty2) ->
      eq_univ u1 u2 &&
      Util.Array.equal_norefl eq elems1 elems2 &&
      eq def1 def2 &&
      eq ty1 ty2
  | (Int _ | Float _ | Array _), _ -> false

let compare f v1 v2 =
  let (=?) f g i1 i2 j1 j2=
    let c = f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c in
  let (==?) fg h i1 i2 j1 j2 k1 k2=
    let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c in
  match v1, v2 with
  | Int i1, Int i2 -> Uint63.compare i1 i2
  | Int _, _ -> -1 | _, Int _ -> 1
  | Float f1, Float f2 -> Float64.total_compare f1 f2
  (*| Float _, _ -> -1 | _, Float _ -> 1*)
  | Array (_,elems1,def1,ty1), Array (_,elems2,def2,ty2) ->
      Util.(((Array.compare f) =? f) ==? f) elems1 elems2 def1 def2 ty1 ty2
  | Array _, _ -> -1 | _, Array _ -> 1

let hash fu fa fc v =
  let open Hashset.Combine in
  match v with
  | Int i -> combinesmall 1 (Uint63.hash i)
  | Float f -> combinesmall 2 (Float64.hash f)
  | Array (u,elems,def,ty) ->
      combinesmall 3 (combine4 (fu u) (fa elems) (fc def) (fc ty))

let hash_term fu fa fc v =
  let open Hashset.Combine in
  match v with
  | Int i ->
      let (h,l) = Uint63.to_int2 i in
      (v, combinesmall 1 (combine h l))
  | Float f ->
      (v, combinesmall 2 (Float64.hash f))
  | Array (u,elems,def,ty) ->
      let u, hu = fu u in
      let elems, helems = fa elems in
      let def, hdef = fc def in
      let ty, hty = fc ty in
      (Array (u,elems,def,ty), combinesmall 3 (combine4 hu helems hdef hty))

let exists_constr p v =
  match v with
  | Array (_,elems,def,_) -> Array.exists p elems || p def
  | Int _ | Float _ -> false

let fold_univs f acc v =
  match v with
  | Array (u,_,_,_) -> f acc u
  | Int _ | Float _ -> acc

let matching ~fail f vpat v acc =
  match vpat, v with
  | Int i1, Int i2 when Uint63.equal i1 i2 -> acc
  | Float f1, Float f2 when Float64.equal f1 f2 -> acc
  | Array (_,elems1,def1,ty1), Array (_,elems2,def2,ty2)
    when Array.length elems1 = Array.length elems2 ->
      let acc = ref acc in
      Array.iter2 (fun e1 e2 -> acc := f !acc e1 e2) elems1 elems2;
      f (f !acc def1 def2) ty1 ty2
  | _, _ -> fail ()

let debug_print pu pc v =
  match v with
  | Int i -> Pp.(str "Int(" ++ str (Uint63.to_string i) ++ str ")")
  | Float i -> Pp.(str "Float(" ++ str (Float64.to_string i) ++ str ")")
  | Array (u,elems,def,ty) ->
      let open Pp in
      str "Array(" ++
      prlist_with_sep pr_comma pc (Array.to_list elems) ++
      str " | " ++
      pc def ++
      str " : " ++
      pc ty ++
      str ")@{" ++
      pu u ++
      str "}"
