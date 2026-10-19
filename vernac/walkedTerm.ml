(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Types of constants without a body, by what the traversal of {!Assumptions}
    reads of them: two terms are one key when it reads the same references in
    the same structure, which is what [eq_walked] compares, arm by arm as
    [Assumptions.fold_with_full_binders] reads a term. No application is
    flattened and no cast is looked through (the traversal reads the type of a
    cast, also at the head of an application, and a flattened comparison would
    not). A [Const], [Ind] or [Construct] is the same only when both its user
    name and its canonical name agree ([Constr.equal] compares the canonical
    name alone, and would merge two user names of one object, which the
    traversal's [data] tells apart). Only what the traversal never reads is
    ignored: binder names, universe instances, sorts, the kind of a cast, the
    strategy and relevance annotations and the binder contexts of a match, the
    name of a projection, the recursion indices of a fixpoint.

    A [Var] is a reference the traversal collects, so it is compared by name.
    [Rel] and [Meta] are compared by value, which is stricter than the
    traversal needs (it reads neither): comparing more strictly than the
    traversal reads can only make two types two keys, which costs reuse and
    never output.

    [hash_walked] reads the same fields and no others, so equal keys hash
    equally. *)
let rec eq_walked a b =
  a == b ||
  (match Constr.kind a, Constr.kind b with
   | Constr.Rel i, Constr.Rel j -> Int.equal i j
   | Constr.Meta i, Constr.Meta j -> Int.equal i j
   | Constr.Var x, Constr.Var y -> Id.equal x y
   | Constr.Sort _, Constr.Sort _ -> true
   | Constr.Int i, Constr.Int j -> Uint63.equal i j
   | Constr.Float x, Constr.Float y -> Float64.equal x y
   | Constr.String x, Constr.String y -> Pstring.equal x y
   | Constr.Const (c1, _), Constr.Const (c2, _) ->
     Constant.UserOrd.equal c1 c2 && Constant.CanOrd.equal c1 c2
   | Constr.Ind (i1, _), Constr.Ind (i2, _) ->
     Ind.UserOrd.equal i1 i2 && Ind.CanOrd.equal i1 i2
   | Constr.Construct (k1, _), Constr.Construct (k2, _) ->
     Construct.UserOrd.equal k1 k2 && Construct.CanOrd.equal k1 k2
   | Constr.Cast (c1, _, t1), Constr.Cast (c2, _, t2) -> eq_walked c1 c2 && eq_walked t1 t2
   | Constr.Prod (_, t1, c1), Constr.Prod (_, t2, c2)
   | Constr.Lambda (_, t1, c1), Constr.Lambda (_, t2, c2) -> eq_walked t1 t2 && eq_walked c1 c2
   | Constr.LetIn (_, b1, t1, c1), Constr.LetIn (_, b2, t2, c2) ->
     eq_walked b1 b2 && eq_walked t1 t2 && eq_walked c1 c2
   | Constr.App (c1, l1), Constr.App (c2, l2) -> eq_walked c1 c2 && eq_walked_array l1 l2
   | Constr.Proj (_, _, c1), Constr.Proj (_, _, c2) -> eq_walked c1 c2
   | Constr.Case (ci1, _, pms1, ((_, p1), _), iv1, c1, bl1),
     Constr.Case (ci2, _, pms2, ((_, p2), _), iv2, c2, bl2) ->
     (* The traversal expands a match through the declaration of its
        inductive, which is the same for the same inductive, the same
        parameters and the same (names aside) return clause and branches. The
        universe instance only changes the instances inside that expansion,
        never a name, so it is ignored. *)
     Ind.UserOrd.equal ci1.Constr.ci_ind ci2.Constr.ci_ind
     && Ind.CanOrd.equal ci1.Constr.ci_ind ci2.Constr.ci_ind
     && eq_walked_array pms1 pms2 && eq_walked p1 p2
     && (match iv1, iv2 with
         | Constr.NoInvert, Constr.NoInvert -> true
         | Constr.CaseInvert { indices = i1 }, Constr.CaseInvert { indices = i2 } ->
           eq_walked_array i1 i2
         | (Constr.NoInvert | Constr.CaseInvert _), _ -> false)
     && eq_walked c1 c2
     && Int.equal (Array.length bl1) (Array.length bl2)
     && (let rec loop i = i >= Array.length bl1
                          || (eq_walked (snd bl1.(i)) (snd bl2.(i)) && loop (i + 1)) in
         loop 0)
   | Constr.Fix (_, (_, tl1, bl1)), Constr.Fix (_, (_, tl2, bl2))
   | Constr.CoFix (_, (_, tl1, bl1)), Constr.CoFix (_, (_, tl2, bl2)) ->
     eq_walked_array tl1 tl2 && eq_walked_array bl1 bl2
   | Constr.Array (_, t1, d1, ty1), Constr.Array (_, t2, d2, ty2) ->
     eq_walked_array t1 t2 && eq_walked d1 d2 && eq_walked ty1 ty2
   | _ -> false)

and eq_walked_array a b =
  Int.equal (Array.length a) (Array.length b)
  && (let rec loop i = i >= Array.length a || (eq_walked a.(i) b.(i) && loop (i + 1)) in
      loop 0)

let hash_walked t =
  let mix h x = (h * 65599 + x) land max_int in
  let rec go h t =
    match Constr.kind t with
    | Constr.Rel i -> mix (mix h 1) i
    | Constr.Meta i -> mix (mix h 2) i
    | Constr.Var x -> mix (mix h 3) (Id.hash x)
    | Constr.Sort _ -> mix h 4
    | Constr.Int i -> mix (mix h 5) (Uint63.hash i)
    | Constr.Float x -> mix (mix h 6) (Float64.hash x)
    | Constr.String x -> mix (mix h 7) (Pstring.hash x)
    | Constr.Const (c, _) -> mix (mix (mix h 8) (Constant.UserOrd.hash c)) (Constant.CanOrd.hash c)
    | Constr.Ind (i, _) -> mix (mix (mix h 9) (Ind.UserOrd.hash i)) (Ind.CanOrd.hash i)
    | Constr.Construct (k, _) -> mix (mix (mix h 10) (Construct.UserOrd.hash k)) (Construct.CanOrd.hash k)
    | Constr.Cast (c, _, ty) -> go (go (mix h 11) c) ty
    | Constr.Prod (_, ty, c) -> go (go (mix h 12) ty) c
    | Constr.Lambda (_, ty, c) -> go (go (mix h 13) ty) c
    | Constr.LetIn (_, b, ty, c) -> go (go (go (mix h 14) b) ty) c
    | Constr.App (c, l) -> go_array (go (mix h 15) c) l
    | Constr.Proj (_, _, c) -> go (mix h 16) c
    | Constr.Case (ci, _, pms, ((_, p), _), iv, c, bl) ->
      let h = mix (mix (mix h 17) (Ind.UserOrd.hash ci.Constr.ci_ind)) (Ind.CanOrd.hash ci.Constr.ci_ind) in
      let h = go (go_array h pms) p in
      let h = match iv with Constr.NoInvert -> h | Constr.CaseInvert { indices } -> go_array (mix h 18) indices in
      let h = go h c in
      Array.fold_left (fun h (_, b) -> go h b) h bl
    | Constr.Fix (_, (_, tl, bl)) -> go_array (go_array (mix h 19) tl) bl
    | Constr.CoFix (_, (_, tl, bl)) -> go_array (go_array (mix h 20) tl) bl
    | Constr.Array (_, tl, d, ty) -> go (go (go_array (mix h 21) tl) d) ty
    | Constr.Evar _ -> mix h 22
  and go_array h a = Array.fold_left go h a in
  go 0 t

module Tbl = Hashtbl.Make (struct
    type t = Constr.t
    let equal = eq_walked
    let hash = hash_walked
  end)
