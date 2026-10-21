(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type t = {
  subst: Universe.t option Level.Map.t;
}

let empty = {
  subst = Level.Map.empty;
}

let is_empty {subst} = Level.Map.is_empty subst

let domain {subst} = Level.Map.domain subst

let mem l {subst} = Level.Map.mem l subst

let is_defined l {subst} = Option.has_some (Level.Map.find l subst)

let fold f {subst} acc =
  Level.Map.fold (fun l v acc -> f l ~is_defined:(Option.has_some v) acc)
    subst acc

let fix_undefined_variables us =
  Level.Map.fold (fun u v ({subst} as acc) ->
      match v with
      | None -> { subst = Level.Map.remove u subst }
      | Some _ -> acc)
    us.subst us

let add l {subst} =
  let subst = Level.Map.update l
      (function
        | None -> Some None
        | Some _ -> assert false)
      subst
  in
  { subst }

let remove l { subst } =
  let subst = match Level.Map.find_opt l subst with
    | None -> subst
    | Some None -> Level.Map.remove l subst
    | Some (Some _) ->
      (* removing [l := v] is unsound as it loses a constraint *)
      assert false
  in
  { subst = subst }

let add_levels levels subst =
  Level.Set.fold (fun l subst -> add l subst) levels subst

let define l v {subst} =
  let subst =
    try Level.Map.modify l (fun _ old -> assert (Option.is_empty old); Some v) subst
    with Not_found -> assert false
  in
  { subst }

let constrain_variables diff us ctx =
  (* XXX update algs? *)
  Level.Set.fold (fun l ((univs,cstrs),{subst } as acc) ->
      match Level.Map.find_opt l subst with
      | None | Some None -> acc
      | Some (Some u) -> match Universe.level u with
        | None -> acc
        | Some ul ->
          ((Level.Set.add l univs, Univ.UnivConstraints.add (Univ.Universe.make l, UnivConstraint.Eq, u) cstrs),
           {subst = Level.Map.remove l subst}))
    diff
    (ctx,us)

let biased_union {subst=lsubst} {subst=rsubst} =
  let subst =
    Level.Map.union (fun _k l r ->
        match l, r with
        | Some _, _ -> Some l
        | None, None -> Some l
        | _, _ -> Some r) lsubst rsubst
  in
  { subst }

let normalize_univ_variable ~find =
  let rec aux cur =
    find cur |>
    Option.map (fun b ->
        let b' = UnivSubst.subst_univs_universe aux b in
        if Universe.equal b' b then b
        else b')
  in aux

let normalize_univ_variable ectx =
  let find l = Option.flatten (Univ.Level.Map.find_opt l ectx.subst) in
  normalize_univ_variable ~find

let normalize_universe subst =
  let normlevel = normalize_univ_variable subst in
  UnivSubst.subst_univs_universe normlevel

let normalize ctx =
  let normalize = normalize_universe ctx in
  let subst =
    Univ.Level.Map.mapi (fun u -> function
        | None -> None
        | Some v -> Some (normalize v)) ctx.subst
  in
  {subst}

let normalize_univ_variables ctx =
  let ctx = normalize ctx in
  let def, subst =
    Univ.Level.Map.fold (fun u v (def, subst) ->
        match v with
        | None -> (def, subst)
        | Some b -> (Univ.Level.Set.add u def, Univ.Level.Map.add u b subst))
      ctx.subst (Univ.Level.Set.empty, Univ.Level.Map.empty)
  in
  let subst l = Level.Map.find_opt l subst in
  ctx, def, subst

let normalize_constraints subst cstrs =
  let norm_univ = normalize_universe subst in
  let normalize_constraint (l, d, r) = (norm_univ l, d, norm_univ r) in
  UnivConstraints.fold (fun cstr acc -> UnivConstraints.add (normalize_constraint cstr) acc)
    cstrs UnivConstraints.empty

let pr prl {subst} =
  let open Pp in
  let ppsubst = Level.Map.pr prl (function
      | None -> mt()
      | Some x -> str " := " ++ Universe.pr prl x)
      subst
  in
  str"FLEXIBLE UNIVERSES:"++brk(0,1)++
  h ppsubst
