open Hashset.Combine
open Util

(** Pretty-printing helper *)
let mkPr show = (fun a -> show a |> Pp.str)

(** Stage variables and stage annotations *)

module SVars =
struct
  include Int.Set

  type var = elt

  let union_list = List.fold_left union empty

  let show init vars =
    Int.Set.fold (fun i str -> string_of_int i ^ "," ^ str) vars init
  let pr init = mkPr (show init)
end

module Stage =
struct
  type t = Infty | StageVar of SVars.var * int

  let infty = -1 (* For constraint representation only!!! *)

  let mk var size = StageVar (var, size)

  let var_equal = Int.equal

  let compare s1 s2 =
    match s1, s2 with
    | Infty, Infty -> 0
    | Infty, _     -> 1
    | _, Infty     -> -1
    | StageVar (var1, sz1), StageVar (var2, sz2) ->
      let nc = Int.compare var1 var2 in
      if not (Int.equal nc 0) then nc
      else Int.compare sz1 sz2

  let show s =
    match s with
    | Infty -> "∞"
    | StageVar (s, n) ->
      let str = "s" ^ string_of_int s in
      if Int.equal n 0 then str else
      str ^ "+" ^ string_of_int n
end

module Annot =
struct
  open Stage

  type t =
    | Empty (* Bare types with no annotations, input to inference *)
    | Star (* Marks the positions of the (co)recursive types in (co)fixpoints *)
    | Glob (* Marks the positions of the (co)recursive types in global definitions *)
    | Stage (* Sized types *) of Stage.t

  let infty = Stage Infty

  let mk var size = Stage (Stage.mk var size)

  let hat a =
    match a with
    | Stage (StageVar (var, sz)) -> Stage (StageVar (var, succ sz))
    | _ -> a

  let is_stage a =
    match a with
    | Empty | Star -> false
    | _ -> true

  let compare a1 a2 =
    match a1, a2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1 | _, Empty -> 1
    | Star, Star   -> 0
    | Star, _  -> -1 | _, Star  -> 1
    | Glob, Glob   -> 0
    | Glob, _  -> -1 | _, Glob  -> 1
    | Stage s1, Stage s2 -> Stage.compare s1 s2

  let show a =
    match a with
    | Empty -> ""
    | Star  -> "*"
    | Glob  -> "ⁱ"
    | Stage s -> Stage.show s

  let pr = mkPr show

  let hash a =
    match a with
    | Empty -> combine 1 (show a |> String.hash)
    | Star  -> combine 2 (show a |> String.hash)
    | Glob  -> combine 3 (show a |> String.hash)
    | Stage Infty -> combine 4 (show a |> String.hash)
    | Stage (StageVar (n, i)) -> combine3 5 (Int.hash n) (Int.hash i)
end

(** Stage sets and state *)

module State =
struct
  open SVars
  open Stage
  open Annot

  (* state =
      ( name of next stage variable
      , all used stage variables
      , stage variables used to replace star annotations
      , old star variables
      ) *)
  type t = var * SVars.t * SVars.t * SVars.t

  let init = (0, empty, empty, empty)
  let push (next, vs, stars, _) = (next, vs, empty, stars)
  let pop (next, vs, stars, old) = (next, vs, SVars.union stars old, empty)
  let get_vars (_, vs, _, _) = vs
  let get_pos_vars (_, _, stars, _) = stars
  let remove_pos_vars rem (next, vs, stars, old) = (next, vs, diff stars rem, old)
  let next ?s:(s=Empty) ((next, vs, stars, old) as stg) =
    match s with
    | Empty | Stage Infty ->
      mk next 0, (succ next, add next vs, stars, old)
    | Star ->
      mk next 0, (succ next, add next vs, add next stars, old)
    | _ -> (s, stg)

  let show (stg, vars, stars, _) =
    let stg_str = string_of_int stg in
    let vars_str = "{" ^ SVars.show "∞" vars  ^ "}" in
    let stars_str = "{" ^ SVars.show ": *" stars ^ "}" in
    "<" ^ stg_str ^ "," ^ vars_str ^ "," ^ stars_str ^ ">"
  let pr = mkPr show
end

(** Stage constraints and sets of constraints *)

(** Constraints.t: A tuple of two maps mto and mfrom,
      where mto, mfrom are {var -> set of (var, weight)}
      Given a constraint v1+s1 ⊑ v2+s2, we update
      mto   {v1 -> Sv1 ∪ {(v2, s2 - s1)}} and
      mfrom {v2 -> Sv2 ∪ {(v1, s1 - s2)}}
      We keep both mto and mfrom for easy access to both
      a stage variable's substages and superstages
      N.B. Infty stages are stored as (-1)
    Generic functions: fold, filter
    Set-like functions: empty, union[_list], remove, contains, add
    Graph-like functions: sup, sub, vertices *)
module Constraints =
struct
  open Stage
  open Annot

  module Map = Int.Map
  module Set = Set.Make(struct
    type t = SVars.var * int
    let compare (v1, w1) (v2, w2) =
      let vc = Int.compare v1 v2 in
      if not (Int.equal vc 0) then vc
      else Int.compare w1 w2
  end)
  type t = Set.t Map.t * Set.t Map.t
  type 'a constrained = 'a * t

  let infty = Stage.infty

  let fold f (mto, _) =
    Map.fold (fun vfrom -> Set.fold (fun (vto, wt) -> f vfrom vto wt)) mto
  let filter f (mto, mfrom) =
    let f_rev vfrom vto wt = f vto vfrom (-wt) in
    let filter_from_set pred vfrom =
      Set.filter (fun (vto, wt) -> pred vfrom vto wt) in
    let filter_from_map pred =
      Map.mapi (filter_from_set pred) in
    filter_from_map f mto, filter_from_map f_rev mfrom

  let empty = Map.empty, Map.empty
  let union (mto1, mfrom1) (mto2, mfrom2) =
    let f _ so1 so2 =
      match so1, so2 with
      | Some s1, Some s2 -> Some (Set.union s1 s2)
      | Some _, _ -> so1
      | _, Some _ -> so2
      | _ -> None in
    Map.merge f mto1 mto2, Map.merge f mfrom1 mfrom2
  let union_list = List.fold_left union empty
  let remove var (mto, mfrom) =
    let remove_from_map var map =
      let has_base (v, _) = Stage.var_equal v var in
      Map.map (Set.filter has_base) (Map.remove var map) in
    remove_from_map var mto, remove_from_map var mfrom
  let contains (vfrom, vto) (mto, _) =
    match Map.find_opt vfrom mto with
    | None -> false
    | Some vtos ->
      Set.exists (fun (vto', _) -> Stage.var_equal vto vto') vtos

  let add a1 a2 ((mto, mfrom) as t) =
    let add_to_map vfrom vto wt =
      let f so =
        match so with
        | Some s -> Some (Set.add (vto, wt) s)
        | None -> Some (Set.singleton (vto, wt)) in
      Map.update vfrom f in
    let add_stages s1 s2 =
      match s1, s2 with
      | Infty, Infty -> t
      | StageVar (var1, sz1), StageVar (var2, sz2) ->
        if var_equal var1 var2 && sz1 <= sz2 then t
        else add_to_map var1 var2 (sz2 - sz1) mto, add_to_map var2 var1 (sz1 - sz2) mfrom
      | Infty, StageVar (var, _) ->
        add_to_map infty var 0 mto, add_to_map var infty 0 mfrom
      | StageVar _, Infty -> t in
    match a1, a2 with
    | Stage s1, Stage s2 -> add_stages s1 s2
    | _ -> t

  let add_infty =
    SVars.fold (fun var -> add Annot.infty (Annot.mk var 0))

  let add_to_set (var, _) vars =
    if Stage.var_equal var infty then vars
    else SVars.add var vars
  let get_set_from_map key map =
    match Map.find_opt key map with
    | Some set -> set
    | None -> Set.empty
  let sup s (mto, _) = Set.fold add_to_set (get_set_from_map s mto) SVars.empty
  let sub s (_, mfrom) = Set.fold add_to_set (get_set_from_map s mfrom) SVars.empty

  let vertices (mto, mfrom) =
    let get_keys m =
      (Map.fold (fun key _ set -> SVars.add key set) m SVars.empty) in
    SVars.union (get_keys mto) (get_keys mfrom)

  let show (mto, _mfrom : t) =
    let str_stage key value wt =
      let sfrom, sto =
        if wt >= 0
        then StageVar (key, 0), StageVar (value, wt)
        else StageVar (key, -wt), StageVar (value, 0) in
      let sfrom = if Stage.var_equal key   infty then Infty else sfrom in
      let sto   = if Stage.var_equal value infty then Infty else sto   in
      "(" ^ Stage.show sfrom ^ "⊑" ^ Stage.show sto ^ ")" in
    let str_set key set = Set.fold (fun (value, wt) str -> str_stage key value wt ^ str) set "" in
    let strs = Map.fold (fun key set str -> str_set key set ^ str) mto "" in
    "{" ^ strs ^ "}"
  let pr = mkPr show
end

(** RecCheck *)
open SVars

exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

let bellman_ford cstrnts src =
  let vertices = Constraints.vertices cstrnts in
  let distances = SVars.fold (fun var -> Int.Map.add var None) vertices Int.Map.empty in
  let distances = Int.Map.set src (Some 0) distances in
  let get_fromto vfrom vto distances =
    Int.Map.get vfrom distances,
    Int.Map.get vto   distances in
  let relax =
    Constraints.fold (fun vfrom vto wt distances ->
      match get_fromto vfrom vto distances with
      | Some ifrom, Some ito when ifrom + wt < ito ->
        Int.Map.set vto (Some (ifrom + wt)) distances
      | Some ifrom, None ->
        Int.Map.set vto (Some (ifrom + wt)) distances
      | _ -> distances)
    cstrnts in
  let rec relax_all i distances =
    if Int.equal i 1 then distances
    else
      let distances' = relax distances in
      if distances == distances' then distances
      else relax_all (i - 1) distances' in
  let distances = relax_all (Int.Set.cardinal vertices) distances in
  let check_neg vfrom vto wt =
    match get_fromto vfrom vto distances with
    | Some ifrom, Some ito -> ifrom + wt < ito
    | Some _, None -> true
    | _ -> false in
  let neg_edges = Constraints.filter check_neg cstrnts in
  Constraints.fold (fun vfrom _ _ -> add vfrom) neg_edges empty

let bellman_ford_all cstrnts =
  let vertices = Constraints.vertices cstrnts in
  fold (fun vertex -> union (bellman_ford cstrnts vertex)) vertices empty

let closure get_adj cstrnts init =
  let rec closure_rec init fin =
    match choose_opt init with
    | None -> fin
    | Some s ->
      let init_rest = remove s init in
      if mem s fin
      then closure_rec init_rest fin
      else
        let init_new = get_adj s cstrnts in
        closure_rec (union init_rest init_new) (add s fin) in
  filter (fun var -> var |> Stage.var_equal Stage.infty |> not) (closure_rec init empty)

let downward = closure Constraints.sub
let upward = closure Constraints.sup

let rec_check _alpha vstar vneq cstrnts =
  let f annot_sub var_sup cstrnts = Constraints.add annot_sub (Annot.mk var_sup 0) cstrnts in

  (* Step 1: Si = downward closure containing V* *)
  let si = downward cstrnts vstar in

  (* Step 2: Add α ⊑ Si *)
  let cstrnts1 = (* fold (f (Annot.mk alpha 0)) si *) cstrnts in

  (* Step 3: Remove negative cycles *)
  let v_neg = upward cstrnts1 (bellman_ford_all cstrnts1) in
  let cstrnts2 = fold Constraints.remove v_neg cstrnts1 in
  let cstrnts3 = fold (f Annot.infty) v_neg cstrnts2 in

  (* Step 4: Si⊑ = upward closure containing Si *)
  let si_up = upward cstrnts2 si in

  (* Step 5: S¬i = upward closure containing V≠ *)
  let si_neq = upward cstrnts2 vneq in

  (* Step 6: Add ∞ ⊑ S¬i ∩ Si⊑ *)
  let si_inter = inter si_neq si_up in
  let cstrnts4 = fold (f Annot.infty) si_inter cstrnts3 in

  (* Step 7: S∞ = upward closure containing {∞} *)
  let si_inf = upward cstrnts4 (singleton Stage.infty) in

  (* Step 8: Check S∞ ∩ Si = ∅ *)
  let si_null = inter si_inf si in
  if is_empty si_null then cstrnts4
  else raise (RecCheckFailed (cstrnts, si_inf, si))
