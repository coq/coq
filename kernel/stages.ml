open Hashset.Combine
open Util

(** Pretty-printing helper *)
let mkPr show = (fun a -> show a |> Pp.str)

(** Stage variables and stage annotations *)

module Stage =
struct
  type var = int
  type t = Infty | StageVar of var * int

  let infty = -1 (* For constraint representation only!!! *)

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

  type t = Empty | Star | Stage of Stage.t

  let infty = Stage Infty

  let mk var = Stage (StageVar (var, 0))

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
    | Stage s1, Stage s2 -> Stage.compare s1 s2

  let show a =
    match a with
    | Empty -> ""
    | Star  -> "*"
    | Stage s -> Stage.show s

  let pr = mkPr show

  let hash a =
    match a with
    | Empty -> combine 1 (show a |> String.hash)
    | Star  -> combine 2 (show a |> String.hash)
    | Stage Infty -> combine 3 (show a |> String.hash)
    | Stage (StageVar (n, i)) -> combine3 4 (Int.hash n) (Int.hash i)
end

(** Stage sets and state *)

module State =
struct
  open Stage
  open Annot
  open Int.Set

  (* state =
      ( name of next stage variable
      , all used stage variables
      , stage variables used to replace star annotations
      ) *)
  type vars = Int.Set.t
  type t = var * vars * vars

  let mem = mem
  let vars_empty = empty
  let vars_add = add

  let init = (0, empty, empty)
  let get_vars (_, vs, _) = vs
  let get_pos_vars (_, _, stars) = stars
  let next ?s:(s=Empty) ((next, vs, stars) as stg) =
    match s with
    | Empty | Stage Infty ->
      mk next, (succ next, add next vs, stars)
    | Star ->
      mk next, (succ next, add next vs, add next stars)
    | _ -> (s, stg)

  let show (stg, vars, stars) =
    let f i str = string_of_int i ^ "," ^ str in
    let stg_str = string_of_int stg in
    let vars_str = "{" ^ Int.Set.fold f vars "∞" ^ "}" in
    let stars_str = "{" ^ Int.Set.fold f stars ": *" ^ "}" in
    "<" ^ stg_str ^ "," ^ vars_str ^ "," ^ stars_str ^ ">"
  let pr = mkPr show
end

(** Stage constraints and sets of constraints *)

module Constraints =
struct
  open Stage
  open Annot

  module Map = Int.Map
  module Set = Set.Make(struct
    type t = var * int
    let compare (v1, w1) (v2, w2) =
      let vc = Int.compare v1 v2 in
      if not (Int.equal vc 0) then vc
      else Int.compare w1 w2
  end)

  type t = Set.t Map.t * Set.t Map.t
  type 'a constrained = 'a * t

  let infty = Stage.infty

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

  (* Given a stage constraint n1+s1 ⊑ n2+s2, we add mappings
    n1 -> (n2, (s2 - s1)) to [mto] and n2 -> (n1, (s1 - s2)) to [mfrom]
    with (-1) representing [Infty]
    Essentially a graph in adjacency list form without
    the usual graph functions unless needed *)
  let add a1 a2 ((mto, mfrom) as t) =
    let add_to_map nfrom nto wt =
      let f so =
        match so with
        | Some s -> Some (Set.add (nto, wt) s)
        | None -> Some (Set.singleton (nto, wt)) in
      Map.update nfrom f in
    let add_stages s1 s2 =
      match s1, s2 with
      | Infty, Infty -> t
      | StageVar (var1, sz1), StageVar (var2, sz2)
        when var_equal var1 var2 && sz1 <= sz2 -> t
      | StageVar (var1, sz1), StageVar (var2, sz2) ->
        add_to_map var1 var2 (sz2 - sz1) mto, add_to_map var2 var1 (sz1 - sz2) mfrom
      | Infty, StageVar (var, _) ->
        add_to_map infty var 0 mto, add_to_map var infty 0 mfrom
      | StageVar _, Infty -> t in
    match a1, a2 with
    | Stage s1, Stage s2 -> add_stages s1 s2
    | _ -> t

  let add_to_set (var, _) vars =
    if Stage.var_equal var infty then vars
    else State.vars_add var vars
  let sup s (mto, _) = Set.fold add_to_set (Map.get s mto) State.vars_empty
  let sub s (_, mfrom) = Set.fold add_to_set (Map.get s mfrom) State.vars_empty

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
open Int.Set

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
  filter (Stage.var_equal Stage.infty) (closure_rec init empty)

let downward = closure Constraints.sub
let upward = closure Constraints.sup

let rec_check alpha vstar vneq cstrnts =
  let f annot_sub var_sup cstrnts = Constraints.add annot_sub (Annot.mk var_sup) cstrnts in

  (* Step 1: Si = downward closure containing V* *)
  let si = downward cstrnts vstar in

  (* Step 2: Add α ⊑ Si *)
  let cstrnts1 = fold (f (Annot.mk alpha)) si cstrnts in

  (* Step 3: Remove negative cycles *)
  let v_neg = empty in (* TODO: Find variables in negative cycles *)
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
  if is_empty si_null then cstrnts4 else
  cstrnts4 (* TODO: Throw error *)
