open Hashset.Combine
open Util

(** Pretty-printing helper *)
let mkPr show = (fun a -> show a |> Pp.str)

(** Stage variables and stage annotations *)

module Stage =
struct
  type var = int
  type t = Infty | StageVar of var * int

  let var_equal = Int.equal

  let compare s1 s2 =
    match s1, s2 with
    | Infty, Infty -> 0
    | Infty, _     -> 1
    | _, Infty     -> -1
    | StageVar (name1, size1), StageVar (name2, size2) ->
      let nc = Int.compare name1 name2 in
      if not (Int.equal nc 0) then nc
      else Int.compare size1 size2

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

  let hat a =
    match a with
    | Stage (StageVar (name, size)) -> Stage (StageVar (name, succ size))
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

  let init = (0, empty, empty)
  let get_vars (_, vs, _) = vs
  let get_pos_vars (_, _, stars) = stars
  let next ?s:(s=Empty) ((next, vs, stars) as stg) =
    match s with
    | Empty | Stage Infty ->
      Stage (StageVar (next, 0)),
      (succ next, add next vs, stars)
    | Star ->
      Stage (StageVar (next, 0)),
      (succ next, add next vs, add next stars)
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

  module Map = Map.Make(Stage)
  module Set = Set.Make(Stage)

  type t = Set.t Map.t * Set.t Map.t
  type 'a constrained = 'a * t

  let empty = Map.empty, Map.empty
  let union (mto1, mfrom1) (mto2, mfrom2) =
    let f _ so1 so2 = match so1, so2 with
      | Some s1, Some s2 -> Some (Set.union s1 s2)
      | Some _, _ -> so1
      | _, Some _ -> so2
      | _ -> None in
    Map.merge f mto1 mto2, Map.merge f mfrom1 mfrom2
  let union_list = List.fold_left union empty
  let add a1 a2 ((mto, mfrom) as t) =
    let add_to_map sfrom sto =
      let f so = match so with
        | Some s -> Some (Set.add sto s)
        | None -> Some (Set.singleton sto) in
      Map.update sfrom f in
    let add_stages s1 s2 = match s1, s2 with
      | Infty, Infty -> t
      | StageVar (name1, size1), StageVar (name2, size2)
        when var_equal name1 name2 && size1 <= size2 -> t
      | StageVar (name1, size1), StageVar (name2, size2) ->
        let diff = min size1 size2 in
        let s1_new, s2_new = StageVar (name1, size1 - diff), StageVar (name2, size2 - diff) in
        add_to_map s1_new s2_new mto, add_to_map s2_new s1_new mfrom
      | _ -> add_to_map s1 s2 mto, add_to_map s2 s1 mfrom in
    match a1, a2 with
    | Stage s1, Stage s2 -> add_stages s1 s2
    | _ -> t

  let tos s (mto, _) = Map.get s mto
  let froms s (_, mfrom) = Map.get s mfrom

  let show (mto, _) =
    let str_stage sfrom sto = "(" ^ Stage.show sfrom ^ "⊑" ^ Stage.show sto ^ ")" in
    let str_set key set = Set.fold (fun value str -> str_stage key value ^ str) set "" in
    let strs = Map.fold (fun key set str -> str_set key set ^ str) mto "" in
    "{" ^ strs ^ "}"
  let pr = mkPr show
end
