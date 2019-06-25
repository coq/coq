open Hashset.Combine
open Util

(** Pretty-printing helper *)
let mkPr show = (fun a -> show a |> Pp.str)

(** Stage variables and stage annotations *)

type stage_name = int
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

let succ_annot a =
  match a with
  | Stage (StageVar (name, size)) -> Stage (StageVar (name, succ size))
  | _ -> a

let is_stage a =
  match a with
  | Empty | Star -> false
  | _ -> true

let compare_stage s1 s2 =
    match s1, s2 with
    | Infty, Infty -> 0
    | Infty, _     -> 1
    | _, Infty     -> -1
    | StageVar (name1, size1), StageVar (name2, size2) ->
      let nc = Int.compare name1 name2 in
      if not (Int.equal nc 0) then nc
      else Int.compare size1 size2

let show_stage s =
  match s with
  | Infty -> "∞"
  | StageVar (s, n) ->
    let str = "s" ^ string_of_int s in
    if Int.equal n 0 then str else
    str ^ "+" ^ string_of_int n
let pr_stage = mkPr show_stage

let compare_annot a1 a2 =
  match a1, a2 with
  | Empty, Empty -> 0
  | Empty, _ -> -1 | _, Empty -> 1
  | Star, Star   -> 0
  | Star, _  -> -1 | _, Star  -> 1
  | Stage s1, Stage s2 -> compare_stage s1 s2

let leq_annot a1 a2 =
  match a1, a2 with
  | Empty, Empty -> true
  | Star,  Star  -> true
  | Stage (StageVar (name1, size1)), Stage (StageVar (name2, size2)) ->
    Int.equal name1 name2 && size1 <= size2
  | _, _ -> false

let show_annot a =
  match a with
  | Empty -> ""
  | Star  -> "*"
  | Stage s -> show_stage s
let pr_annot = mkPr show_annot

let hash_stage_annot a =
    match a with
    | Empty -> combine 1 (show_annot a |> String.hash)
    | Star  -> combine 2 (show_annot a |> String.hash)
    | Stage Infty -> combine 3 (show_annot a |> String.hash)
    | Stage (StageVar (n, i)) -> combine3 4 (Int.hash n) (Int.hash i)

(** Stage sets *)

type stage_vars = Int.Set.t
type stage_state  = stage_name * stage_vars

let init_stage_state = (0, Int.Set.empty)
let next_stage_state (next, vs) = (Stage (StageVar (next, 0)), (next + 1, Int.Set.add next vs))
let get_stage_vars (_, vs) = vs
let diff_stage_vars = Int.Set.diff

let show_stage_state (stg, vars) =
  let f i str = string_of_int i ^ "," ^ str in
  let vars_str = Int.Set.fold f vars "∞" in
  let stg_str = string_of_int stg in
  "<" ^ stg_str ^ "," ^ "{" ^ vars_str ^ "}" ^ ">"
let pr_stage_state = mkPr show_stage_state

(** Stage constraints and sets of constraints
   N.B. For a constraint to be "larger" than another has no inherent meaning;
        the ordering is just for using Set. *)

module SConstraintOrd =
struct
  type t = stage * stage
  (* (s, r) means s ⊑ r *)

  let compare (s1, s2) (r1, r2) =
    let sc = compare_stage s1 r1 in
    if not (Int.equal sc 0) then sc
    else compare_stage s2 r2
end

module SConstraint =
struct
  module S = Set.Make(SConstraintOrd)
  include S
end

type stage_constraint = SConstraint.elt
type constraints = SConstraint.t
type 'a constrained = 'a * constraints

let empty_constraint = SConstraint.empty
let union_constraint = SConstraint.union
let union_constraints = List.fold_left union_constraint empty_constraint

let add_constraint s1 s2 csts =
  match s1, s2 with
  | Infty, Infty -> csts
  | StageVar (name1, size1), StageVar (name2, size2)
    when Int.equal name1 name2 && size1 <= size2 -> csts
  | StageVar (name1, size1), StageVar (name2, size2) ->
    let diff = min size1 size2 in
    let new_cst = (StageVar (name1, size1 - diff), StageVar (name2, size2 - diff)) in
    SConstraint.add new_cst csts
  | _ -> SConstraint.add (s1, s2) csts

let add_constraint_ref_option a1 a2 cstrnts =
  match a1, a2, cstrnts with
    | Stage s1, Stage s2, Some cstrnts_ref -> cstrnts_ref := add_constraint s1 s2 !cstrnts_ref
    | _ -> ()

let show_constraints cstrnts =
  let f (s1, s2) str = "(" ^ show_stage s1 ^ "⊑" ^ show_stage s2 ^ ")" ^ str in
  let str = SConstraint.fold f cstrnts "" in
  "{" ^ str ^ "}"
let pr_constraints = mkPr show_constraints
