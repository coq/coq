open Hashset.Combine
open Util

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
  | Empty -> "Empty"
  | Star  -> "Star"
  | Stage Infty -> "Infty"
  | Stage (StageVar (n, i)) -> "Stage s" ^ string_of_int n ^ " + " ^ string_of_int i

let pr a = Pp.str (show_annot a)

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
