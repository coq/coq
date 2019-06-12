open Names
open Context
open Univ
open Constr

(** Stage variables, stage annotations, and stage sets *)
type stage_name = int
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

type stage_vars = Int.Set.t
type stage_state  = stage_name * stage_vars

let init_stage_var = (0, Int.Set.empty)
let next_stage_var (next, vs) = (next, (next + 1, Int.Set.add next vs))
let get_stage_vars (_, vs) = vs
let diff_stage_vars = Int.Set.diff

(** Stage constraints and sets of constraints
   N.B. For a constraint to be "larger" than another has no inherent meaning;
        the ordering is just for using Set. *)

module SConstraintOrd =
struct
  type t = stage * stage
  (* (s, r) means s ⊑ r *)

  let compare_stage s1 s2 =
    match (s1, s2) with
    | (Infty, Infty) -> 0
    | (Infty, _)     -> 1
    | (_, Infty)     -> -1
    | (StageVar (name1, size1), StageVar (name2, size2)) ->
      let nc = Int.compare name1 name2 in
      if not (Int.equal nc 0) then nc
      else Int.compare size1 size2

  let compare (s1, s2) (r1, r2) =
    let sc = compare_stage s1 r1 in
    if not (Int.equal sc 0) then sc
    else compare_stage s2 r2
end

module Constraint =
struct
  module S = Set.Make(SConstraintOrd)
  include S
end

type stage_constraint = Constraint.elt
type constraints = Constraint.t

let empty_constraint = Constraint.empty
let union_constraint = Constraint.union
let add_constraint cst csts =
  match cst with
  | (Infty, Infty) -> csts
  | (StageVar (name1, size1), StageVar (name2, size2)) when Int.equal name1 name2 ->
    let diff = min size1 size2 in
    let new_cst = (StageVar (name1, size1 - diff), StageVar (name2, size2 - diff)) in
    Constraint.add new_cst csts
  | _ -> Constraint.add cst csts

(** Sized terms and types *)

type metavariable = int
type ('constr, 'types, 'sort, 'univs) kind_of_term_sized =
  | SRel       of int
  | SVar       of Id.t
  | SMeta      of metavariable
  | SEvar      of 'constr pexistential
  | SSort      of 'sort
  | SCast      of 'constr * cast_kind * 'types
  | SProd      of Name.t binder_annot * 'types * 'types
  | SLambda    of Name.t binder_annot * 'types * 'constr
  | SLetIn     of Name.t binder_annot * 'constr * 'types * 'constr
  | SApp       of 'constr * 'constr array
  | SConst     of (Constant.t * 'univs)
  | SInd       of (inductive * 'univs) * annot
  | SConstruct of (constructor * 'univs)
  | SCase      of case_info * 'constr * 'constr * 'constr array
  | SFix       of ('constr, 'types) pfixpoint
  | SCoFix     of ('constr, 'types) pcofixpoint
  | SProj      of Projection.t * 'constr
  | SInt       of Uint63.t
type t = (t, t, Sorts.t, Instance.t) kind_of_term_sized
type constr_sized = t
type types_sized = constr_sized

let rec erase cstr =
    match cstr with
    | SRel n                    -> Rel n
    | SVar id                   -> Var id
    | SMeta n                   -> Meta n
    | SEvar (e, l)              -> Evar (e, Array.map erase l)
    | SSort s                   -> Sort s
    | SCast (c, k, t)           -> Cast (erase c, k, erase t)
    | SProd (na, t, c)          -> Prod (na, erase t, erase c)
    | SLambda (na, t, c)        -> Lambda (na, erase t, erase c)
    | SLetIn (na, b, t, c)      -> LetIn (na, erase b, erase t, erase c)
    | SApp (f, l)               -> App (erase f, Array.map erase l)
    | SConst cu                 -> Const cu
    | SInd (iu, _)              -> Ind iu
    | SConstruct cu             -> Construct cu
    | SCase (ci, p, c, lf)      -> Case (ci, erase p, erase c, Array.map erase lf)
    | SFix (vni, (lna, lc, lt)) -> Fix (vni, (lna, Array.map erase lc, Array.map erase lt))
    | SCoFix (i, (lna, lc, lt)) -> CoFix (i, (lna, Array.map erase lc, Array.map erase lt))
    | SProj (p, c)              -> Proj (p, erase c)
    | SInt i                    -> Int i
