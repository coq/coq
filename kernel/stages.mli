(* open Constr *)

type stage_name
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

type stage_vars
type stage_state
val init_stage_var : stage_state
val next_stage_var : stage_state -> stage_name * stage_state
val get_stage_vars : stage_state -> stage_vars
val diff_stage_vars : stage_vars -> stage_vars -> stage_vars


module Constraint : sig
  include Set.S
end

type stage_constraint = Constraint.elt
type constraints = Constraint.t
val empty_constraint : Constraint.t
val union_constraint : Constraint.t -> Constraint.t -> Constraint.t
val add_constraint : Constraint.elt -> Constraint.t -> Constraint.t


type ('constr, 'types, 'sort, 'univs) kind_of_term_sized
type t
type constr_sized = t
type types_sized = constr_sized

(* val erase : constr_sized -> constr *)
