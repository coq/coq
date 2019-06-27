type stage_name
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

val succ_annot : annot -> annot
val is_stage : annot -> bool
val compare_annot : annot -> annot -> int
val show_annot : annot -> string
val pr_annot : annot -> Pp.t
val hash_stage_annot : annot -> int


type stage_vars
type stage_state
val init_stage_state : stage_state
val next_stage_state : stage_state -> annot * stage_state
val get_stage_vars : stage_state -> stage_vars
val diff_stage_vars : stage_vars -> stage_vars -> stage_vars
val pr_stage_state : stage_state -> Pp.t


module SConstraint : sig
  include Set.S
end

type stage_constraint = SConstraint.elt
type constraints = SConstraint.t
type 'a constrained = 'a * constraints
val empty_constraint : constraints
val union_constraint : constraints -> constraints -> constraints
val union_constraints : constraints list -> constraints
val add_constraint : annot -> annot -> constraints -> constraints
val pr_constraints : constraints -> Pp.t
