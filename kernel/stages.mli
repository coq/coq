type stage_name
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

val compare_stage : stage -> stage -> int
val compare_annot : annot -> annot -> int
val show_annot : annot -> string
val pr : annot -> Pp.t
val hash_stage_annot : annot -> int


type stage_vars
type stage_state
val init_stage_state : stage_state
val next_stage_state : stage_state -> annot * stage_state
val get_stage_vars : stage_state -> stage_vars
val diff_stage_vars : stage_vars -> stage_vars -> stage_vars


module SConstraint : sig
  include Set.S
end

type stage_constraint = SConstraint.elt
type constraints = SConstraint.t
val empty_constraint : SConstraint.t
val union_constraint : SConstraint.t -> SConstraint.t -> SConstraint.t
val union_constraints : SConstraint.t list -> SConstraint.t
val add_constraint : SConstraint.elt -> SConstraint.t -> SConstraint.t
