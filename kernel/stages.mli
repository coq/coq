type stage_name
type stage = Infty | StageVar of stage_name * int
type annot = Empty | Star | Stage of stage

val succ_annot : annot -> annot
val is_stage : annot -> bool
val compare_stage : stage -> stage -> int
val compare_annot : annot -> annot -> int
val leq_annot : annot -> annot -> bool
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
type 'a constrained = 'a * constraints
val empty_constraint : SConstraint.t
val union_constraint : SConstraint.t -> SConstraint.t -> SConstraint.t
val union_constraints : SConstraint.t list -> SConstraint.t
val add_constraint : stage -> stage -> SConstraint.t -> SConstraint.t
val add_constraint_ref_option : annot -> annot -> (SConstraint.t ref) option -> unit
