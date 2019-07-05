open Stages

val add_constraint_from_ind : Environ.env -> Constraints.t ->
    Names.inductive -> Annot.t -> Annot.t -> Constraints.t

val add_constraint_from_ind_ref : Environ.env -> Constraints.t ref ->
    Names.inductive -> Annot.t -> Annot.t -> unit
