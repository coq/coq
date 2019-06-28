val add_constraint_from_ind : Environ.env -> Stages.constraints ->
    Names.inductive -> Stages.annot -> Stages.annot -> Stages.constraints

val add_constraint_from_ind_ref : Environ.env -> Stages.constraints ref ->
    Names.inductive -> Stages.annot -> Stages.annot -> unit
