open Stages

type variance =
  | Variant
  | Bivariant

val add_constraint_from_ind : Environ.env -> variance ->
  Constraints.t -> Names.inductive -> Annot.t -> Annot.t -> Constraints.t

val add_constraint_from_ind_ref : Environ.env -> variance ->
  Constraints.t ref -> Names.inductive -> Annot.t -> Annot.t -> unit
